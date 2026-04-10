const EPSILON = 'ε';
let stateCounter = 0, snapshots = [], currentStep = 0;
let canvasScale = 1, panX = 0, panY = 0, isPanning = false, lastPan = null;
let nodePositions = [], renderEdges = [];
const canvas = document.getElementById('main-canvas');
const ctx = canvas.getContext('2d');
const R = 30;

// ==================== PARSER ====================
function parseRegex(input) {
  let pos = 0;
  const peek = () => pos < input.length ? input[pos] : null;
  const eat = () => input[pos++];
  function expr() {
    let n = term();
    while (peek() === '|' || peek() === '+') { eat(); n = { type: 'union', left: n, right: term() }; }
    return n;
  }
  function term() {
    let n = factor();
    while (peek() && !')|+'.includes(peek())) n = { type: 'concat', left: n, right: factor() };
    return n;
  }
  function factor() {
    let n = atom();
    while (peek() === '*') { eat(); n = { type: 'star', child: n }; }
    return n;
  }
  function atom() {
    if (peek() === '(') { eat(); const n = expr(); if (peek() !== ')') throw new Error('Unmatched ('); eat(); return n; }
    const c = peek();
    if (!c || ')|+*'.includes(c)) throw new Error('Unexpected: ' + (c || 'end'));
    eat();
    return { type: 'char', value: c };
  }
  const result = expr();
  if (pos < input.length) throw new Error('Unexpected character');
  return result;
}

// ==================== AST UTILS ====================
function astStr(n) {
  if (!n) return '';
  if (n.type === 'char') return n.value;
  if (n.type === 'epsilon') return EPSILON;
  if (n.type === 'concat') return astStr(n.left) + astStr(n.right);
  if (n.type === 'union') {
    const l = astStr(n.left), r = astStr(n.right);
    return l + '+' + r;
  }
  if (n.type === 'star') {
    const s = astStr(n.child);
    return (n.child.type === 'union' || n.child.type === 'concat') ? '(' + s + ')*' : s + '*';
  }
  return '';
}
function isAtomic(n) { return !n || n.type === 'char' || n.type === 'epsilon'; }
function flatConcat(n) { return n.type === 'concat' ? [...flatConcat(n.left), ...flatConcat(n.right)] : [n]; }
function flatUnion(n) { return n.type === 'union' ? [...flatUnion(n.left), ...flatUnion(n.right)] : [n]; }
function clone(o) { return JSON.parse(JSON.stringify(o)); }

// ==================== DECOMPOSITION ====================
function snap(g, desc) { return { nodes: clone(g.nodes), edges: clone(g.edges), description: desc }; }
function hasComplex(g) { return g.edges.some(e => e.ast && !isAtomic(e.ast)); }

function doConcat(g) {
  let changed = false; const add = [], rem = new Set();
  g.edges.forEach((e, i) => {
    if (e.ast?.type === 'concat') {
      rem.add(i); changed = true;
      const parts = flatConcat(e.ast); let prev = e.from;
      parts.forEach((p, j) => {
        const next = j === parts.length - 1 ? e.to : stateCounter++;
        if (j < parts.length - 1) g.nodes.push({ id: next, isStart: false, isAccept: false });
        add.push({ from: prev, to: next, ast: clone(p), label: astStr(p) });
        prev = next;
      });
    }
  });
  if (changed) g.edges = g.edges.filter((_, i) => !rem.has(i)).concat(add);
  return changed;
}

function doStar(g) {
  let changed = false; const add = [], rem = new Set();
  g.edges.forEach((e, i) => {
    if (e.ast?.type === 'star') {
      rem.add(i); changed = true;
      const qa = stateCounter++, qb = stateCounter++;
      g.nodes.push({ id: qa, isStart: false, isAccept: false }, { id: qb, isStart: false, isAccept: false });
      const inner = e.ast.child;
      add.push(
        { from: e.from, to: qa, ast: {type:'epsilon'}, label: EPSILON },
        { from: qa, to: qb, ast: clone(inner), label: astStr(inner) },
        { from: qb, to: qa, ast: {type:'epsilon'}, label: EPSILON },
        { from: qb, to: e.to, ast: {type:'epsilon'}, label: EPSILON },
        { from: e.from, to: e.to, ast: {type:'epsilon'}, label: EPSILON }
      );
    }
  });
  if (changed) g.edges = g.edges.filter((_, i) => !rem.has(i)).concat(add);
  return changed;
}

function doUnion(g) {
  let changed = false; const add = [], rem = new Set();
  g.edges.forEach((e, i) => {
    if (e.ast?.type === 'union') {
      rem.add(i); changed = true;
      for (const p of flatUnion(e.ast))
        add.push({ from: e.from, to: e.to, ast: clone(p), label: astStr(p) });
    }
  });
  if (changed) g.edges = g.edges.filter((_, i) => !rem.has(i)).concat(add);
  return changed;
}

// ==================== EPSILON ELIMINATION ====================
function elimEpsilon(g) {
  const closures = new Map();
  for (const node of g.nodes) {
    const cl = new Set([node.id]), q = [node.id];
    while (q.length) {
      const s = q.shift();
      for (const e of g.edges)
        if (e.from === s && e.ast?.type === 'epsilon' && !cl.has(e.to)) { cl.add(e.to); q.push(e.to); }
    }
    closures.set(node.id, cl);
  }
  for (const node of g.nodes)
    for (const s of closures.get(node.id)) {
      if (g.nodes.find(n => n.id === s)?.isAccept) { node.isAccept = true; break; }
    }
  const symbols = new Set();
  for (const e of g.edges) if (e.ast?.type !== 'epsilon') symbols.add(e.label);
  const newEdges = [], seen = new Set();
  for (const node of g.nodes)
    for (const sym of symbols) {
      const dests = new Set();
      for (const s of closures.get(node.id))
        for (const e of g.edges)
          if (e.from === s && e.label === sym)
            for (const t of closures.get(e.to)) dests.add(t);
      for (const d of dests) {
        const k = `${node.id}-${sym}-${d}`;
        if (!seen.has(k)) { seen.add(k); newEdges.push({ from: node.id, to: d, ast: {type:'char',value:sym}, label: sym }); }
      }
    }
  g.edges = newEdges;
  const startId = g.nodes.find(n => n.isStart)?.id;
  if (startId == null) return;
  const reach = new Set([startId]), rq = [startId];
  while (rq.length) { const s = rq.shift(); for (const e of g.edges) if (e.from === s && !reach.has(e.to)) { reach.add(e.to); rq.push(e.to); } }
  g.nodes = g.nodes.filter(n => reach.has(n.id));
  g.edges = g.edges.filter(e => reach.has(e.from) && reach.has(e.to));
}

// ==================== MAIN DECOMPOSE ====================
function decompose(regex) {
  stateCounter = 0;
  const ast = parseRegex(regex);
  const q0 = stateCounter++, qf = stateCounter++;
  const g = {
    nodes: [{ id: q0, isStart: true, isAccept: false }, { id: qf, isStart: false, isAccept: true }],
    edges: [{ from: q0, to: qf, ast: ast, label: astStr(ast) }]
  };
  const snaps = [];
  snaps.push(snap(g, 'Step 1: Construct initial transition graph — q\u2080 \u2192[' + astStr(ast) + ']\u2192 q_f'));
  if (doConcat(g))
    snaps.push(snap(g, 'Step 2: Remove concatenation — insert intermediate states'));
  if (doStar(g))
    snaps.push(snap(g, 'Step 3: Eliminate * (Kleene star) — 2 new states per star with \u03b5-moves'));
  let iter = 0, did = false;
  while (hasComplex(g) && iter++ < 30) {
    const c1 = doConcat(g), c2 = doUnion(g), c3 = doStar(g);
    if (!c1 && !c2 && !c3) break;
    did = true;
  }
  if (did)
    snaps.push(snap(g, 'Step 4: Eliminate remaining concatenation & addition operations'));
  elimEpsilon(g);
  snaps.push(snap(g, 'Step 5: Eliminate all \u03b5-moves — final NFA'));
  return snaps;
}

// ==================== LAYOUT ====================
function layoutGraph(snap) {
  const { nodes, edges } = snap;
  if (!nodes.length) return { positions: [], edgeList: [] };
  const startNode = nodes.find(n => n.isStart);
  const layers = new Map(), visited = new Set(), maxPerLayer = new Map();
  const queue = [{ id: startNode.id, layer: 0 }];
  layers.set(startNode.id, 0);
  while (queue.length) {
    const { id, layer } = queue.shift();
    if (visited.has(id)) continue;
    visited.add(id);
    maxPerLayer.set(layer, (maxPerLayer.get(layer) || 0) + 1);
    for (const e of edges) {
      if (e.from === id && !layers.has(e.to)) {
        layers.set(e.to, layer + 1);
        queue.push({ id: e.to, layer: layer + 1 });
      }
    }
  }
  for (const n of nodes) if (!layers.has(n.id)) { const l = (maxPerLayer.size || 0); layers.set(n.id, l); maxPerLayer.set(l, (maxPerLayer.get(l)||0)+1); }
  const layerCount = new Map();
  const numNodes = nodes.length;
  const hGap = numNodes > 8 ? 200 : 160;
  const vGap = numNodes > 8 ? 140 : 120;
  const positions = nodes.map(n => {
    const layer = layers.get(n.id) || 0;
    const idx = layerCount.get(layer) || 0;
    const total = maxPerLayer.get(layer) || 1;
    layerCount.set(layer, idx + 1);
    return { id: n.id, x: 120 + layer * hGap, y: 100 + (idx - (total - 1) / 2) * vGap, isStart: n.isStart, isAccept: n.isAccept };
  });
  const edgeMap = new Map();
  for (const e of edges) {
    const key = `${e.from}-${e.to}`;
    if (!edgeMap.has(key)) edgeMap.set(key, { from: e.from, to: e.to, labels: [] });
    if (!edgeMap.get(key).labels.includes(e.label)) edgeMap.get(key).labels.push(e.label);
  }
  const edgeList = [...edgeMap.values()].map(e => ({ from: e.from, to: e.to, label: e.labels.join(', ') }));
  return { positions, edgeList };
}

// ==================== RENDER ====================
function worldToScreen(x, y) { return [x * canvasScale + panX, y * canvasScale + panY]; }

function render() {
  if (!canvas.width) return;
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  if (!nodePositions.length) return;
  ctx.save();
  for (const edge of renderEdges) {
    const fn = nodePositions.find(n => n.id === edge.from);
    const tn = nodePositions.find(n => n.id === edge.to);
    if (!fn || !tn) continue;
    const isSelf = edge.from === edge.to;
    const [x1, y1] = worldToScreen(fn.x, fn.y);
    const [x2, y2] = worldToScreen(tn.x, tn.y);
    const isEps = edge.label.includes(EPSILON);
    ctx.save();
    ctx.strokeStyle = isEps ? '#44495e' : '#6060a0';
    ctx.lineWidth = 1.5 * canvasScale;
    if (isEps) ctx.setLineDash([4 * canvasScale, 3 * canvasScale]);
    if (isSelf) {
      const lr = R * canvasScale * 1.2;
      ctx.beginPath(); ctx.arc(x1, y1 - R * canvasScale - lr * 0.6, lr, 0.4, Math.PI * 1.8); ctx.stroke();
      drawArrow(ctx, x1 - 8, y1 - R * canvasScale, -0.5, '#6060a0');
      drawLabel(ctx, x1, y1 - R * canvasScale - lr * 1.4, edge.label, canvasScale);
    } else {
      const hasRev = renderEdges.some(e => e.from === edge.to && e.to === edge.from);
      if (hasRev) {
        const mx = (x1+x2)/2, my = (y1+y2)/2, dx = x2-x1, dy = y2-y1, len = Math.hypot(dx,dy)||1;
        const cx = mx - dy/len*40*canvasScale, cy = my + dx/len*40*canvasScale;
        ctx.beginPath(); ctx.moveTo(x1,y1); ctx.quadraticCurveTo(cx,cy,x2,y2); ctx.stroke();
        const tx = x2-cx, ty = y2-cy, tl = Math.hypot(tx,ty)||1;
        drawArrow(ctx, x2-(R*canvasScale)*tx/tl, y2-(R*canvasScale)*ty/tl, Math.atan2(ty,tx), isEps?'#44495e':'#6060a0');
        drawLabel(ctx, cx, cy, edge.label, canvasScale);
      } else {
        const angle = Math.atan2(y2-y1,x2-x1);
        const sx = x1+Math.cos(angle)*R*canvasScale, sy = y1+Math.sin(angle)*R*canvasScale;
        const ex = x2-Math.cos(angle)*R*canvasScale, ey = y2-Math.sin(angle)*R*canvasScale;
        ctx.beginPath(); ctx.moveTo(sx,sy); ctx.lineTo(ex,ey); ctx.stroke();
        drawArrow(ctx, ex, ey, angle, isEps?'#44495e':'#6060a0');
        const lx = (sx+ex)/2 - Math.sin(angle)*18*canvasScale;
        const ly = (sy+ey)/2 + Math.cos(angle)*18*canvasScale;
        drawLabel(ctx, lx, ly, edge.label, canvasScale);
      }
    }
    ctx.restore();
  }
  for (const node of nodePositions) {
    const [cx, cy] = worldToScreen(node.x, node.y);
    const r = R * canvasScale;
    if (node.isStart) {
      ctx.save(); ctx.strokeStyle = '#ffb347'; ctx.lineWidth = 2*canvasScale;
      ctx.beginPath(); ctx.moveTo(cx-r-28*canvasScale, cy); ctx.lineTo(cx-r, cy); ctx.stroke();
      drawArrow(ctx, cx-r, cy, 0, '#ffb347'); ctx.restore();
    }
    ctx.beginPath(); ctx.arc(cx, cy, r, 0, Math.PI*2);
    ctx.fillStyle = node.isAccept ? 'rgba(61,220,151,0.1)' : node.isStart ? 'rgba(255,179,71,0.08)' : '#1a1e2a';
    ctx.fill();
    ctx.lineWidth = (node.isStart ? 2 : 1.5) * canvasScale;
    ctx.strokeStyle = node.isAccept ? '#3ddc97' : node.isStart ? '#ffb347' : '#353c58';
    ctx.stroke();
    if (node.isAccept) { ctx.beginPath(); ctx.arc(cx, cy, r-5*canvasScale, 0, Math.PI*2); ctx.strokeStyle='#3ddc97'; ctx.lineWidth=1*canvasScale; ctx.stroke(); }
    ctx.fillStyle = '#e8eaf0';
    ctx.font = `${Math.max(11,13*canvasScale)}px 'JetBrains Mono',monospace`;
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.fillText(`q${node.id}`, cx, cy);
  }
  ctx.restore();
}

function drawArrow(ctx, x, y, angle, color) {
  const s = 8*canvasScale; ctx.save(); ctx.translate(x,y); ctx.rotate(angle);
  ctx.fillStyle = color; ctx.beginPath(); ctx.moveTo(0,0); ctx.lineTo(-s,-s*0.45); ctx.lineTo(-s,s*0.45); ctx.closePath(); ctx.fill(); ctx.restore();
}

function drawLabel(ctx, x, y, label, scale) {
  const fs = Math.max(10, 12*scale);
  ctx.font = `${fs}px 'JetBrains Mono',monospace`;
  const w = ctx.measureText(label).width + 10;
  ctx.fillStyle = '#13161e'; ctx.fillRect(x-w/2, y-fs*0.8, w, fs*1.6);
  ctx.fillStyle = (label.includes(EPSILON) && label.length <= 2) ? '#555c7a' : '#9d8ffb';
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText(label, x, y+fs*0.1);
}

// ==================== CANVAS EVENTS ====================
function resizeCanvas() {
  const rect = canvas.parentElement.getBoundingClientRect();
  const w = Math.max(rect.width, 400);
  const h = Math.max(rect.height, 300);
  canvas.width = w; canvas.height = h; render();
}
window.addEventListener('resize', resizeCanvas);
canvas.addEventListener('mousedown', e => { isPanning = true; lastPan = {x:e.clientX,y:e.clientY}; });
canvas.addEventListener('mousemove', e => { if(!isPanning)return; panX+=e.clientX-lastPan.x; panY+=e.clientY-lastPan.y; lastPan={x:e.clientX,y:e.clientY}; render(); });
canvas.addEventListener('mouseup', () => isPanning=false);
canvas.addEventListener('mouseleave', () => isPanning=false);
canvas.addEventListener('wheel', e => { e.preventDefault(); const f=e.deltaY<0?1.1:0.9; const rect=canvas.getBoundingClientRect(); const mx=e.clientX-rect.left,my=e.clientY-rect.top; panX=mx-f*(mx-panX); panY=my-f*(my-panY); canvasScale*=f; render(); }, {passive:false});
canvas.addEventListener('touchstart', e => { if(e.touches.length===1){isPanning=true;lastPan={x:e.touches[0].clientX,y:e.touches[0].clientY};} });
canvas.addEventListener('touchmove', e => { e.preventDefault();if(!isPanning||e.touches.length!==1)return; panX+=e.touches[0].clientX-lastPan.x;panY+=e.touches[0].clientY-lastPan.y;lastPan={x:e.touches[0].clientX,y:e.touches[0].clientY};render(); },{passive:false});
canvas.addEventListener('touchend', ()=>isPanning=false);

function zoomFit() {
  if (!nodePositions.length) return;
  const xs = nodePositions.map(n=>n.x), ys = nodePositions.map(n=>n.y);
  const minX=Math.min(...xs)-80, maxX=Math.max(...xs)+80, minY=Math.min(...ys)-80, maxY=Math.max(...ys)+80;
  const w=maxX-minX, h=maxY-minY;
  canvasScale = Math.min(canvas.width/w, canvas.height/h, 1.5);
  panX = (canvas.width-w*canvasScale)/2 - minX*canvasScale;
  panY = (canvas.height-h*canvasScale)/2 - minY*canvasScale;
  render();
}
function resetView() { canvasScale=1; panX=0; panY=0; render(); }

// ==================== TRANSITION TABLE ====================
function buildTable(snap) {
  const table = document.getElementById('trans-table');
  const { nodes, edges } = snap;
  const symbols = [...new Set(edges.map(e => e.label))].sort((a,b) => a===EPSILON?-1:b===EPSILON?1:a.localeCompare(b));
  let html = '<tr><th>State</th>' + symbols.map(s => `<th>${s}</th>`).join('') + '</tr>';
  for (const n of nodes) {
    const cls = (n.isStart ? 'start-state' : '') + ' ' + (n.isAccept ? 'accept-state' : '');
    let row = `<tr><td class="${cls}">${n.isStart?'→':''}q${n.id}${n.isAccept?'*':''}</td>`;
    for (const sym of symbols) {
      const dests = edges.filter(e => e.from === n.id && e.label === sym).map(e => 'q'+e.to);
      row += `<td>${dests.length ? [...new Set(dests)].join(',') : '∅'}</td>`;
    }
    html += row + '</tr>';
  }
  table.innerHTML = html;
}

// ==================== STATS ====================
function updateStats(snap) {
  const symbols = new Set();
  for (const e of snap.edges) if (e.label !== EPSILON) symbols.add(e.label);
  document.getElementById('stats-grid').innerHTML = `
    <div class="stat-card"><div class="stat-label">STATES</div><div class="stat-value accent">${snap.nodes.length}</div></div>
    <div class="stat-card"><div class="stat-label">TRANSITIONS</div><div class="stat-value green">${snap.edges.length}</div></div>
    <div class="stat-card"><div class="stat-label">ALPHABET</div><div class="stat-value" style="font-size:14px">{${[...symbols].join(',')}}</div></div>
    <div class="stat-card"><div class="stat-label">ε-MOVES</div><div class="stat-value">${snap.edges.filter(e=>e.label===EPSILON).length}</div></div>
  `;
}

// ==================== STEPPER ====================
function showStep(idx) {
  if (idx < 0 || idx >= snapshots.length) return;
  currentStep = idx;
  const s = snapshots[idx];
  const { positions, edgeList } = layoutGraph(s);
  nodePositions = positions;
  renderEdges = edgeList;
  document.getElementById('step-counter').textContent = `Step ${idx+1} / ${snapshots.length}`;
  document.getElementById('step-description').textContent = s.description;
  document.getElementById('btn-prev').disabled = idx === 0;
  document.getElementById('btn-next').disabled = idx === snapshots.length - 1;
  const dots = document.getElementById('step-progress');
  dots.innerHTML = snapshots.map((_, i) => `<div class="step-dot ${i<idx?'done':''} ${i===idx?'active':''}"></div>`).join('');
  buildTable(s);
  updateStats(s);
  requestAnimationFrame(() => { resizeCanvas(); zoomFit(); });
}
function stepPrev() { showStep(currentStep - 1); }
function stepNext() { showStep(currentStep + 1); }

// ==================== SIMULATE ====================
function simulate() {
  const input = document.getElementById('sim-input').value;
  const resultEl = document.getElementById('sim-result');
  if (!snapshots.length) { resultEl.style.display='none'; return; }
  const final = snapshots[snapshots.length - 1];
  const startNode = final.nodes.find(n => n.isStart);
  if (!startNode) { resultEl.innerHTML = '<div class="sim-result sim-reject"><div class="sim-dot"></div>No start state</div>'; resultEl.style.display='block'; return; }
  let current = new Set([startNode.id]);
  for (const ch of input) {
    const next = new Set();
    for (const s of current)
      for (const e of final.edges)
        if (e.from === s && e.label === ch) next.add(e.to);
    if (next.size === 0) {
      resultEl.innerHTML = `<div class="sim-result sim-reject"><div class="sim-dot"></div>Rejected — no transition on '${ch}'</div>`;
      resultEl.style.display='block'; return;
    }
    current = next;
  }
  const accepted = [...current].some(s => final.nodes.find(n => n.id === s)?.isAccept);
  resultEl.innerHTML = accepted
    ? `<div class="sim-result sim-accept"><div class="sim-dot"></div>Accepted ✓</div>`
    : `<div class="sim-result sim-reject"><div class="sim-dot"></div>Rejected — not in accept state</div>`;
  resultEl.style.display = 'block';
}

// ==================== BUILD ====================
function validateRegex(re) {
  if (!re.trim()) throw new Error('Empty expression');
  let depth = 0;
  for (const c of re) {
    if (c === '(') depth++;
    else if (c === ')') { depth--; if (depth < 0) throw new Error('Unmatched )'); }
  }
  if (depth !== 0) throw new Error('Unmatched (');
}

function buildAutomaton() {
  const re = document.getElementById('regex-input').value.trim();
  const errEl = document.getElementById('error-msg');
  errEl.textContent = '';
  try {
    validateRegex(re);
    snapshots = decompose(re);
    currentStep = 0;
    document.getElementById('empty-state').style.display = 'none';
    document.getElementById('legend').style.display = 'flex';
    document.getElementById('stats-panel').style.display = 'block';
    document.getElementById('table-panel').style.display = 'block';
    document.getElementById('stepper-bar').classList.add('visible');
    document.getElementById('sim-result').style.display = 'none';
    showStep(0);
  } catch (e) {
    errEl.textContent = '✗ ' + e.message;
    document.getElementById('regex-input').classList.add('error');
    setTimeout(() => document.getElementById('regex-input').classList.remove('error'), 1500);
  }
}

function loadExample(re) {
  document.getElementById('regex-input').value = re;
  buildAutomaton();
}

// ==================== EVENT HANDLERS ====================
document.getElementById('regex-input').addEventListener('keydown', e => { if (e.key === 'Enter') buildAutomaton(); });
document.getElementById('sim-input').addEventListener('keydown', e => { if (e.key === 'Enter') simulate(); });
resizeCanvas();
setTimeout(() => loadExample('(a|b)*abb'), 100);
