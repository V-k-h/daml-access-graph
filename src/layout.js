// src/layout.js
//
// Deterministic, dependency-free graph layout. Pure: takes a ViewGraph (see
// src/view.js) and returns positions. No DOM, no Math.random, no timers.
//
// Two layouts, because the collapsed view and the expanded view are different
// pictures:
//
//   forceLayout   - Barnes-Hut approximated spring embedder with per-module
//                   clustering. Used for the expanded / detail views, where
//                   there is no meaningful hierarchy to exploit.
//   layeredLayout - a Sugiyama-style layered layout over the LIFECYCLE edges
//                   (create / exercise / archive / ...). The collapsed
//                   repository view is a lifecycle graph, and a lifecycle
//                   reads far better as layers than as a ball of springs:
//                   "what creates what" becomes a left-to-right direction
//                   rather than something the reader has to trace.
//
// DETERMINISM is a hard requirement (the project has tests that depend on it).
// Two properties are guaranteed and tested:
//   1. same input        -> byte-identical output
//   2. permuted input    -> identical position PER NODE ID
// (2) is why every stage sorts by id before doing anything order-sensitive.
// Floating-point addition is not commutative, so without the sort the force
// accumulation would drift with input order.

/** @typedef {import('./view.js').ViewGraph} ViewGraph */

const GOLDEN_ANGLE = Math.PI * (3 - Math.sqrt(5));

/**
 * Deterministic starting positions on a phyllotactic (sunflower) spiral.
 *
 * A spiral beats the previous "spread on a circle" seeding for two reasons:
 * every node starts at a distinct radius so coincident points never happen,
 * and the interior of the canvas is populated, so the simulation does not have
 * to push 200 nodes off a single ring before it can start separating clusters.
 *
 * @param {number} i index in the id-sorted node list
 * @param {number} n total
 * @param {number} cx
 * @param {number} cy
 * @param {number} spread
 */
function seedPosition(i, n, cx, cy, spread) {
  const r = spread * Math.sqrt((i + 0.5) / Math.max(1, n));
  const a = i * GOLDEN_ANGLE;
  return { x: cx + r * Math.cos(a), y: cy + r * Math.sin(a) };
}

// ---------------------------------------------------------------- quadtree

/**
 * A Barnes-Hut quadtree over points, carrying mass and centre of mass.
 *
 * Barnes-Hut turns the O(n^2) repulsion loop into O(n log n) by treating a
 * distant cluster as a single body. It is NOT unconditionally faster: building
 * the tree once per iteration costs more than the exact sum until the graph is
 * big enough to amortise it. Measured on this implementation (320 iterations,
 * n nodes / 2n edges, node 22, M-series):
 *
 *     n      exact    Barnes-Hut
 *     200     16ms        27ms
 *     400     63ms        70ms
 *     600    132ms       116ms   <- crossover sits near here
 *    1200    602ms       320ms
 *    2000   1933ms       629ms
 *
 * So the repository-scale graphs this tool actually renders (~200 nodes) use
 * the EXACT sum, and Barnes-Hut exists to keep a much larger repository from
 * falling off a quadratic cliff. Picking BH at 200 nodes would have made the
 * common case twice as slow while looking like an optimisation.
 */
function buildQuadtree(nodes) {
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  for (const n of nodes) {
    if (n.x < minX) minX = n.x;
    if (n.y < minY) minY = n.y;
    if (n.x > maxX) maxX = n.x;
    if (n.y > maxY) maxY = n.y;
  }
  if (!Number.isFinite(minX)) return null;
  // Square, slightly padded root cell.
  const size = Math.max(maxX - minX, maxY - minY, 1) * 1.01;
  const root = cell(minX, minY, size);
  for (const n of nodes) insert(root, n, 0);
  return root;
}

function cell(x, y, size) {
  return { x, y, size, mass: 0, cx: 0, cy: 0, body: null, kids: null };
}

const MAX_DEPTH = 24; // guards against exactly-coincident points

/**
 * Node count above which Barnes-Hut beats the exact repulsion sum.
 * Measured, not guessed - see the table above buildQuadtree().
 */
export const BH_THRESHOLD = 500;

function insert(c, p, depth) {
  // Running centre of mass.
  const m = c.mass + 1;
  c.cx = (c.cx * c.mass + p.x) / m;
  c.cy = (c.cy * c.mass + p.y) / m;
  c.mass = m;

  if (c.kids === null && c.body === null) { c.body = p; return; }
  if (depth >= MAX_DEPTH) return; // bail out; coincident points just stack up

  if (c.kids === null) {
    const old = c.body;
    c.body = null;
    c.kids = [null, null, null, null];
    place(c, old, depth);
  }
  place(c, p, depth);
}

function place(c, p, depth) {
  const half = c.size / 2;
  const qx = p.x >= c.x + half ? 1 : 0;
  const qy = p.y >= c.y + half ? 1 : 0;
  const i = qy * 2 + qx;
  if (c.kids[i] === null) c.kids[i] = cell(c.x + qx * half, c.y + qy * half, half);
  insert(c.kids[i], p, depth + 1);
}

/** Accumulate repulsion on `p` from the tree, using the theta criterion. */
function repulse(c, p, theta, strength, out) {
  if (c === null || c.mass === 0) return;
  let dx = p.x - c.cx;
  let dy = p.y - c.cy;
  let d2 = dx * dx + dy * dy;

  if (c.body !== null) {
    if (c.body === p) return;
    if (d2 < 0.01) {
      // Coincident: nudge along a deterministic axis rather than dividing by 0.
      dx = 0.01; dy = 0; d2 = 0.0001;
    }
    const f = (strength * c.mass) / d2;
    const d = Math.sqrt(d2);
    out.x += (dx / d) * f;
    out.y += (dy / d) * f;
    return;
  }
  if (d2 < 1e-9) d2 = 1e-9;
  // Far enough away to treat the whole cell as one body?
  if ((c.size * c.size) / d2 < theta * theta) {
    const f = (strength * c.mass) / d2;
    const d = Math.sqrt(d2);
    out.x += (dx / d) * f;
    out.y += (dy / d) * f;
    return;
  }
  if (c.kids) for (const k of c.kids) repulse(k, p, theta, strength, out);
}

// ------------------------------------------------------------ force layout

/**
 * Spring embedder with Barnes-Hut repulsion, module clustering and annealing.
 *
 * Module clustering is the part that actually buys legibility at repository
 * scale. Each module gets a fixed anchor on a ring (ordered by module name, so
 * it is stable across runs) and every node is weakly pulled toward its own
 * module's anchor. Modules then occupy distinct regions instead of being
 * interleaved, which is what makes "where does this template live" answerable
 * at a glance. The pull is weak enough that a template with strong cross-module
 * edges still drifts toward its real neighbours.
 *
 * @param {ViewGraph} view
 * @param {Object} [options]
 * @returns {{positions: Map<string,{x:number,y:number}>, bounds: Object, iterations: number, ms: number}}
 */
export function forceLayout(view, options = {}) {
  const width = options.width || 1000;
  const height = options.height || 700;
  const iterations = options.iterations === undefined ? 320 : options.iterations;
  const repelStrength = options.repel === undefined ? 5200 : options.repel;
  const spring = options.spring === undefined ? 0.05 : options.spring;
  const restLength = options.restLength === undefined ? 90 : options.restLength;
  const gravity = options.gravity === undefined ? 0.012 : options.gravity;
  const clusterPull = options.clusterPull === undefined ? 0.035 : options.clusterPull;
  const theta = options.theta === undefined ? 0.9 : options.theta;
  const exact = options.exact === undefined ? view.nodes.length <= BH_THRESHOLD : options.exact;
  const t0 = now();

  const cx = width / 2;
  const cy = height / 2;

  // Sort by id: the single thing that makes the result permutation-stable.
  const sorted = [...view.nodes].sort((a, b) => (a.id < b.id ? -1 : a.id > b.id ? 1 : 0));
  const n = sorted.length;
  const spread = Math.min(width, height) * 0.42;
  const nodes = sorted.map((v, i) => {
    const p = seedPosition(i, n, cx, cy, spread);
    return { id: v.id, x: p.x, y: p.y, vx: 0, vy: 0, module: v.module === null ? '(no module)' : v.module };
  });
  const index = new Map(nodes.map((p) => [p.id, p]));

  // Module anchors on a ring, ordered by name so they never move between runs.
  const moduleNames = [...new Set(nodes.map((p) => p.module))].sort();
  const anchors = new Map();
  const anchorR = Math.min(width, height) * 0.31;
  moduleNames.forEach((m, i) => {
    const a = (i / Math.max(1, moduleNames.length)) * Math.PI * 2;
    anchors.set(m, { x: cx + anchorR * Math.cos(a), y: cy + anchorR * Math.sin(a) });
  });
  // With one module (or none named) clustering is meaningless; switch it off so
  // a small single-module graph is not squashed onto one point.
  const clustering = moduleNames.length > 1 ? clusterPull : 0;

  const links = [];
  for (const e of view.edges) {
    const s = index.get(e.source);
    const t = index.get(e.target);
    if (s && t && s !== t) links.push({ s, t, w: 1 });
  }
  links.sort((a, b) => (a.s.id < b.s.id ? -1 : a.s.id > b.s.id ? 1 : a.t.id < b.t.id ? -1 : a.t.id > b.t.id ? 1 : 0));

  const force = { x: 0, y: 0 };
  for (let step = 0; step < iterations; step++) {
    // Annealing: large moves early to untangle, small moves late to settle.
    // The old layout used a fixed clamp for all 300 iterations, which is why it
    // never converged: it kept taking 15px steps right to the end.
    const temperature = Math.max(1, (1 - step / iterations) * 28 + 0.6);

    if (exact) {
      for (let i = 0; i < n; i++) {
        for (let j = i + 1; j < n; j++) {
          const a = nodes[i];
          const b = nodes[j];
          let dx = a.x - b.x;
          let dy = a.y - b.y;
          let d2 = dx * dx + dy * dy;
          if (d2 < 0.01) { dx = 0.01; dy = 0; d2 = 0.0001; }
          const d = Math.sqrt(d2);
          const f = repelStrength / d2;
          const fx = (dx / d) * f;
          const fy = (dy / d) * f;
          a.vx += fx; a.vy += fy;
          b.vx -= fx; b.vy -= fy;
        }
      }
    } else {
      const tree = buildQuadtree(nodes);
      for (const p of nodes) {
        force.x = 0; force.y = 0;
        repulse(tree, p, theta, repelStrength, force);
        p.vx += force.x;
        p.vy += force.y;
      }
    }

    for (const l of links) {
      const dx = l.t.x - l.s.x;
      const dy = l.t.y - l.s.y;
      const d = Math.sqrt(dx * dx + dy * dy) || 0.01;
      const f = (d - restLength) * spring;
      const fx = (dx / d) * f;
      const fy = (dy / d) * f;
      l.s.vx += fx; l.s.vy += fy;
      l.t.vx -= fx; l.t.vy -= fy;
    }

    for (const p of nodes) {
      if (clustering > 0) {
        const a = anchors.get(p.module);
        if (a) { p.vx += (a.x - p.x) * clustering; p.vy += (a.y - p.y) * clustering; }
      }
      p.vx += (cx - p.x) * gravity;
      p.vy += (cy - p.y) * gravity;
      p.vx *= 0.82;
      p.vy *= 0.82;
      const sp = Math.sqrt(p.vx * p.vx + p.vy * p.vy);
      if (sp > temperature) { p.vx = (p.vx / sp) * temperature; p.vy = (p.vy / sp) * temperature; }
      p.x += p.vx;
      p.y += p.vy;
    }
  }

  const positions = new Map(nodes.map((p) => [p.id, { x: round(p.x), y: round(p.y) }]));
  return { positions, bounds: boundsOf(positions), iterations, ms: now() - t0, mode: exact ? 'force-exact' : 'force-bh' };
}

// ----------------------------------------------------------- layered layout

/**
 * Layered (Sugiyama-style) layout, for the collapsed lifecycle view.
 *
 * Steps: choose hierarchy edges -> break cycles -> assign layers by longest
 * path -> order within each layer by barycentre sweeps -> assign coordinates.
 *
 * Cycle breaking is not optional here: the canton sample's own analysis reports
 * a `lifecycle-cycle` finding, so real repositories do contain them. Back edges
 * are detected by a DFS over id-sorted adjacency (deterministic) and are simply
 * excluded from layering; they are still drawn, just pointing backwards.
 *
 * @param {ViewGraph} view
 * @param {Object} [options]
 */
export function layeredLayout(view, options = {}) {
  const width = options.width || 1000;
  const height = options.height || 700;
  const layerGap = options.layerGap === undefined ? 210 : options.layerGap;
  const rowGap = options.rowGap === undefined ? 76 : options.rowGap;
  const sweeps = options.sweeps === undefined ? 6 : options.sweeps;
  const hierarchyKinds = options.hierarchyKinds || null;
  const t0 = now();

  const ids = view.nodes.map((v) => v.id).sort();
  const idSet = new Set(ids);
  if (ids.length === 0) {
    return { positions: new Map(), bounds: boundsOf(new Map()), layers: [], ms: now() - t0, mode: 'layered' };
  }

  // Hierarchy edges: the lifecycle ones if there are any, else everything.
  // Falling back matters for a structural-only view, which would otherwise
  // layer nothing and degenerate to a single column.
  let hier = view.edges.filter(
    (e) => !e.selfLoop && idSet.has(e.source) && idSet.has(e.target) &&
      (hierarchyKinds ? hierarchyKinds.has(e.kind) : e.group === 'operational')
  );
  if (hier.length === 0) {
    hier = view.edges.filter((e) => !e.selfLoop && idSet.has(e.source) && idSet.has(e.target));
  }
  // Deduplicate and sort, so the DFS is order-independent.
  const pairSeen = new Set();
  const pairs = [];
  for (const e of hier) {
    const k = `${e.source} ${e.target}`;
    if (pairSeen.has(k)) continue;
    pairSeen.add(k);
    pairs.push({ s: e.source, t: e.target });
  }
  pairs.sort((a, b) => (a.s < b.s ? -1 : a.s > b.s ? 1 : a.t < b.t ? -1 : a.t > b.t ? 1 : 0));

  const out = new Map(ids.map((i) => [i, []]));
  for (const p of pairs) out.get(p.s).push(p.t);
  for (const l of out.values()) l.sort();

  // --- break cycles: iterative DFS, mark edges that point back onto the stack
  const WHITE = 0, GREY = 1, BLACK = 2;
  const color = new Map(ids.map((i) => [i, WHITE]));
  const back = new Set();
  for (const root of ids) {
    if (color.get(root) !== WHITE) continue;
    const stack = [{ id: root, i: 0 }];
    color.set(root, GREY);
    while (stack.length) {
      const top = stack[stack.length - 1];
      const kids = out.get(top.id);
      if (top.i >= kids.length) { color.set(top.id, BLACK); stack.pop(); continue; }
      const next = kids[top.i++];
      const c = color.get(next);
      if (c === GREY) { back.add(`${top.id} ${next}`); continue; }
      if (c === BLACK) continue;
      color.set(next, GREY);
      stack.push({ id: next, i: 0 });
    }
  }
  const dag = pairs.filter((p) => !back.has(`${p.s} ${p.t}`));

  // --- layer assignment: longest path from the sources of the DAG
  const dagOut = new Map(ids.map((i) => [i, []]));
  const indeg = new Map(ids.map((i) => [i, 0]));
  for (const p of dag) { dagOut.get(p.s).push(p.t); indeg.set(p.t, indeg.get(p.t) + 1); }
  for (const l of dagOut.values()) l.sort();

  const layer = new Map(ids.map((i) => [i, 0]));
  const queue = ids.filter((i) => indeg.get(i) === 0).sort();
  const deg = new Map(indeg);
  let head = 0;
  while (head < queue.length) {
    const cur = queue[head++];
    for (const nx of dagOut.get(cur)) {
      if (layer.get(nx) < layer.get(cur) + 1) layer.set(nx, layer.get(cur) + 1);
      deg.set(nx, deg.get(nx) - 1);
      if (deg.get(nx) === 0) queue.push(nx);
    }
  }

  // --- order within layers, barycentre sweeps
  const maxLayer = Math.max(...ids.map((i) => layer.get(i)));
  /** @type {string[][]} */
  const layers = [];
  for (let i = 0; i <= maxLayer; i++) layers.push([]);
  for (const id of ids) layers[layer.get(id)].push(id);
  for (const l of layers) l.sort();

  const pos = new Map();
  for (const l of layers) l.forEach((id, i) => pos.set(id, i));

  const preds = new Map(ids.map((i) => [i, []]));
  const succs = new Map(ids.map((i) => [i, []]));
  for (const p of dag) { succs.get(p.s).push(p.t); preds.get(p.t).push(p.s); }

  const bary = (id, rel) => {
    const ns = rel.get(id);
    if (!ns || ns.length === 0) return pos.get(id);
    let s = 0;
    for (const x of ns) s += pos.get(x);
    return s / ns.length;
  };
  for (let sweep = 0; sweep < sweeps; sweep++) {
    const downward = sweep % 2 === 0;
    const order = downward ? layers : [...layers].reverse();
    for (const l of order) {
      const rel = downward ? preds : succs;
      const keyed = l.map((id) => ({ id, k: bary(id, rel) }));
      // Ties broken by id, so the sweep can never be order-dependent.
      keyed.sort((a, b) => a.k - b.k || (a.id < b.id ? -1 : a.id > b.id ? 1 : 0));
      keyed.forEach((e, i) => pos.set(e.id, i));
      l.length = 0;
      for (const e of keyed) l.push(e.id);
    }
  }

  // --- coordinates: layers advance in x, members stack in y.
  //
  // A layer is WRAPPED into sub-columns when it is taller than the viewport.
  // Without this, a real repository degenerates: on the canton sample 4 layers
  // hold 28 templates but the widest layer holds ~24, giving a drawing 1900px
  // tall and 630px wide. Fitted to a viewport that is a column of unreadable
  // dots. Wrapping trades a little layer purity for an aspect ratio a reader
  // can actually use; sub-columns stay inside their layer's band, so the
  // left-to-right "what creates what" reading survives.
  const maxRows = Math.max(3, Math.floor((height - 100) / rowGap));
  const positions = new Map();
  let x = 90;
  const layerX = [];
  layers.forEach((l) => {
    const cols = Math.max(1, Math.ceil(l.length / maxRows));
    const perCol = Math.ceil(l.length / cols);
    const subGap = cols > 1 ? Math.min(layerGap * 0.55, 150) : 0;
    layerX.push(x);
    for (let c = 0; c < cols; c++) {
      const slice = l.slice(c * perCol, (c + 1) * perCol);
      const cxCol = x + c * subGap;
      const top = Math.max(60, height / 2 - ((slice.length - 1) * rowGap) / 2);
      slice.forEach((id, i) => positions.set(id, { x: round(cxCol), y: round(top + i * rowGap) }));
    }
    x += (cols - 1) * subGap + layerGap;
  });

  return {
    positions,
    bounds: boundsOf(positions),
    layers: layers.map((l) => l.slice()),
    layerX,
    backEdges: [...back].sort(),
    ms: now() - t0,
    mode: 'layered',
    width,
    height,
  };
}

/**
 * Pick a layout. The collapsed repository view is a lifecycle graph and reads
 * better layered; anything with expanded detail goes back to force, because
 * party and choice nodes have no lifecycle direction to lay out along.
 *
 * @param {ViewGraph} view
 * @param {{mode?: 'auto'|'force'|'layered'}} [options]
 */
export function layoutGraph(view, options = {}) {
  const mode = options.mode || 'auto';
  if (mode === 'layered') return layeredLayout(view, options);
  if (mode === 'force') return forceLayout(view, options);
  const anyExpanded = view.nodes.some((n) => n.expanded) ||
    view.nodes.some((n) => n.kind !== 'template' && n.kind !== 'interface');
  const anyOperational = view.edges.some((e) => e.group === 'operational' && !e.selfLoop);
  return anyExpanded || !anyOperational ? forceLayout(view, options) : layeredLayout(view, options);
}

/**
 * Fit positions into a viewport, preserving aspect ratio.
 * Returned separately from layout so that layout stays a pure function of the
 * graph and the viewport can change (resize, zoom) without recomputing it.
 */
export function fitToViewport(positions, width, height, padding = 60) {
  const b = boundsOf(positions);
  if (!Number.isFinite(b.minX)) return { scale: 1, tx: 0, ty: 0 };
  const w = Math.max(b.maxX - b.minX, 1);
  const h = Math.max(b.maxY - b.minY, 1);
  const scale = Math.min((width - padding * 2) / w, (height - padding * 2) / h, 1.6);
  return {
    scale,
    tx: padding - b.minX * scale + Math.max(0, (width - padding * 2 - w * scale) / 2),
    ty: padding - b.minY * scale + Math.max(0, (height - padding * 2 - h * scale) / 2),
  };
}

function boundsOf(positions) {
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  for (const p of positions.values()) {
    if (p.x < minX) minX = p.x;
    if (p.y < minY) minY = p.y;
    if (p.x > maxX) maxX = p.x;
    if (p.y > maxY) maxY = p.y;
  }
  return { minX, minY, maxX, maxY };
}

// Positions are rounded to 1e-4 so that "same input, same output" is a
// byte-for-byte property rather than one that depends on the last bits of a
// float. The renderer does not need more precision than this.
const round = (v) => Math.round(v * 10000) / 10000;

const now = () =>
  (typeof performance !== 'undefined' && performance.now ? performance.now() : Date.now());

export { seedPosition, buildQuadtree };
