// src/renderer.js
//
// A tiny dependency-free SVG renderer with a basic force-directed layout.
// Not a real graph library — just enough to make the access structure legible.

const SVG_NS = 'http://www.w3.org/2000/svg';

const NODE_STYLE = {
  template: { r: 26, fill: '#2563eb', stroke: '#1e3a8a' },
  party: { r: 18, fill: '#16a34a', stroke: '#14532d' },
  choice: { r: 20, fill: '#d97706', stroke: '#7c2d12' },
};

const EDGE_STYLE = {
  declares: { color: '#94a3b8', dash: '0' },
  signatory: { color: '#dc2626', dash: '0' },
  observer: { color: '#0891b2', dash: '4 3' },
  controller: { color: '#d97706', dash: '0' },
  create: { color: '#16a34a', dash: '0' },
  createAndExercise: { color: '#16a34a', dash: '2 2' },
  exercise: { color: '#7c3aed', dash: '0' },
  exerciseByKey: { color: '#7c3aed', dash: '2 2' },
  fetch: { color: '#64748b', dash: '4 3' },
  fetchByKey: { color: '#64748b', dash: '4 3' },
  lookupByKey: { color: '#64748b', dash: '1 3' },
  archive: { color: '#334155', dash: '6 3' },
};

/**
 * Render a normalized graph into an SVG element.
 * @param {SVGSVGElement} svg
 * @param {import('./graph.js').Graph} graph
 */
export function renderGraph(svg, graph) {
  while (svg.firstChild) svg.removeChild(svg.firstChild);

  const width = svg.clientWidth || 800;
  const height = svg.clientHeight || 600;

  const nodes = graph.nodes.map((n, i) => ({
    ...n,
    // deterministic initial spread on a circle (no Math.random for stability)
    x: width / 2 + Math.cos((i / Math.max(1, graph.nodes.length)) * Math.PI * 2) * 150,
    y: height / 2 + Math.sin((i / Math.max(1, graph.nodes.length)) * Math.PI * 2) * 150,
    vx: 0,
    vy: 0,
  }));
  const index = new Map(nodes.map((n) => [n.id, n]));
  const links = graph.edges
    .map((e) => ({ ...e, s: index.get(e.source), t: index.get(e.target) }))
    .filter((e) => e.s && e.t);

  runLayout(nodes, links, width, height);

  // defs: arrow markers per edge color (dedupe by color)
  const defs = document.createElementNS(SVG_NS, 'defs');
  const colors = new Set(links.map((l) => (EDGE_STYLE[l.kind] || EDGE_STYLE.declares).color));
  for (const c of colors) {
    const marker = el('marker', {
      id: markerId(c),
      viewBox: '0 0 10 10',
      refX: '10',
      refY: '5',
      markerWidth: '7',
      markerHeight: '7',
      orient: 'auto-start-reverse',
    });
    marker.appendChild(el('path', { d: 'M 0 0 L 10 5 L 0 10 z', fill: c }));
    defs.appendChild(marker);
  }
  svg.appendChild(defs);

  const linkLayer = el('g', { class: 'links' });
  const nodeLayer = el('g', { class: 'nodes' });
  svg.appendChild(linkLayer);
  svg.appendChild(nodeLayer);

  const lineEls = links.map((l) => {
    const style = EDGE_STYLE[l.kind] || EDGE_STYLE.declares;
    const line = el('line', {
      stroke: style.color,
      'stroke-width': '1.6',
      'stroke-dasharray': style.dash,
      'marker-end': `url(#${markerId(style.color)})`,
    });
    const title = el('title');
    title.textContent = `${l.s.label} —${l.kind}→ ${l.t.label}`;
    line.appendChild(title);
    linkLayer.appendChild(line);
    return { l, line };
  });

  const nodeEls = nodes.map((n) => {
    const style = NODE_STYLE[n.kind] || NODE_STYLE.template;
    const g = el('g', { class: `node node-${n.kind}`, 'data-id': n.id });
    const external = n.meta && n.meta.external;
    const nonconsuming = n.kind === 'choice' && n.meta && n.meta.consuming === false;

    const circle = el('circle', {
      r: String(style.r),
      fill: external ? '#e2e8f0' : style.fill,
      stroke: style.stroke,
      'stroke-width': external ? '1.5' : '2',
      'stroke-dasharray': external ? '4 2' : nonconsuming ? '3 2' : '0',
    });
    const label = el('text', {
      'text-anchor': 'middle',
      dy: String(style.r + 13),
      class: 'node-label',
    });
    label.textContent = n.label;

    const title = el('title');
    title.textContent = nodeTooltip(n);

    g.appendChild(circle);
    g.appendChild(label);
    g.appendChild(title);
    nodeLayer.appendChild(g);

    enableDrag(g, n, svg, () => tick(lineEls, nodeEls));
    return { n, g };
  });

  tick(lineEls, nodeEls);
}

function nodeTooltip(n) {
  if (n.kind === 'template') return `template ${n.label}${n.meta && n.meta.external ? ' (external)' : ''}`;
  if (n.kind === 'choice') {
    return `choice ${n.template}.${n.label} (${n.meta && n.meta.consuming === false ? 'nonconsuming' : 'consuming'})`;
  }
  if (n.kind === 'party') {
    return `party ${n.template}.${n.label}${n.meta && n.meta.fromArg ? ' (from choice argument)' : ''}`;
  }
  return n.label;
}

function tick(lineEls, nodeEls) {
  for (const { l, line } of lineEls) {
    line.setAttribute('x1', l.s.x);
    line.setAttribute('y1', l.s.y);
    line.setAttribute('x2', l.t.x);
    line.setAttribute('y2', l.t.y);
  }
  for (const { n, g } of nodeEls) {
    g.setAttribute('transform', `translate(${n.x},${n.y})`);
  }
}

/** Simple O(n^2) spring/repulsion simulation, fixed iteration count. */
function runLayout(nodes, links, width, height) {
  const cx = width / 2;
  const cy = height / 2;
  const REPULSE = 6000;
  const SPRING = 0.02;
  const REST = 110;
  const CENTER = 0.01;
  const ITER = 300;

  for (let step = 0; step < ITER; step++) {
    // repulsion
    for (let i = 0; i < nodes.length; i++) {
      for (let j = i + 1; j < nodes.length; j++) {
        const a = nodes[i];
        const b = nodes[j];
        let dx = a.x - b.x;
        let dy = a.y - b.y;
        let d2 = dx * dx + dy * dy || 0.01;
        const f = REPULSE / d2;
        const d = Math.sqrt(d2);
        const fx = (dx / d) * f;
        const fy = (dy / d) * f;
        a.vx += fx; a.vy += fy;
        b.vx -= fx; b.vy -= fy;
      }
    }
    // springs
    for (const l of links) {
      let dx = l.t.x - l.s.x;
      let dy = l.t.y - l.s.y;
      const d = Math.sqrt(dx * dx + dy * dy) || 0.01;
      const f = (d - REST) * SPRING;
      const fx = (dx / d) * f;
      const fy = (dy / d) * f;
      l.s.vx += fx; l.s.vy += fy;
      l.t.vx -= fx; l.t.vy -= fy;
    }
    // centering + integrate
    for (const n of nodes) {
      n.vx += (cx - n.x) * CENTER;
      n.vy += (cy - n.y) * CENTER;
      n.vx *= 0.85;
      n.vy *= 0.85;
      n.x += Math.max(-15, Math.min(15, n.vx));
      n.y += Math.max(-15, Math.min(15, n.vy));
      n.x = Math.max(30, Math.min(width - 30, n.x));
      n.y = Math.max(30, Math.min(height - 40, n.y));
    }
  }
}

function enableDrag(g, node, svg, onMove) {
  let dragging = false;
  const toSvg = (evt) => {
    const pt = svg.createSVGPoint();
    pt.x = evt.clientX;
    pt.y = evt.clientY;
    const ctm = svg.getScreenCTM();
    return ctm ? pt.matrixTransform(ctm.inverse()) : { x: evt.clientX, y: evt.clientY };
  };
  g.style.cursor = 'grab';
  g.addEventListener('pointerdown', (e) => {
    dragging = true;
    g.setPointerCapture(e.pointerId);
    g.style.cursor = 'grabbing';
  });
  g.addEventListener('pointermove', (e) => {
    if (!dragging) return;
    const p = toSvg(e);
    node.x = p.x;
    node.y = p.y;
    onMove();
  });
  const stop = (e) => {
    dragging = false;
    g.style.cursor = 'grab';
    try { g.releasePointerCapture(e.pointerId); } catch (_) {}
  };
  g.addEventListener('pointerup', stop);
  g.addEventListener('pointercancel', stop);
}

function el(tag, attrs = {}) {
  const node = document.createElementNS(SVG_NS, tag);
  for (const [k, v] of Object.entries(attrs)) node.setAttribute(k, v);
  return node;
}

function markerId(color) {
  return 'arrow-' + color.replace('#', '');
}

export { NODE_STYLE, EDGE_STYLE };
