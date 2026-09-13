// src/renderer.js
//
// The DRAWING layer, and only the drawing layer.
//
// Everything that decides WHAT is on screen lives in src/view.js (collapse,
// filter, focus, hidden accounting) and src/layout.js (positions). Those are
// pure and tested in node without a DOM. This file turns their output into
// SVG and wires up interaction. If you find yourself deciding what a reader
// should see in here, it belongs in view.js instead.

import { buildView, legendFor, declutterLabels, bundleEdges } from './view.js';
import { layoutGraph, fitToViewport } from './layout.js';

const SVG_NS = 'http://www.w3.org/2000/svg';

const NODE_STYLE = {
  template: { r: 26, fill: '#2563eb', stroke: '#1e3a8a' },
  party: { r: 18, fill: '#16a34a', stroke: '#14532d' },
  choice: { r: 20, fill: '#d97706', stroke: '#7c2d12' },
  interface: { r: 24, fill: '#9333ea', stroke: '#581c87' },
  key: { r: 14, fill: '#0f766e', stroke: '#134e4a' },
};

const EDGE_STYLE = {
  declares: { color: '#94a3b8', dash: '0' },
  signatory: { color: '#dc2626', dash: '0' },
  observer: { color: '#0891b2', dash: '4 3' },
  controller: { color: '#d97706', dash: '0' },
  'view-controller': { color: '#9333ea', dash: '5 2' },
  implements: { color: '#9333ea', dash: '0' },
  'keyed-by': { color: '#0f766e', dash: '0' },
  maintainer: { color: '#0f766e', dash: '3 2' },
  create: { color: '#16a34a', dash: '0' },
  createAndExercise: { color: '#16a34a', dash: '2 2' },
  exercise: { color: '#7c3aed', dash: '0' },
  exerciseByKey: { color: '#7c3aed', dash: '2 2' },
  fetch: { color: '#64748b', dash: '4 3' },
  fetchByKey: { color: '#64748b', dash: '4 3' },
  lookupByKey: { color: '#64748b', dash: '1 3' },
  lookupAllByKey: { color: '#0f766e', dash: '1 3' },
  archive: { color: '#334155', dash: '6 3' },
};

const styleOf = (kind) => EDGE_STYLE[kind] || EDGE_STYLE.declares;

// A collapsed container is drawn as a labelled BOX rather than a circle. The
// shape change is the signal that the node stands for more than itself: a box
// has room for the badge row, and a reader can tell at a glance which nodes
// still have detail folded inside them.
const BOX_H = 30;
const BADGE_H = 13;
const CHAR_W = 6.6;

function boxSize(node) {
  const w = Math.max(84, String(node.label).length * CHAR_W + 26);
  const h = BOX_H + (hasBadges(node) ? BADGE_H : 0);
  return { w, h };
}

function hasBadges(node) {
  const b = node.badges;
  if (!b) return false;
  return b.choices > 0 || b.parties > 0 || b.keyed || b.implements.length > 0 ||
    Object.keys(b.selfOps).length > 0;
}

/**
 * The badge row: the detail that collapse folded away, as counts.
 * Deliberately terse - this is a density-limited surface, and the tooltip
 * carries the long form.
 */
function badgeText(node) {
  const b = node.badges;
  if (!b) return '';
  const parts = [];
  if (b.choices) parts.push(`${b.choices}ch${b.nonconsuming ? `(${b.nonconsuming}nc)` : ''}`);
  if (b.parties) parts.push(`${b.parties}p`);
  if (b.signatories) parts.push(`${b.signatories}sig`);
  if (b.observers) parts.push(`${b.observers}obs`);
  if (b.keyed) parts.push('key');
  if (b.implements.length) parts.push(`impl:${b.implements.length}`);
  const self = Object.entries(b.selfOps).sort();
  if (self.length) parts.push(self.map(([k, v]) => `${k}x${v}`).join(' '));
  return parts.join(' ');
}

function nodeTooltip(node) {
  const raw = node.node || {};
  const lines = [];
  if (node.collapsed) {
    lines.push(`${node.kind} ${node.label}  [collapsed - click to expand]`);
  } else {
    lines.push(`${node.kind} ${node.label}`);
  }
  if (node.module) lines.push(`module ${node.module}${node.moduleAmbiguous ? ' (members disagree; smallest shown)' : ''}`);
  else if (node.kind === 'template' || node.kind === 'interface') lines.push('module (not recorded in the graph)');
  const b = node.badges;
  if (b) {
    if (b.external) lines.push('external (declared outside this project)');
    if (b.choices) lines.push(`${b.choices} choice(s), ${b.nonconsuming} nonconsuming`);
    if (b.parties) lines.push(`${b.parties} party field/reference(s)`);
    if (b.signatories) lines.push(`${b.signatories} signatory edge(s)`);
    if (b.observers) lines.push(`${b.observers} observer edge(s)`);
    if (b.controllers) lines.push(`${b.controllers} controller edge(s)`);
    if (b.keyed) lines.push(`contract key, ${b.maintainers} maintainer(s)`);
    if (b.implements.length) lines.push(`implements ${b.implements.join(', ')}`);
    for (const [k, v] of Object.entries(b.selfOps).sort()) lines.push(`${v} self ${k}`);
  }
  if (raw.kind === 'choice') {
    lines.push(raw.meta && raw.meta.consuming === false ? 'nonconsuming' : 'consuming');
  }
  if (raw.kind === 'party') {
    if (raw.meta && raw.meta.fromArg) lines.push('from a choice argument');
    else if (raw.meta && raw.meta.derived) lines.push('projected expression');
  }
  if (raw.kind === 'key' && raw.meta) {
    lines.push(`key ${raw.meta.expr || ''} : ${raw.meta.type || ''}`);
  }
  return lines.join('\n');
}

function edgeTooltip(e, labelOf) {
  const head = `${labelOf(e.source)} -${e.kind}-> ${labelOf(e.target)}`;
  const bits = [head];
  if (e.count > 1) bits.push(`${e.count} underlying edge(s) aggregated`);
  if (e.via) bits.push('at least one attributed through a helper function (meta.via)');
  if (e.selfLoop) bits.push('self-referential: a choice of this template targets it');
  return bits.join('\n');
}

/**
 * Render a normalized graph into an SVG element.
 *
 * @param {SVGSVGElement} svg
 * @param {Object} graph normalized graph JSON
 * @param {Object} [state] {expanded, filters, focus, layout}
 * @param {Object} [callbacks] {onSelect, onToggleExpand, onRendered}
 * @returns {Object} render info (hidden report, legend, timings)
 */
export function renderGraph(svg, graph, state = {}, callbacks = {}) {
  const t0 = now();
  while (svg.firstChild) svg.removeChild(svg.firstChild);

  const width = svg.clientWidth || 1000;
  const height = svg.clientHeight || 700;

  const built = buildView(graph, state);
  const view = built.view;
  const tView = now();

  const layout = layoutGraph(view, {
    width,
    height,
    mode: state.layout || 'auto',
  });
  const tLayout = now();

  const pos = layout.positions;
  const byId = new Map(view.nodes.map((n) => [n.id, n]));
  const labelOf = (id) => (byId.get(id) ? byId.get(id).label : id);

  const fit = fitToViewport(pos, width, height, 70);
  const root = el('g', { class: 'viewport' });
  root.setAttribute('transform', `translate(${fit.tx},${fit.ty}) scale(${fit.scale})`);

  // Arrow markers, one per colour actually used.
  const defs = document.createElementNS(SVG_NS, 'defs');
  const colors = new Set(view.edges.map((e) => styleOf(e.kind).color));
  for (const c of colors) {
    const marker = el('marker', {
      id: markerId(c),
      viewBox: '0 0 10 10',
      refX: '9',
      refY: '5',
      markerWidth: '6',
      markerHeight: '6',
      orient: 'auto-start-reverse',
    });
    marker.appendChild(el('path', { d: 'M 0 0 L 10 5 L 0 10 z', fill: c }));
    defs.appendChild(marker);
  }
  svg.appendChild(defs);
  svg.appendChild(root);

  const linkLayer = el('g', { class: 'links' });
  const nodeLayer = el('g', { class: 'nodes' });
  const labelLayer = el('g', { class: 'labels' });
  root.appendChild(linkLayer);
  root.appendChild(nodeLayer);
  root.appendChild(labelLayer);

  // --- focus de-emphasis -------------------------------------------------
  // Depth 0 is the selection, 1..N its neighbourhood, and anything with no
  // depth is outside it. Opacity, not removal, is the default: the reader can
  // still see that there is more graph, which is the honest presentation.
  const depth = built.depth;
  const focusActive = built.focusActive;
  const opacityFor = (id) => {
    if (!focusActive) return 1;
    if (!depth.has(id)) return 0.07;
    const d = depth.get(id);
    return d === 0 ? 1 : Math.max(0.3, 1 - d * 0.28);
  };

  // --- edges -------------------------------------------------------------
  const curve = bundleEdges(view.edges.filter((e) => !e.selfLoop));
  for (const e of view.edges) {
    const s = pos.get(e.source);
    const t = pos.get(e.target);
    if (!s || !t) continue;
    const style = styleOf(e.kind);
    const eo = Math.min(opacityFor(e.source), opacityFor(e.target));
    const path = el('path', {
      fill: 'none',
      stroke: style.color,
      'stroke-width': String(Math.min(4, 1.3 + Math.log2(e.count + 1) * 0.7)),
      'stroke-dasharray': e.via ? '5 3' : style.dash,
      'marker-end': `url(#${markerId(style.color)})`,
      class: `link link-${e.kind} link-${e.group}`,
      opacity: String(eo),
    });
    const geom = e.selfLoop
      ? { d: selfLoopPath(byId.get(e.source), s), mid: null }
      : edgePath(byId.get(e.source), byId.get(e.target), s, t, curve.get(e.id) || 0);
    path.setAttribute('d', geom.d);
    const title = el('title');
    title.textContent = edgeTooltip(e, labelOf);
    path.appendChild(title);
    linkLayer.appendChild(path);

    // Aggregated edges carry the count inline: "3x" next to a create edge is
    // how the reader learns three different choices create that template.
    if (e.count > 1 && geom.mid && eo > 0.2) {
      const tag = el('text', {
        x: String(r(geom.mid.x)), y: String(r(geom.mid.y - 4)),
        'text-anchor': 'middle',
        class: 'edge-count',
        fill: style.color,
        opacity: String(eo),
      });
      tag.textContent = `${e.count}x`;
      linkLayer.appendChild(tag);
    }
  }

  // --- nodes -------------------------------------------------------------
  const drawn = [];
  for (const n of view.nodes) {
    const p = pos.get(n.id);
    if (!p) continue;
    const style = NODE_STYLE[n.kind] || NODE_STYLE.template;
    const isContainer = n.kind === 'template' || n.kind === 'interface';
    const g = el('g', {
      class: `node node-${n.kind}${n.collapsed ? ' node-collapsed' : ''}${n.expanded ? ' node-expanded' : ''}`,
      'data-id': n.id,
      transform: `translate(${p.x},${p.y})`,
      opacity: String(opacityFor(n.id)),
      tabindex: '0',
      role: 'button',
      'aria-label': ariaLabel(n),
    });

    const external = n.badges ? n.badges.external : !!(n.node.meta && n.node.meta.external);
    const nonconsuming = n.kind === 'choice' && n.node.meta && n.node.meta.consuming === false;
    const derivedParty = n.kind === 'party' && n.node.meta && (n.node.meta.derived || n.node.meta.fromArg);
    const selected = state.focus && (state.focus.seeds || []).includes(n.id);

    if (isContainer) {
      const { w, h } = boxSize(n);
      g.appendChild(el('rect', {
        x: String(-w / 2), y: String(-h / 2), width: String(w), height: String(h),
        rx: n.kind === 'interface' ? String(h / 2) : '6',
        fill: external ? '#1f2937' : style.fill,
        stroke: selected ? '#fbbf24' : style.stroke,
        'stroke-width': selected ? '3' : external ? '1.5' : '2',
        'stroke-dasharray': external ? '4 2' : '0',
        class: 'node-shape',
      }));
      const nameY = hasBadges(n) ? -h / 2 + 14 : 4;
      const name = el('text', { 'text-anchor': 'middle', y: String(nameY), class: 'node-name' });
      name.textContent = n.label;
      g.appendChild(name);
      if (hasBadges(n)) {
        const badge = el('text', { 'text-anchor': 'middle', y: String(-h / 2 + 27), class: 'node-badge' });
        badge.textContent = badgeText(n);
        g.appendChild(badge);
      }
      // A small caret marks a node that still has detail folded inside it.
      if (n.collapsed) {
        g.appendChild(el('path', {
          d: `M ${w / 2 - 11} ${-h / 2 + 4} l 7 0 l -3.5 5 z`,
          fill: '#e2e8f0', opacity: '0.85', class: 'node-caret',
        }));
      }
    } else {
      g.appendChild(el('circle', {
        r: String(style.r),
        fill: style.fill,
        stroke: selected ? '#fbbf24' : style.stroke,
        'stroke-width': selected ? '3' : '2',
        'stroke-dasharray': nonconsuming || derivedParty ? '3 2' : '0',
        class: 'node-shape',
      }));
      drawn.push({ n, p, style });
    }

    const title = el('title');
    title.textContent = nodeTooltip(n);
    g.appendChild(title);
    nodeLayer.appendChild(g);

    wireNode(g, n, svg, callbacks);
  }

  // --- detail-node labels, decluttered -----------------------------------
  // Container boxes carry their own label inside the shape, so only the
  // circles need external labels - and at density those are what collide.
  const degree = new Map();
  for (const e of view.edges) {
    degree.set(e.source, (degree.get(e.source) || 0) + e.count);
    degree.set(e.target, (degree.get(e.target) || 0) + e.count);
  }
  const candidates = drawn.map(({ n, p, style }) => ({
    id: n.id,
    x: p.x,
    y: p.y + style.r + 11,
    label: n.label,
    // Highest degree wins the space, and a focused node always keeps its label.
    priority: (focusActive && depth.has(n.id) ? 10000 - depth.get(n.id) * 100 : 0) + (degree.get(n.id) || 0),
  }));
  const visibleLabels = declutterLabels(candidates, {
    charWidth: 5.6 / Math.max(0.35, fit.scale),
    lineHeight: 12 / Math.max(0.35, fit.scale),
  });
  for (const c of candidates) {
    if (!visibleLabels.has(c.id)) continue;
    const t = el('text', {
      x: String(c.x), y: String(c.y),
      'text-anchor': 'middle',
      class: 'node-label',
      opacity: String(opacityFor(c.id)),
    });
    t.textContent = c.label;
    labelLayer.appendChild(t);
  }

  const info = {
    hidden: built.hidden,
    legend: legendFor(view),
    view,
    containers: built.containers,
    layout: { mode: layout.mode, ms: layout.ms, layers: layout.layers ? layout.layers.length : 0 },
    labelsShown: visibleLabels.size,
    labelsTotal: candidates.length,
    timing: {
      viewMs: tView - t0,
      layoutMs: tLayout - tView,
      drawMs: now() - tLayout,
      totalMs: now() - t0,
    },
  };
  if (callbacks.onRendered) callbacks.onRendered(info);
  return info;
}

function ariaLabel(n) {
  const bits = [`${n.kind} ${n.label}`];
  if (n.collapsed) bits.push(`collapsed, ${n.members.length} hidden detail nodes, press Enter to expand`);
  else if (n.expanded) bits.push('expanded, press Enter to collapse');
  if (n.module) bits.push(`module ${n.module}`);
  return bits.join(', ');
}

/**
 * Quadratic-Bezier edge, clipped to both node boundaries so the arrowhead
 * lands on the edge of the shape rather than under it.
 *
 * `rank` fans parallel edges apart. Two templates joined by both `create` and
 * `exercise` were previously drawn as one line with two arrowheads on top of
 * each other, which is exactly the kind of silent loss this tool should not do.
 */
function edgePath(sNode, tNode, s, t, rank) {
  const dx = t.x - s.x;
  const dy = t.y - s.y;
  const len = Math.sqrt(dx * dx + dy * dy) || 1;
  // Control point offset perpendicular to the chord.
  const off = rank * Math.min(38, 14 + len * 0.06);
  const mx = (s.x + t.x) / 2 - (dy / len) * off;
  const my = (s.y + t.y) / 2 + (dx / len) * off;
  const a = boundary(sNode, s, mx, my);
  const b = boundary(tNode, t, mx, my);
  return {
    d: `M ${r(a.x)} ${r(a.y)} Q ${r(mx)} ${r(my)} ${r(b.x)} ${r(b.y)}`,
    // The point at t = 0.5 on the quadratic, which is where a label belongs.
    // Using the straight-chord midpoint instead would drift the "3x" tag off
    // its own curve exactly where curvature is largest, i.e. on the bundles
    // that need labelling most.
    mid: { x: 0.25 * a.x + 0.5 * mx + 0.25 * b.x, y: 0.25 * a.y + 0.5 * my + 0.25 * b.y },
  };
}

/** A loop that leaves and re-enters the top of the node. */
function selfLoopPath(node, p) {
  const { w, h } = node && (node.kind === 'template' || node.kind === 'interface')
    ? boxSize(node)
    : { w: 40, h: 40 };
  const x = p.x + w / 4;
  const y = p.y - h / 2;
  const R = 17;
  return `M ${r(x - R * 0.6)} ${r(y)} C ${r(x - R)} ${r(y - R * 1.9)} ${r(x + R)} ${r(y - R * 1.9)} ${r(x + R * 0.35)} ${r(y - 1)}`;
}

/** Where the segment from (towardX, towardY) meets the node's outline. */
function boundary(node, p, towardX, towardY) {
  let dx = towardX - p.x;
  let dy = towardY - p.y;
  const len = Math.sqrt(dx * dx + dy * dy);
  if (len < 0.001) return { x: p.x, y: p.y };
  dx /= len; dy /= len;
  if (node && (node.kind === 'template' || node.kind === 'interface')) {
    const { w, h } = boxSize(node);
    // Scale the unit direction until it exits the half-extent box.
    const sx = dx === 0 ? Infinity : (w / 2 + 3) / Math.abs(dx);
    const sy = dy === 0 ? Infinity : (h / 2 + 3) / Math.abs(dy);
    const k = Math.min(sx, sy);
    return { x: p.x + dx * k, y: p.y + dy * k };
  }
  const rr = (NODE_STYLE[node ? node.kind : 'template'] || NODE_STYLE.template).r + 3;
  return { x: p.x + dx * rr, y: p.y + dy * rr };
}

/**
 * Pointer and keyboard interaction for one node.
 *
 * Click selects (drives focus). Enter/Space toggles expand/collapse, and so
 * does a double click. Every node is in the tab order with a visible focus
 * ring (see styles.css), so the graph is navigable without a mouse.
 */
function wireNode(g, n, svg, callbacks) {
  g.style.cursor = 'pointer';
  let moved = false;
  let dragging = false;

  const toSvg = (evt) => {
    const pt = svg.createSVGPoint();
    pt.x = evt.clientX;
    pt.y = evt.clientY;
    const ctm = svg.getScreenCTM();
    return ctm ? pt.matrixTransform(ctm.inverse()) : { x: 0, y: 0 };
  };
  let start = null;
  let base = { x: 0, y: 0 };

  g.addEventListener('pointerdown', (e) => {
    if (e.button !== 0) return;
    dragging = true;
    moved = false;
    start = toSvg(e);
    const m = /translate\(([-\d.]+),([-\d.]+)\)/.exec(g.getAttribute('transform') || '');
    base = m ? { x: parseFloat(m[1]), y: parseFloat(m[2]) } : { x: 0, y: 0 };
    g.setPointerCapture(e.pointerId);
  });
  g.addEventListener('pointermove', (e) => {
    if (!dragging || !start) return;
    const p = toSvg(e);
    const dx = p.x - start.x;
    const dy = p.y - start.y;
    if (Math.abs(dx) + Math.abs(dy) > 3) moved = true;
    if (!moved) return;
    // Dragging nudges the drawn node only. Positions come from a pure layout
    // function, so a drag is presentation, not state: re-rendering restores
    // the deterministic layout rather than preserving an ad-hoc arrangement.
    g.setAttribute('transform', `translate(${base.x + dx},${base.y + dy})`);
  });
  const stop = (e) => {
    if (!dragging) return;
    dragging = false;
    try { g.releasePointerCapture(e.pointerId); } catch (_) { /* not captured */ }
    if (!moved && callbacks.onSelect) callbacks.onSelect(n.id, n);
  };
  g.addEventListener('pointerup', stop);
  g.addEventListener('pointercancel', stop);

  g.addEventListener('dblclick', (e) => {
    e.preventDefault();
    if (callbacks.onToggleExpand) callbacks.onToggleExpand(n.container || n.id, n);
  });
  g.addEventListener('keydown', (e) => {
    if (e.key === 'Enter' || e.key === ' ') {
      e.preventDefault();
      if (callbacks.onToggleExpand) callbacks.onToggleExpand(n.container || n.id, n);
    } else if (e.key === 'f' || e.key === 'F') {
      e.preventDefault();
      if (callbacks.onSelect) callbacks.onSelect(n.id, n);
    }
  });
}

function el(tag, attrs = {}) {
  const node = document.createElementNS(SVG_NS, tag);
  for (const [k, v] of Object.entries(attrs)) node.setAttribute(k, v);
  return node;
}

const markerId = (color) => 'arrow-' + color.replace('#', '');
const r = (v) => Math.round(v * 100) / 100;
const now = () =>
  (typeof performance !== 'undefined' && performance.now ? performance.now() : Date.now());

export { NODE_STYLE, EDGE_STYLE, badgeText, boxSize };
