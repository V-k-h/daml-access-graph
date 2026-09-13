// src/view.js
//
// The VIEW MODEL: pure functions that turn a normalized graph JSON (the schema
// built by src/graph.js and by the backend CLIs) into the smaller, legible
// graph that actually gets drawn.
//
// Nothing here touches the DOM. That separation is deliberate: collapse,
// filtering, focus and the hidden-node accounting are the parts that decide
// WHAT a reader sees, and they are the parts worth testing. src/renderer.js
// only decides how the result is painted.
//
// The pipeline is:
//
//   raw graph  -> collapse (one node per template/interface, detail as badges)
//              -> filter   (by module, node kind, edge kind)
//              -> focus    (N-hop neighbourhood of a selection)
//              -> ViewGraph + a HiddenReport
//
// Every stage that removes something records why and how much. The tool's
// discipline is that it never shows a subset without saying so, so a stage
// that cannot explain its own omissions is a bug.

import { OPERATION_KINDS, STRUCTURAL_KINDS } from './graph.js';

/**
 * @typedef {Object} ViewNode
 * @property {string} id
 * @property {'template'|'interface'|'party'|'choice'|'key'} kind
 * @property {string} label
 * @property {string|null} module       derived (see deriveModule)
 * @property {boolean} collapsed        true if this node stands for a container
 * @property {string[]} members         raw node ids folded into this node
 * @property {Object} badges            counts summarising what was folded in
 * @property {Object} node              the underlying raw node
 *
 * @typedef {Object} ViewEdge
 * @property {string} id
 * @property {string} source
 * @property {string} target
 * @property {string} kind
 * @property {number} count             how many raw edges this aggregates
 * @property {string[]} members         raw edge ids
 * @property {boolean} via              any underlying edge was helper-attributed
 * @property {boolean} selfLoop
 *
 * @typedef {Object} ViewGraph
 * @property {ViewNode[]} nodes
 * @property {ViewEdge[]} edges
 * @property {Object} meta
 */

/** Edge kinds that describe the LIFECYCLE (what a choice does to a contract). */
export const OPERATIONAL = new Set(OPERATION_KINDS);
/** Edge kinds that describe the ACCESS STRUCTURE (who may see or authorize). */
export const STRUCTURAL = new Set(STRUCTURAL_KINDS);

/** `declares` is pure containment: it is what collapse exists to remove. */
const CONTAINMENT_KINDS = new Set(['declares']);

/**
 * The container a node belongs to: a template or an interface.
 *
 * graph.js already names template nodes `tpl:<Name>` and interface nodes
 * `iface:<Name>`, so a container id is always also a real node id when that
 * declaration was seen. Party / choice / key nodes carry `owner` + `ownerKind`
 * pointing at their declaring template or interface.
 *
 * A node with no recoverable owner is its own container rather than being
 * dropped or silently attached to something: an orphan is a fact about the
 * parse, not something to tidy away.
 *
 * @param {Object} node
 * @returns {string} container id
 */
export function containerIdOf(node) {
  if (node.kind === 'template') return `tpl:${node.label}`;
  if (node.kind === 'interface') return `iface:${node.label}`;
  const owner = node.owner || node.template || node.interface;
  if (!owner) return node.id;
  return node.ownerKind === 'interface' ? `iface:${owner}` : `tpl:${owner}`;
}

/**
 * Derive a container's module.
 *
 * NOTE: this is defensive on purpose. In real project-mode output most
 * template nodes carry NO `module` field, because graph.js can emit a template
 * as a bare placeholder (from an operation edge that targets it) before its
 * declaration is reached, and its placeholder-upgrade rule only replaces a node
 * that was marked `external: true`. An internal template referenced before it
 * is declared therefore keeps the stub, losing `module` and `meta.fields`.
 * On the canton sample that is 23 of 28 templates.
 *
 * Rather than change the shared schema, the view recovers the module from the
 * container's own choice nodes, which do carry it. If members disagree, the
 * lexicographically smallest wins and `ambiguous` is set, so the UI can say so
 * instead of picking silently.
 *
 * @param {Object|null} containerNode
 * @param {Object[]} members
 * @returns {{module: string|null, ambiguous: boolean}}
 */
export function deriveModule(containerNode, members) {
  if (containerNode && containerNode.module) {
    return { module: containerNode.module, ambiguous: false };
  }
  const seen = new Set();
  for (const m of members) if (m.module) seen.add(m.module);
  if (seen.size === 0) return { module: null, ambiguous: false };
  const sorted = [...seen].sort();
  return { module: sorted[0], ambiguous: sorted.length > 1 };
}

/**
 * Group every raw node into its container and summarise the detail.
 *
 * @param {Object} graph normalized graph JSON
 * @returns {Map<string, Object>} container id -> container record
 */
export function buildContainers(graph) {
  const byId = new Map(graph.nodes.map((n) => [n.id, n]));
  /** @type {Map<string, Object>} */
  const containers = new Map();

  const ensure = (cid, seedNode) => {
    let c = containers.get(cid);
    if (c) return c;
    const real = byId.get(cid) || null;
    c = {
      id: cid,
      // A container id that has no node of its own (possible only on a
      // malformed graph) is still rendered, tagged by what we could infer.
      kind: real ? real.kind : cid.startsWith('iface:') ? 'interface' : 'template',
      label: real ? real.label : cid.replace(/^(tpl|iface):/, ''),
      node: real,
      synthesized: !real,
      members: [],
      memberNodes: [],
      badges: {
        choices: 0,
        nonconsuming: 0,
        parties: 0,
        signatories: 0,
        observers: 0,
        controllers: 0,
        maintainers: 0,
        keyed: false,
        implements: [],
        external: !!(real && real.meta && real.meta.external),
        selfOps: {},
      },
    };
    containers.set(cid, c);
    return c;
  };

  // Containers first, so ordering of the node array cannot change the result.
  for (const n of graph.nodes) {
    if (n.kind === 'template' || n.kind === 'interface') ensure(n.id, n);
  }
  for (const n of graph.nodes) {
    const cid = containerIdOf(n);
    const c = ensure(cid, n);
    if (n.id === cid) continue; // the container's own node is not its member
    c.members.push(n.id);
    c.memberNodes.push(n);
    if (n.kind === 'choice') {
      c.badges.choices++;
      if (n.meta && n.meta.consuming === false) c.badges.nonconsuming++;
    } else if (n.kind === 'party') {
      c.badges.parties++;
    } else if (n.kind === 'key') {
      c.badges.keyed = true;
    }
  }

  for (const c of containers.values()) {
    const { module, ambiguous } = deriveModule(c.node, c.memberNodes);
    c.module = module;
    c.moduleAmbiguous = ambiguous;
  }
  return containers;
}

/**
 * Collapse (or partially expand) a graph.
 *
 * `expanded` names the containers whose detail should stay visible. The empty
 * set is the fully collapsed view (~28 nodes on the canton sample); the set of
 * every container reproduces the original graph, except that raw edges which
 * agree on (source, target, kind) are aggregated into one edge carrying
 * `count`. No edge is dropped: sum(count) always equals the raw edge total,
 * which is the conservation law the tests assert.
 *
 * @param {Object} graph
 * @param {{expanded?: Set<string>|string[], containers?: Map<string,Object>}} [options]
 * @returns {ViewGraph}
 */
export function collapseGraph(graph, options = {}) {
  const expanded = options.expanded instanceof Set
    ? options.expanded
    : new Set(options.expanded || []);
  const containers = options.containers || buildContainers(graph);
  const byId = new Map(graph.nodes.map((n) => [n.id, n]));

  const containerOfNode = new Map();
  for (const n of graph.nodes) containerOfNode.set(n.id, containerIdOf(n));

  // Which raw node id does an endpoint resolve to in this view?
  const endpointOf = (rawId) => {
    const cid = containerOfNode.get(rawId);
    if (cid === undefined) return null; // edge references a node that is absent
    return expanded.has(cid) ? rawId : cid;
  };

  /** @type {ViewNode[]} */
  const nodes = [];
  const emitted = new Set();

  for (const c of containers.values()) {
    const isExpanded = expanded.has(c.id);
    nodes.push({
      id: c.id,
      kind: c.kind,
      label: c.label,
      module: c.module,
      moduleAmbiguous: c.moduleAmbiguous,
      collapsed: !isExpanded && c.members.length > 0,
      expanded: isExpanded,
      container: c.id,
      members: isExpanded ? [] : c.members.slice(),
      badges: c.badges,
      node: c.node || { id: c.id, kind: c.kind, label: c.label },
      synthesized: c.synthesized,
    });
    emitted.add(c.id);
    if (!isExpanded) continue;
    for (const m of c.memberNodes) {
      nodes.push({
        id: m.id,
        kind: m.kind,
        label: m.label,
        module: c.module,
        moduleAmbiguous: c.moduleAmbiguous,
        collapsed: false,
        expanded: false,
        container: c.id,
        members: [],
        badges: null,
        node: m,
        synthesized: false,
      });
      emitted.add(m.id);
    }
  }

  // Aggregate edges by (resolved source, resolved target, kind).
  /** @type {Map<string, ViewEdge>} */
  const agg = new Map();
  let dangling = 0;
  let foldedContainment = 0;
  let foldedStructural = 0;
  for (const e of graph.edges) {
    const s = endpointOf(e.source);
    const t = endpointOf(e.target);
    if (s === null || t === null) { dangling++; continue; }
    const selfLoop = s === t;
    // An edge that stayed inside one collapsed node is the detail that collapse
    // exists to remove, so it is folded into a badge rather than drawn - with
    // ONE exception. An operational self-loop ("a choice of Asset creates
    // Asset") is a genuine lifecycle fact about the template, not internal
    // wiring, so it survives as a drawn self-loop. Drawing the structural ones
    // too is what produced a 184-edge "collapsed" view in the first cut: every
    // template sprouted five self-loops for its own signatories, observers,
    // controllers, key and maintainers, none of which tell the reader anything
    // the badges do not.
    if (selfLoop && !OPERATIONAL.has(e.kind)) {
      if (CONTAINMENT_KINDS.has(e.kind)) foldedContainment++;
      else foldedStructural++;
      continue;
    }
    const key = `${s} ${t} ${e.kind}`;
    let a = agg.get(key);
    if (!a) {
      a = {
        id: `v${agg.size}`,
        source: s,
        target: t,
        kind: e.kind,
        count: 0,
        members: [],
        via: false,
        selfLoop,
        group: OPERATIONAL.has(e.kind) ? 'operational' : STRUCTURAL.has(e.kind) ? 'structural' : 'other',
      };
      agg.set(key, a);
    }
    a.count++;
    a.members.push(e.id);
    if (e.meta && e.meta.via) a.via = true;
  }

  // Fold the structural detail that stayed inside a collapsed node into badges,
  // so "who signs this" survives collapse as a count rather than vanishing.
  // Counters are reset first so that collapsing twice with the same container
  // map (e.g. re-rendering after an expand) cannot double-count.
  for (const c of containers.values()) {
    c.badges.signatories = 0;
    c.badges.observers = 0;
    c.badges.controllers = 0;
    c.badges.maintainers = 0;
    c.badges.selfOps = {};
    c.badges.implements = [];
  }
  for (const e of graph.edges) {
    const sc = containerOfNode.get(e.source);
    const tc = containerOfNode.get(e.target);
    if (sc === undefined || tc === undefined || sc !== tc) continue;
    if (expanded.has(sc)) continue;
    const c = containers.get(sc);
    if (!c) continue;
    if (e.kind === 'signatory') c.badges.signatories++;
    else if (e.kind === 'observer') c.badges.observers++;
    else if (e.kind === 'controller' || e.kind === 'view-controller') c.badges.controllers++;
    else if (e.kind === 'maintainer') c.badges.maintainers++;
    else if (OPERATIONAL.has(e.kind)) {
      c.badges.selfOps[e.kind] = (c.badges.selfOps[e.kind] || 0) + 1;
    }
  }
  // `implements` is a cross-container edge, so it stays drawn; it is also
  // badged because "implements N interfaces" is a property of the template.
  for (const e of graph.edges) {
    if (e.kind !== 'implements') continue;
    const c = containers.get(containerOfNode.get(e.source));
    const tgt = byId.get(e.target);
    if (c && tgt && !c.badges.implements.includes(tgt.label)) c.badges.implements.push(tgt.label);
  }

  return {
    nodes,
    edges: [...agg.values()],
    meta: {
      ...(graph.meta || {}),
      rawNodes: graph.nodes.length,
      rawEdges: graph.edges.length,
      containers: containers.size,
      expanded: [...expanded].sort(),
      foldedContainment,
      foldedStructural,
      dangling,
    },
  };
}

/**
 * Breadth-first N-hop neighbourhood over a view graph.
 *
 * This is what answers "what can touch this template?". Direction matters for
 * that question: `in` gives the things that reach the seed (who creates,
 * exercises or fetches it), `out` gives what the seed reaches, `both` gives the
 * undirected neighbourhood.
 *
 * @param {ViewGraph} view
 * @param {string[]|Set<string>} seeds
 * @param {number} hops                 0 = seeds only; Infinity = component
 * @param {{direction?: 'in'|'out'|'both', edgeKinds?: Set<string>}} [options]
 * @returns {{ids: Set<string>, depth: Map<string, number>, frontier: string[]}}
 */
export function neighbourhood(view, seeds, hops = 1, options = {}) {
  const direction = options.direction || 'both';
  const allow = options.edgeKinds || null;
  const present = new Set(view.nodes.map((n) => n.id));
  const seedList = [...(seeds instanceof Set ? seeds : seeds || [])]
    .filter((id) => present.has(id))
    .sort();

  /** @type {Map<string, string[]>} */
  const adj = new Map();
  const link = (a, b) => {
    let l = adj.get(a);
    if (!l) { l = []; adj.set(a, l); }
    l.push(b);
  };
  for (const e of view.edges) {
    if (allow && !allow.has(e.kind)) continue;
    if (direction === 'out' || direction === 'both') link(e.source, e.target);
    if (direction === 'in' || direction === 'both') link(e.target, e.source);
  }
  // Sorted adjacency keeps traversal order independent of edge array order.
  for (const l of adj.values()) l.sort();

  const depth = new Map();
  const ids = new Set();
  let frontier = [];
  for (const s of seedList) { depth.set(s, 0); ids.add(s); frontier.push(s); }

  for (let d = 0; d < hops && frontier.length > 0; d++) {
    const next = [];
    for (const cur of frontier) {
      for (const nb of adj.get(cur) || []) {
        if (ids.has(nb)) continue;
        ids.add(nb);
        depth.set(nb, d + 1);
        next.push(nb);
      }
    }
    frontier = next.sort();
  }
  return { ids, depth, frontier };
}

/**
 * Restrict a view to a neighbourhood.
 *
 * mode `hide` removes everything outside it; mode `dim` keeps the whole graph
 * and only annotates depth, letting the renderer de-emphasise. `dim` is the
 * safer default because nothing leaves the picture.
 *
 * @param {ViewGraph} view
 * @param {{seeds?: string[], hops?: number, direction?: string, mode?: 'hide'|'dim'}} focus
 * @returns {{view: ViewGraph, depth: Map<string,number>, hiddenNodes: number, hiddenEdges: number}}
 */
export function applyFocus(view, focus = {}) {
  const seeds = focus.seeds || [];
  if (seeds.length === 0) {
    return { view, depth: new Map(), hiddenNodes: 0, hiddenEdges: 0, active: false, stale: false };
  }
  // A seed can outlive the view that produced it: select a choice node, then
  // collapse its template, and the id no longer names anything on screen.
  // Treating that as a focus with an empty neighbourhood would dim the ENTIRE
  // graph to near-invisibility with nothing to explain it, so a focus that
  // selects nothing is reported as stale and applied as no focus at all.
  const present = new Set(view.nodes.map((n) => n.id));
  if (!seeds.some((id) => present.has(id))) {
    return {
      view, depth: new Map(), hiddenNodes: 0, hiddenEdges: 0, active: false,
      stale: true, staleSeeds: [...seeds].sort(),
    };
  }
  const hops = focus.hops === undefined ? 1 : focus.hops;
  const { ids, depth } = neighbourhood(view, seeds, hops, { direction: focus.direction });
  if ((focus.mode || 'dim') === 'dim') {
    return { view, depth, hiddenNodes: 0, hiddenEdges: 0, active: true, stale: false, ids };
  }
  const nodes = view.nodes.filter((n) => ids.has(n.id));
  const edges = view.edges.filter((e) => ids.has(e.source) && ids.has(e.target));
  return {
    view: { ...view, nodes, edges },
    depth,
    ids,
    active: true,
    stale: false,
    hiddenNodes: view.nodes.length - nodes.length,
    hiddenEdges: view.edges.length - edges.length,
  };
}

/**
 * Filter a view graph.
 *
 * Node filters and edge filters are independent on purpose: the operational
 * edges (create / exercise / fetch) and the structural ones (signatory /
 * observer / controller) answer different questions, and a reader usually
 * wants one family at a time.
 *
 * Nodes are NOT dropped just because filtering isolated them. Isolation is
 * information ("nothing in the visible edge set touches this template"), so
 * hiding it is opt-in via `hideIsolated` and is counted either way.
 *
 * @param {ViewGraph} view
 * @param {Object} filters
 * @returns {{view: ViewGraph, dropped: Object}}
 */
export function applyFilters(view, filters = {}) {
  const nodeKinds = toSet(filters.nodeKinds);
  const edgeKinds = toSet(filters.edgeKinds);
  const modules = toSet(filters.modules);
  const prefix = filters.modulePrefix || '';
  const showExternal = filters.showExternal !== false;

  const dropped = {
    nodesByKind: {},
    nodesByModule: 0,
    nodesByExternal: 0,
    edgesByKind: {},
    edgesWithNodes: 0,
    isolated: 0,
  };

  const moduleOk = (n) => {
    if (modules && !modules.has(n.module === null ? '(no module)' : n.module)) return false;
    if (prefix) {
      const m = n.module || '';
      if (!m.startsWith(prefix)) return false;
    }
    return true;
  };

  const keptNodes = [];
  for (const n of view.nodes) {
    if (nodeKinds && !nodeKinds.has(n.kind)) {
      dropped.nodesByKind[n.kind] = (dropped.nodesByKind[n.kind] || 0) + 1;
      continue;
    }
    if (!showExternal && n.badges && n.badges.external) { dropped.nodesByExternal++; continue; }
    if (!moduleOk(n)) { dropped.nodesByModule++; continue; }
    keptNodes.push(n);
  }
  const keptIds = new Set(keptNodes.map((n) => n.id));

  const keptEdges = [];
  for (const e of view.edges) {
    if (edgeKinds && !edgeKinds.has(e.kind)) {
      dropped.edgesByKind[e.kind] = (dropped.edgesByKind[e.kind] || 0) + 1;
      continue;
    }
    if (!keptIds.has(e.source) || !keptIds.has(e.target)) { dropped.edgesWithNodes++; continue; }
    keptEdges.push(e);
  }

  let finalNodes = keptNodes;
  const touched = new Set();
  for (const e of keptEdges) { touched.add(e.source); touched.add(e.target); }
  const isolated = keptNodes.filter((n) => !touched.has(n.id));
  dropped.isolated = isolated.length;
  if (filters.hideIsolated) finalNodes = keptNodes.filter((n) => touched.has(n.id));

  return {
    view: { ...view, nodes: finalNodes, edges: keptEdges },
    dropped,
    isolatedIds: isolated.map((n) => n.id),
  };
}

function toSet(v) {
  if (!v) return null;
  const s = v instanceof Set ? v : new Set(v);
  return s.size === 0 ? null : s;
}

/**
 * Run the whole pipeline and produce, alongside the drawable view, a plain
 * English account of everything that is NOT on screen.
 *
 * @param {Object} graph normalized graph JSON
 * @param {Object} state {expanded, filters, focus}
 * @returns {{view: ViewGraph, containers: Map, depth: Map, hidden: Object}}
 */
export function buildView(graph, state = {}) {
  const containers = buildContainers(graph);
  const collapsed = collapseGraph(graph, { expanded: state.expanded, containers });
  const filtered = applyFilters(collapsed, state.filters);
  const focused = applyFocus(filtered.view, state.focus);

  const shownNodes = focused.view.nodes.length;
  const shownEdges = focused.view.edges.length;
  const foldedDetail = graph.nodes.length - collapsed.nodes.length;
  const rawEdgesShown = focused.view.edges.reduce((a, e) => a + e.count, 0);

  const reasons = [];
  if (foldedDetail > 0) {
    reasons.push(
      `${foldedDetail} detail node(s) folded into ${collapsed.nodes.length} template/interface node(s); ` +
      `click a node to expand it`
    );
  }
  const kindDrops = Object.entries(filtered.dropped.nodesByKind).filter(([, v]) => v > 0);
  if (kindDrops.length) {
    reasons.push(`${sum(kindDrops)} node(s) hidden by the node-kind filter (${kindDrops.map(([k, v]) => `${k}:${v}`).join(', ')})`);
  }
  if (filtered.dropped.nodesByModule > 0) {
    reasons.push(`${filtered.dropped.nodesByModule} node(s) hidden by the module filter`);
  }
  if (filtered.dropped.nodesByExternal > 0) {
    reasons.push(`${filtered.dropped.nodesByExternal} external node(s) hidden`);
  }
  const eKindDrops = Object.entries(filtered.dropped.edgesByKind).filter(([, v]) => v > 0);
  if (eKindDrops.length) {
    reasons.push(`${sum(eKindDrops)} edge group(s) hidden by the edge-kind filter (${eKindDrops.map(([k, v]) => `${k}:${v}`).join(', ')})`);
  }
  if (filtered.dropped.edgesWithNodes > 0) {
    reasons.push(`${filtered.dropped.edgesWithNodes} edge group(s) hidden because an endpoint is hidden`);
  }
  if (filtered.dropped.isolated > 0) {
    reasons.push(
      hidesIsolated(state)
        ? `${filtered.dropped.isolated} node(s) hidden because no visible edge touches them`
        : `${filtered.dropped.isolated} visible node(s) have no visible edge`
    );
  }
  if (focused.active && focused.hiddenNodes > 0) {
    reasons.push(`${focused.hiddenNodes} node(s) outside the focus neighbourhood are hidden`);
  }
  if (focused.stale) {
    reasons.push(
      `the focused node (${focused.staleSeeds.join(', ')}) is not in the current view, so the focus is not applied`
    );
  }
  if (collapsed.meta.dangling > 0) {
    reasons.push(`${collapsed.meta.dangling} edge(s) reference a node that is not in the graph`);
  }

  return {
    view: focused.view,
    containers,
    depth: focused.depth,
    focusIds: focused.ids || null,
    focusActive: !!focused.active,
    focusStale: !!focused.stale,
    hidden: {
      rawNodes: graph.nodes.length,
      rawEdges: graph.edges.length,
      shownNodes,
      shownEdges,
      rawEdgesShown,
      collapsedInto: collapsed.nodes.length,
      complete: shownNodes === graph.nodes.length && rawEdgesShown === graph.edges.length,
      reasons,
      dropped: filtered.dropped,
    },
  };
}

const sum = (pairs) => pairs.reduce((a, [, v]) => a + v, 0);
const hidesIsolated = (state) => !!(state.filters && state.filters.hideIsolated);

/**
 * What the legend should say for the graph that is ACTUALLY on screen.
 * Deriving it from the view rather than from a fixed list is the point: a
 * legend that lists edge kinds the reader cannot see is noise.
 *
 * @param {ViewGraph} view
 * @returns {{nodeKinds: string[], edgeKinds: Array<{kind: string, group: string, count: number}>}}
 */
export function legendFor(view) {
  const nodeKinds = [...new Set(view.nodes.map((n) => n.kind))].sort();
  const counts = new Map();
  for (const e of view.edges) {
    const c = counts.get(e.kind) || { kind: e.kind, group: e.group, count: 0, groups: 0 };
    c.count += e.count;
    c.groups++;
    counts.set(e.kind, c);
  }
  const edgeKinds = [...counts.values()].sort(
    (a, b) => a.group.localeCompare(b.group) || a.kind.localeCompare(b.kind)
  );
  return { nodeKinds, edgeKinds };
}

/**
 * All modules present in a graph, with how many containers each holds.
 * `(no module)` is a real bucket, not a silent omission.
 *
 * @param {Object} graph
 * @returns {Array<{module: string, count: number}>}
 */
export function modulesOf(graph) {
  const containers = buildContainers(graph);
  const counts = new Map();
  for (const c of containers.values()) {
    const key = c.module === null ? '(no module)' : c.module;
    counts.set(key, (counts.get(key) || 0) + 1);
  }
  return [...counts.entries()]
    .map(([module, count]) => ({ module, count }))
    .sort((a, b) => a.module.localeCompare(b.module));
}

/**
 * All edge kinds present in a graph, grouped.
 * @param {Object} graph
 */
export function edgeKindsOf(graph) {
  const counts = new Map();
  for (const e of graph.edges) counts.set(e.kind, (counts.get(e.kind) || 0) + 1);
  return [...counts.entries()]
    .map(([kind, count]) => ({
      kind,
      count,
      group: OPERATIONAL.has(kind) ? 'operational' : STRUCTURAL.has(kind) ? 'structural' : 'other',
    }))
    .sort((a, b) => a.group.localeCompare(b.group) || a.kind.localeCompare(b.kind));
}

/**
 * Greedy label decluttering.
 *
 * At 200 nodes most labels overlap, and overlapping labels are worse than no
 * labels: they are unreadable AND they hide the marks. Labels are granted in
 * priority order (degree first, then id so the result is deterministic) and a
 * label is refused if its box intersects one already granted.
 *
 * Text is measured by character count rather than by a DOM call so that this
 * stays pure and testable; the estimate only needs to be in the right ballpark
 * because the padding absorbs the error.
 *
 * @param {Array<{id: string, x: number, y: number, label: string, priority?: number}>} placed
 * @param {{charWidth?: number, lineHeight?: number, padX?: number, padY?: number, max?: number}} [options]
 * @returns {Set<string>} ids whose label should be drawn
 */
export function declutterLabels(placed, options = {}) {
  const charWidth = options.charWidth === undefined ? 5.6 : options.charWidth;
  const lineHeight = options.lineHeight === undefined ? 12 : options.lineHeight;
  const padX = options.padX === undefined ? 2 : options.padX;
  const padY = options.padY === undefined ? 2 : options.padY;
  const max = options.max === undefined ? Infinity : options.max;

  const boxes = placed.map((p) => {
    const w = String(p.label || '').length * charWidth + padX * 2;
    const h = lineHeight + padY * 2;
    return {
      id: p.id,
      priority: p.priority || 0,
      x0: p.x - w / 2, x1: p.x + w / 2,
      y0: p.y - h / 2, y1: p.y + h / 2,
    };
  });
  boxes.sort((a, b) => b.priority - a.priority || (a.id < b.id ? -1 : a.id > b.id ? 1 : 0));

  const accepted = [];
  const visible = new Set();
  for (const b of boxes) {
    if (visible.size >= max) break;
    let clash = false;
    for (const a of accepted) {
      if (b.x0 < a.x1 && b.x1 > a.x0 && b.y0 < a.y1 && b.y1 > a.y0) { clash = true; break; }
    }
    if (clash) continue;
    accepted.push(b);
    visible.add(b.id);
  }
  return visible;
}

/**
 * Assign a curvature offset to each edge so that parallel edges between the
 * same pair of nodes are individually visible instead of drawing on top of one
 * another. Offsets fan out symmetrically: 0, +1, -1, +2, -2, ...
 *
 * Edges in the opposite direction between the same pair share the bundle, so
 * A->B and B->A separate too.
 *
 * @param {ViewEdge[]} edges
 * @returns {Map<string, number>} edge id -> curvature rank
 */
export function bundleEdges(edges) {
  /** @type {Map<string, string[]>} */
  const bundles = new Map();
  for (const e of edges) {
    const key = e.source < e.target ? `${e.source} ${e.target}` : `${e.target} ${e.source}`;
    let b = bundles.get(key);
    if (!b) { b = []; bundles.set(key, b); }
    b.push(e);
  }
  const rank = new Map();
  for (const b of bundles.values()) {
    const sorted = [...b].sort((x, y) => (x.kind < y.kind ? -1 : x.kind > y.kind ? 1 : x.id < y.id ? -1 : 1));
    sorted.forEach((e, i) => {
      // 0, +1, -1, +2, -2, ...
      const step = Math.ceil(i / 2);
      const sign = i % 2 === 1 ? 1 : -1;
      rank.set(e.id, i === 0 ? 0 : sign * step);
    });
  }
  return rank;
}
