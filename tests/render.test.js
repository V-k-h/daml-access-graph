// tests/render.test.js
//
//   node --test
//
// Tests for the VIEW MODEL and the LAYOUT - the pure half of the visualizer.
//
// The renderer needs a DOM, so it is not exercised here. Everything that
// decides what a reader sees (collapse, filtering, focus, hidden accounting)
// and where it lands (layout) is a pure function over the normalized graph
// JSON, and that is what these tests cover. If a behaviour can only be tested
// by looking at pixels, it has been put in the wrong module.

import test from 'node:test';
import assert from 'node:assert/strict';

import { parseDaml } from '../src/parser.js';
import { parseProject } from '../src/project.js';
import { buildGraph } from '../src/graph.js';
import {
  containerIdOf,
  deriveModule,
  buildContainers,
  collapseGraph,
  neighbourhood,
  applyFocus,
  applyFilters,
  buildView,
  legendFor,
  modulesOf,
  edgeKindsOf,
  declutterLabels,
  bundleEdges,
  OPERATIONAL,
  STRUCTURAL,
} from '../src/view.js';
import { forceLayout, layeredLayout, layoutGraph, fitToViewport, BH_THRESHOLD } from '../src/layout.js';
// badgeText / boxSize are the only pure functions in the renderer: they format
// the collapse summary, which is logic, not painting. They import cleanly in
// node because renderer.js touches the DOM only inside renderGraph.
import { badgeText, boxSize } from '../src/renderer.js';

// ------------------------------------------------------------------ fixtures

const SRC = `module Shop where

template Asset
  with
    issuer : Party
    owner : Party
  where
    signatory issuer
    observer owner
    key (issuer, owner) : (Party, Party)
    maintainer issuer

    choice Give : ContractId Asset
      with newOwner : Party
      controller owner
      do create this with owner = newOwner

    nonconsuming choice Peek : ()
      controller issuer
      do return ()

template Proposal
  with
    from : Party
    to : Party
  where
    signatory from
    observer to

    choice Accept : ContractId Asset
      controller to
      do
        create Asset with issuer = from, owner = to

    choice Reject : ()
      controller to
      do return ()
`;

const graph = () => buildGraph(parseDaml(SRC));

/** A two-module project, so module-derived behaviour has something to chew on. */
const projectGraph = () =>
  buildGraph(
    parseProject([
      {
        path: 'A.daml',
        source: `module Alpha where
template Coin
  with owner : Party
  where
    signatory owner
    choice Burn : ()
      controller owner
      do return ()
`,
      },
      {
        path: 'B.daml',
        source: `module Beta where
import Alpha
template Mint
  with minter : Party
  where
    signatory minter
    choice Go : ContractId Coin
      controller minter
      do create Coin with owner = minter
`,
      },
    ]),
    { source: 'project-source' }
  );

// ------------------------------------------------------------- containers

test('view: every node maps to exactly one container, and templates are their own', () => {
  const g = graph();
  const containers = buildContainers(g);
  assert.equal(containers.size, 2, 'Asset and Proposal');
  assert.ok(containers.has('tpl:Asset'));
  assert.ok(containers.has('tpl:Proposal'));

  // Conservation: containers + their members account for every raw node once.
  const claimed = new Set();
  for (const c of containers.values()) {
    claimed.add(c.id);
    for (const m of c.members) {
      assert.ok(!claimed.has(m), `${m} claimed twice`);
      claimed.add(m);
    }
  }
  assert.equal(claimed.size, g.nodes.length);
});

test('view: containerIdOf routes by ownerKind, and an orphan is its own container', () => {
  assert.equal(containerIdOf({ kind: 'template', label: 'T' }), 'tpl:T');
  assert.equal(containerIdOf({ kind: 'interface', label: 'I' }), 'iface:I');
  assert.equal(
    containerIdOf({ kind: 'choice', label: 'C', owner: 'I', ownerKind: 'interface' }),
    'iface:I'
  );
  assert.equal(
    containerIdOf({ kind: 'party', label: 'p', owner: 'T', ownerKind: 'template' }),
    'tpl:T'
  );
  // No owner at all: the node stands alone rather than being attached to
  // something arbitrary or dropped.
  assert.equal(containerIdOf({ id: 'party:x', kind: 'party', label: 'x' }), 'party:x');
});

test('view: badges carry the folded detail as counts', () => {
  const c = buildContainers(graph()).get('tpl:Asset');
  assert.equal(c.badges.choices, 2);
  assert.equal(c.badges.nonconsuming, 1);
  assert.equal(c.badges.keyed, true);
  assert.ok(c.badges.parties >= 2);
});

test('view: a module missing from the container node is recovered from its choices', () => {
  // graph.js can emit a template as a placeholder before its declaration is
  // reached, which loses `module`. The view must not lose the module with it.
  assert.deepEqual(deriveModule({ module: 'Mine' }, [{ module: 'Other' }]), {
    module: 'Mine',
    ambiguous: false,
  });
  assert.deepEqual(deriveModule({}, [{ module: 'Recovered' }, { module: 'Recovered' }]), {
    module: 'Recovered',
    ambiguous: false,
  });
  // Disagreement is reported, not silently resolved.
  assert.deepEqual(deriveModule({}, [{ module: 'B' }, { module: 'A' }]), {
    module: 'A',
    ambiguous: true,
  });
  assert.deepEqual(deriveModule({}, []), { module: null, ambiguous: false });
});

test('view: project-mode modules are derived for every container', () => {
  const g = projectGraph();
  const mods = modulesOf(g);
  const names = mods.map((m) => m.module);
  assert.ok(names.includes('Alpha'), `got ${names.join(',')}`);
  assert.ok(names.includes('Beta'), `got ${names.join(',')}`);
  // Every container is accounted for by exactly one bucket, including the
  // explicit "(no module)" one.
  const total = mods.reduce((a, m) => a + m.count, 0);
  assert.equal(total, buildContainers(g).size);
});

// ---------------------------------------------------------------- collapse

test('collapse: the default view is one node per template, detail folded away', () => {
  const g = graph();
  const v = collapseGraph(g);
  assert.equal(v.nodes.length, 2);
  assert.ok(v.nodes.every((n) => n.kind === 'template'));
  assert.ok(v.nodes.every((n) => n.collapsed));
  assert.ok(v.nodes.length < g.nodes.length);
});

test('collapse: no edge is lost - sum(count) plus folded equals the raw total', () => {
  const g = graph();
  const v = collapseGraph(g);
  const drawn = v.edges.reduce((a, e) => a + e.count, 0);
  const folded = v.meta.foldedContainment + v.meta.foldedStructural;
  assert.equal(drawn + folded + v.meta.dangling, g.edges.length);
});

test('collapse: structural self-edges become badges, operational ones stay drawn', () => {
  const g = graph();
  const v = collapseGraph(g);
  // Asset.Give creates Asset: a real lifecycle fact, so it survives as a loop.
  const loop = v.edges.find((e) => e.selfLoop && e.source === 'tpl:Asset');
  assert.ok(loop, 'expected a self-loop for Asset creating Asset');
  assert.equal(loop.kind, 'create');
  // But no signatory/observer/controller self-loop is drawn.
  assert.equal(v.edges.filter((e) => e.selfLoop && STRUCTURAL.has(e.kind)).length, 0);
  const asset = v.nodes.find((n) => n.id === 'tpl:Asset');
  assert.ok(asset.badges.signatories >= 1);
  assert.ok(asset.badges.controllers >= 2);
});

test('collapse: expanding a container reveals its members and its internal edges', () => {
  const g = graph();
  const v = collapseGraph(g, { expanded: ['tpl:Asset'] });
  const ids = new Set(v.nodes.map((n) => n.id));
  assert.ok(ids.has('choice:Asset.Give'));
  assert.ok(ids.has('tpl:Asset'));
  // Proposal stays folded.
  assert.ok(!ids.has('choice:Proposal.Accept'));
  assert.ok(v.nodes.find((n) => n.id === 'tpl:Asset').expanded);
  assert.ok(v.nodes.find((n) => n.id === 'tpl:Proposal').collapsed);
  // The `declares` edge is now between two visible nodes, so it is drawn.
  assert.ok(v.edges.some((e) => e.kind === 'declares' && e.target === 'choice:Asset.Give'));
});

test('collapse: expanding everything recovers the whole graph, losing nothing', () => {
  const g = graph();
  const all = [...buildContainers(g).keys()];
  const v = collapseGraph(g, { expanded: all });
  assert.equal(v.nodes.length, g.nodes.length);
  assert.equal(v.edges.reduce((a, e) => a + e.count, 0), g.edges.length);
  assert.equal(v.meta.foldedContainment + v.meta.foldedStructural, 0);
});

test('collapse: cross-container edges aggregate by (source, target, kind)', () => {
  const g = graph();
  const v = collapseGraph(g);
  const created = v.edges.filter((e) => e.source === 'tpl:Proposal' && e.target === 'tpl:Asset');
  assert.equal(created.length, 1, 'one drawn edge per kind between a pair');
  assert.equal(created[0].kind, 'create');
  assert.equal(created[0].group, 'operational');
  assert.ok(created[0].members.length >= 1);
});

test('collapse: collapsing twice with the same container map does not double-count badges', () => {
  const g = graph();
  const containers = buildContainers(g);
  const a = collapseGraph(g, { containers });
  const first = a.nodes.find((n) => n.id === 'tpl:Asset').badges.signatories;
  collapseGraph(g, { containers });
  const b = collapseGraph(g, { containers });
  assert.equal(b.nodes.find((n) => n.id === 'tpl:Asset').badges.signatories, first);
});

// ----------------------------------------------------------- neighbourhood

test('neighbourhood: hop 0 is the seed, and depth grows by one per ring', () => {
  const v = collapseGraph(graph(), { expanded: [...buildContainers(graph()).keys()] });
  const n0 = neighbourhood(v, ['tpl:Asset'], 0);
  assert.deepEqual([...n0.ids], ['tpl:Asset']);
  assert.equal(n0.depth.get('tpl:Asset'), 0);

  const n1 = neighbourhood(v, ['tpl:Asset'], 1);
  assert.ok(n1.ids.size > 1);
  for (const id of n1.ids) assert.ok(n1.depth.get(id) <= 1);

  const n2 = neighbourhood(v, ['tpl:Asset'], 2);
  assert.ok(n2.ids.size >= n1.ids.size);
  for (const id of n1.ids) assert.ok(n2.ids.has(id), 'a wider hop never loses a closer node');
});

test('neighbourhood: direction answers "what can touch this" separately from "what it touches"', () => {
  const v = collapseGraph(graph());
  // Proposal -create-> Asset is the only cross edge.
  const into = neighbourhood(v, ['tpl:Asset'], 1, { direction: 'in' });
  assert.ok(into.ids.has('tpl:Proposal'), 'Proposal reaches Asset');

  const outOf = neighbourhood(v, ['tpl:Asset'], 1, { direction: 'out' });
  assert.ok(!outOf.ids.has('tpl:Proposal'), 'Asset does not reach Proposal');

  const both = neighbourhood(v, ['tpl:Asset'], 1, { direction: 'both' });
  assert.ok(both.ids.has('tpl:Proposal'));
});

test('neighbourhood: an edge-kind restriction changes who is reachable', () => {
  const v = collapseGraph(graph());
  const viaOps = neighbourhood(v, ['tpl:Asset'], 1, { direction: 'in', edgeKinds: OPERATIONAL });
  assert.ok(viaOps.ids.has('tpl:Proposal'));
  const viaStructural = neighbourhood(v, ['tpl:Asset'], 1, { direction: 'in', edgeKinds: STRUCTURAL });
  assert.ok(!viaStructural.ids.has('tpl:Proposal'));
});

test('neighbourhood: unknown seeds are ignored, not crashed on', () => {
  const v = collapseGraph(graph());
  const r = neighbourhood(v, ['tpl:Nope'], 2);
  assert.equal(r.ids.size, 0);
});

test('neighbourhood: result is independent of node and edge array order', () => {
  const g = graph();
  const v1 = collapseGraph(g);
  const v2 = { ...v1, nodes: [...v1.nodes].reverse(), edges: [...v1.edges].reverse() };
  const a = neighbourhood(v1, ['tpl:Asset'], 2);
  const b = neighbourhood(v2, ['tpl:Asset'], 2);
  assert.deepEqual([...a.ids].sort(), [...b.ids].sort());
  for (const id of a.ids) assert.equal(a.depth.get(id), b.depth.get(id));
});

test('focus: dim keeps the whole graph, hide removes the outside and counts it', () => {
  const g = graph();
  const v = collapseGraph(g, { expanded: [...buildContainers(g).keys()] });

  const dim = applyFocus(v, { seeds: ['tpl:Asset'], hops: 1, mode: 'dim' });
  assert.equal(dim.view.nodes.length, v.nodes.length, 'dim hides nothing');
  assert.equal(dim.hiddenNodes, 0);
  assert.ok(dim.depth.size > 0);

  const hide = applyFocus(v, { seeds: ['tpl:Asset'], hops: 1, mode: 'hide' });
  assert.ok(hide.view.nodes.length < v.nodes.length);
  assert.equal(hide.hiddenNodes, v.nodes.length - hide.view.nodes.length);
  // Every surviving edge has both endpoints present.
  const ids = new Set(hide.view.nodes.map((n) => n.id));
  for (const e of hide.view.edges) {
    assert.ok(ids.has(e.source) && ids.has(e.target));
  }
});

test('focus: a seed that is not in the view is reported stale, not applied', () => {
  // Select a choice while its template is expanded, then collapse it: the id
  // still sits in the view state but names nothing on screen. Applying it as a
  // normal focus would give an empty neighbourhood and dim the whole graph to
  // nothing, which looks like a broken render rather than a stale selection.
  const g = graph();
  const collapsed = collapseGraph(g);
  const r = applyFocus(collapsed, { seeds: ['choice:Asset.Give'], hops: 1, mode: 'dim' });
  assert.equal(r.active, false);
  assert.equal(r.stale, true);
  assert.deepEqual(r.staleSeeds, ['choice:Asset.Give']);
  assert.equal(r.depth.size, 0, 'nothing is dimmed');
  assert.equal(r.view.nodes.length, collapsed.nodes.length, 'nothing is hidden either');

  // and buildView says so out loud
  const built = buildView(g, { focus: { seeds: ['choice:Asset.Give'], hops: 1, mode: 'dim' } });
  assert.equal(built.focusStale, true);
  assert.match(built.hidden.reasons.join(' '), /not in the current view/);
});

test('focus: a partially stale seed set still focuses on the seeds that exist', () => {
  const g = graph();
  const collapsed = collapseGraph(g);
  const r = applyFocus(collapsed, { seeds: ['tpl:Asset', 'choice:Gone.Nope'], hops: 1, mode: 'dim' });
  assert.equal(r.active, true);
  assert.equal(r.stale, false);
  assert.equal(r.depth.get('tpl:Asset'), 0);
});

test('focus: no seed is not a filter', () => {
  const v = collapseGraph(graph());
  const r = applyFocus(v, { seeds: [], hops: 1, mode: 'hide' });
  assert.equal(r.active, false);
  assert.equal(r.view.nodes.length, v.nodes.length);
});

// --------------------------------------------------------------- filtering

test('filter: edge kinds and node kinds are independent', () => {
  const g = graph();
  const v = collapseGraph(g, { expanded: [...buildContainers(g).keys()] });

  const opsOnly = applyFilters(v, { edgeKinds: OPERATIONAL });
  assert.ok(opsOnly.view.edges.every((e) => OPERATIONAL.has(e.kind)));
  assert.equal(opsOnly.view.nodes.length, v.nodes.length, 'an edge filter does not remove nodes');
  assert.ok(Object.values(opsOnly.dropped.edgesByKind).reduce((a, b) => a + b, 0) > 0);

  const noParties = applyFilters(v, { nodeKinds: new Set(['template', 'choice']) });
  assert.ok(noParties.view.nodes.every((n) => n.kind === 'template' || n.kind === 'choice'));
  assert.ok(noParties.dropped.nodesByKind.party > 0);
  // Edges to a removed node are removed too, and counted separately.
  assert.ok(noParties.dropped.edgesWithNodes > 0);
});

test('filter: a module filter keeps only that module, and reports the rest', () => {
  const g = projectGraph();
  const v = collapseGraph(g);
  const onlyAlpha = applyFilters(v, { modules: new Set(['Alpha']) });
  assert.ok(onlyAlpha.view.nodes.length > 0);
  assert.ok(onlyAlpha.view.nodes.every((n) => n.module === 'Alpha'));
  assert.ok(onlyAlpha.dropped.nodesByModule > 0);
});

test('filter: a module PREFIX matches dotted module names', () => {
  const v = {
    nodes: [
      { id: 'a', kind: 'template', label: 'A', module: 'Calc.Perb', badges: null },
      { id: 'b', kind: 'template', label: 'B', module: 'Calc.Wf', badges: null },
      { id: 'c', kind: 'template', label: 'C', module: 'Other', badges: null },
    ],
    edges: [],
    meta: {},
  };
  const r = applyFilters(v, { modulePrefix: 'Calc.' });
  assert.deepEqual(r.view.nodes.map((n) => n.id), ['a', 'b']);
  assert.equal(r.dropped.nodesByModule, 1);
});

test('filter: isolation is reported but only removed when asked', () => {
  const v = {
    nodes: [
      { id: 'a', kind: 'template', label: 'A', module: null, badges: null },
      { id: 'b', kind: 'template', label: 'B', module: null, badges: null },
      { id: 'lonely', kind: 'template', label: 'L', module: null, badges: null },
    ],
    edges: [{ id: 'e0', source: 'a', target: 'b', kind: 'create', count: 1, members: ['x'], group: 'operational' }],
    meta: {},
  };
  const kept = applyFilters(v, {});
  assert.equal(kept.view.nodes.length, 3, 'isolation alone never hides a node');
  assert.equal(kept.dropped.isolated, 1);
  assert.deepEqual(kept.isolatedIds, ['lonely']);

  const hidden = applyFilters(v, { hideIsolated: true });
  assert.equal(hidden.view.nodes.length, 2);
  assert.equal(hidden.dropped.isolated, 1);
});

test('filter: an empty or absent filter set means "everything"', () => {
  const v = collapseGraph(graph());
  const a = applyFilters(v, {});
  const b = applyFilters(v, { edgeKinds: new Set(), nodeKinds: [] });
  assert.equal(a.view.nodes.length, v.nodes.length);
  assert.equal(b.view.nodes.length, v.nodes.length);
  assert.equal(b.view.edges.length, v.edges.length);
});

// ----------------------------------------------------- the hidden report

test('report: a complete view says so, and any omission is explained', () => {
  const g = graph();
  const all = [...buildContainers(g).keys()];

  const full = buildView(g, { expanded: all });
  assert.equal(full.hidden.complete, true);
  assert.deepEqual(full.hidden.reasons, []);
  assert.equal(full.hidden.rawEdgesShown, g.edges.length);

  const collapsed = buildView(g, {});
  assert.equal(collapsed.hidden.complete, false);
  assert.ok(collapsed.hidden.reasons.length > 0);
  assert.match(collapsed.hidden.reasons[0], /folded into/);
  assert.equal(collapsed.hidden.rawNodes, g.nodes.length);
});

test('report: every removing stage contributes a reason', () => {
  const g = graph();
  const all = [...buildContainers(g).keys()];
  const r = buildView(g, {
    expanded: all,
    filters: { nodeKinds: new Set(['template']), edgeKinds: OPERATIONAL },
    focus: { seeds: ['tpl:Asset'], hops: 0, mode: 'hide' },
  });
  const joined = r.hidden.reasons.join(' | ');
  assert.match(joined, /node-kind filter/);
  assert.match(joined, /edge-kind filter/);
  assert.match(joined, /focus neighbourhood/);
  assert.equal(r.hidden.complete, false);
});

test('report: the node and edge totals always refer to the raw graph', () => {
  const g = graph();
  for (const state of [{}, { expanded: ['tpl:Asset'] }, { filters: { edgeKinds: STRUCTURAL } }]) {
    const r = buildView(g, state);
    assert.equal(r.hidden.rawNodes, g.nodes.length);
    assert.equal(r.hidden.rawEdges, g.edges.length);
    assert.ok(r.hidden.rawEdgesShown <= g.edges.length);
  }
});

// ------------------------------------------------------------------ legend

test('legend: describes only what is on screen', () => {
  const g = graph();
  const collapsed = buildView(g, {});
  const l = legendFor(collapsed.view);
  assert.deepEqual(l.nodeKinds, ['template'], 'no party/choice swatch in a collapsed view');
  assert.ok(l.edgeKinds.every((e) => collapsed.view.edges.some((x) => x.kind === e.kind)));

  const ops = buildView(g, { filters: { edgeKinds: OPERATIONAL } });
  assert.ok(legendFor(ops.view).edgeKinds.every((e) => OPERATIONAL.has(e.kind)));
});

test('legend: edge counts are the raw counts, not the drawn ones', () => {
  const g = graph();
  const v = buildView(g, {}).view;
  const l = legendFor(v);
  for (const e of l.edgeKinds) {
    const raw = v.edges.filter((x) => x.kind === e.kind).reduce((a, x) => a + x.count, 0);
    assert.equal(e.count, raw);
  }
});

test('edgeKindsOf groups every kind as structural, operational or other', () => {
  const g = graph();
  for (const { kind, group } of edgeKindsOf(g)) {
    if (OPERATIONAL.has(kind)) assert.equal(group, 'operational');
    else if (STRUCTURAL.has(kind)) assert.equal(group, 'structural');
    else assert.equal(group, 'other');
  }
});

// ------------------------------------------------------------ readability

test('declutter: overlapping labels are refused, highest priority wins', () => {
  const placed = [
    { id: 'a', x: 0, y: 0, label: 'AAAAAAAA', priority: 1 },
    { id: 'b', x: 2, y: 0, label: 'BBBBBBBB', priority: 9 },
    { id: 'c', x: 400, y: 400, label: 'CCCCCCCC', priority: 0 },
  ];
  const vis = declutterLabels(placed);
  assert.ok(vis.has('b'), 'the higher priority label survives');
  assert.ok(!vis.has('a'), 'the colliding lower-priority one is dropped');
  assert.ok(vis.has('c'), 'a distant label is unaffected');
});

test('declutter: is deterministic and ties break by id', () => {
  const placed = [
    { id: 'zz', x: 0, y: 0, label: 'XXXX', priority: 5 },
    { id: 'aa', x: 1, y: 0, label: 'XXXX', priority: 5 },
  ];
  const a = declutterLabels(placed);
  const b = declutterLabels([...placed].reverse());
  assert.deepEqual([...a].sort(), [...b].sort());
  assert.ok(a.has('aa'), 'the id-smallest wins the tie');
  assert.equal(a.size, 1);
});

test('declutter: nothing overlaps when everything is far apart', () => {
  const placed = Array.from({ length: 10 }, (_, i) => ({ id: `n${i}`, x: i * 200, y: 0, label: 'ab' }));
  assert.equal(declutterLabels(placed).size, 10);
});

test('bundle: parallel edges between a pair get distinct curvature', () => {
  const edges = [
    { id: 'e0', source: 'a', target: 'b', kind: 'create' },
    { id: 'e1', source: 'a', target: 'b', kind: 'exercise' },
    { id: 'e2', source: 'b', target: 'a', kind: 'fetch' },
    { id: 'e3', source: 'c', target: 'd', kind: 'create' },
  ];
  const rank = bundleEdges(edges);
  const ab = [rank.get('e0'), rank.get('e1'), rank.get('e2')];
  assert.equal(new Set(ab).size, 3, 'three edges in the a-b bundle, three offsets');
  assert.equal(rank.get('e3'), 0, 'a lone edge stays straight');
  // Reverse-direction edges share the bundle, so they cannot coincide.
  assert.notEqual(rank.get('e0'), rank.get('e2'));
});

test('bundle: is deterministic under input reordering', () => {
  const edges = [
    { id: 'e0', source: 'a', target: 'b', kind: 'create' },
    { id: 'e1', source: 'a', target: 'b', kind: 'exercise' },
    { id: 'e2', source: 'a', target: 'b', kind: 'archive' },
  ];
  const a = bundleEdges(edges);
  const b = bundleEdges([...edges].reverse());
  for (const e of edges) assert.equal(a.get(e.id), b.get(e.id));
});

// ------------------------------------------------------------------ layout

const bigView = () => {
  // A synthetic graph wide enough that Barnes-Hut, not the exact path, runs.
  const nodes = [];
  const edges = [];
  for (let i = 0; i < 80; i++) {
    nodes.push({
      id: `tpl:T${String(i).padStart(3, '0')}`,
      kind: 'template',
      label: `T${i}`,
      module: `M${i % 7}`,
      badges: null,
    });
  }
  for (let i = 0; i < 79; i++) {
    edges.push({
      id: `e${i}`,
      source: nodes[i].id,
      target: nodes[(i * 7 + 3) % 80].id,
      kind: 'create',
      count: 1,
      members: [`r${i}`],
      group: 'operational',
      selfLoop: false,
    });
  }
  return { nodes, edges, meta: {} };
};

/** A graph of arbitrary size, for exercising the Barnes-Hut path. */
const wideView = (n) => {
  const nodes = [];
  const edges = [];
  for (let i = 0; i < n; i++) {
    nodes.push({
      id: `tpl:W${String(i).padStart(5, '0')}`,
      kind: 'template',
      label: `W${i}`,
      module: `M${i % 9}`,
      badges: null,
    });
  }
  for (let i = 0; i < n; i++) {
    edges.push({
      id: `e${i}`,
      source: nodes[i].id,
      target: nodes[(i * 7 + 3) % n].id,
      kind: 'create',
      count: 1,
      members: [`r${i}`],
      group: 'operational',
      selfLoop: false,
    });
  }
  return { nodes, edges, meta: {} };
};

test('layout: force is deterministic - identical input, identical output', () => {
  const v = bigView();
  const a = forceLayout(v, { width: 900, height: 600 });
  const b = forceLayout(v, { width: 900, height: 600 });
  assert.deepEqual([...a.positions.entries()], [...b.positions.entries()]);
});

test('layout: force is invariant under permutation of the node and edge arrays', () => {
  const v = bigView();
  const shuffled = {
    ...v,
    nodes: [...v.nodes].reverse(),
    edges: [...v.edges].reverse(),
  };
  const a = forceLayout(v, { width: 900, height: 600 });
  const b = forceLayout(shuffled, { width: 900, height: 600 });
  assert.equal(a.positions.size, b.positions.size);
  for (const [id, p] of a.positions) {
    assert.deepEqual(p, b.positions.get(id), `node ${id} moved when the input was reordered`);
  }
});

test('layout: force uses the exact sum up to the measured Barnes-Hut threshold', () => {
  // The threshold is empirical (see the table in layout.js): Barnes-Hut only
  // pays for its per-iteration tree build on graphs far larger than a typical
  // repository, so the 200-node case must NOT silently take the slower path.
  assert.equal(forceLayout(bigView(), {}).mode, 'force-exact');
  assert.ok(BH_THRESHOLD >= 200, 'a 200-node repository graph uses the exact sum');

  const huge = wideView(BH_THRESHOLD + 10);
  assert.equal(forceLayout(huge, { iterations: 2 }).mode, 'force-bh');

  // The option overrides the heuristic in both directions.
  assert.equal(forceLayout(huge, { iterations: 2, exact: true }).mode, 'force-exact');
  assert.equal(forceLayout(bigView(), { iterations: 2, exact: false }).mode, 'force-bh');
});

test('layout: both repulsion paths agree on the broad shape', () => {
  // They are two implementations of the same force, so a node should not land
  // in a different region depending on which one ran.
  const v = bigView();
  const a = forceLayout(v, { width: 1000, height: 700, exact: true });
  const b = forceLayout(v, { width: 1000, height: 700, exact: false });
  let far = 0;
  for (const [id, p] of a.positions) {
    if (Math.hypot(p.x - b.positions.get(id).x, p.y - b.positions.get(id).y) > 180) far++;
  }
  assert.ok(far < v.nodes.length * 0.25, `${far} nodes disagree between the two paths`);
});

test('layout: force separates nodes rather than piling them up', () => {
  const v = bigView();
  const { positions } = forceLayout(v, { width: 1000, height: 700 });
  const pts = [...positions.values()];
  // No two nodes coincide, and the drawing has real extent in both axes.
  const seen = new Set(pts.map((p) => `${Math.round(p.x)},${Math.round(p.y)}`));
  assert.ok(seen.size > pts.length * 0.9, 'nodes are not stacked on each other');
  const xs = pts.map((p) => p.x);
  const ys = pts.map((p) => p.y);
  assert.ok(Math.max(...xs) - Math.min(...xs) > 200);
  assert.ok(Math.max(...ys) - Math.min(...ys) > 200);
  assert.ok(pts.every((p) => Number.isFinite(p.x) && Number.isFinite(p.y)));
});

test('layout: module clustering puts a module closer to itself than to the whole', () => {
  const v = bigView();
  const { positions } = forceLayout(v, { width: 1000, height: 700, clusterPull: 0.09 });
  const centroid = (ids) => {
    let x = 0, y = 0;
    for (const id of ids) { x += positions.get(id).x; y += positions.get(id).y; }
    return { x: x / ids.length, y: y / ids.length };
  };
  const spread = (ids) => {
    const c = centroid(ids);
    let s = 0;
    for (const id of ids) {
      const p = positions.get(id);
      s += Math.hypot(p.x - c.x, p.y - c.y);
    }
    return s / ids.length;
  };
  const all = v.nodes.map((n) => n.id);
  const m0 = v.nodes.filter((n) => n.module === 'M0').map((n) => n.id);
  assert.ok(spread(m0) < spread(all), 'a module is tighter than the whole drawing');
});

test('layout: layered assigns layers along the operational edges', () => {
  const v = {
    nodes: ['a', 'b', 'c'].map((id) => ({ id, kind: 'template', label: id, module: null, badges: null })),
    edges: [
      { id: 'e0', source: 'a', target: 'b', kind: 'create', count: 1, group: 'operational', selfLoop: false },
      { id: 'e1', source: 'b', target: 'c', kind: 'create', count: 1, group: 'operational', selfLoop: false },
    ],
    meta: {},
  };
  const r = layeredLayout(v, { width: 900, height: 600 });
  assert.equal(r.layers.length, 3);
  assert.deepEqual(r.layers, [['a'], ['b'], ['c']]);
  // Layers advance left to right, so "what creates what" is a direction.
  assert.ok(r.positions.get('a').x < r.positions.get('b').x);
  assert.ok(r.positions.get('b').x < r.positions.get('c').x);
});

test('layout: layered terminates on a cycle and reports the back edge', () => {
  const v = {
    nodes: ['a', 'b', 'c'].map((id) => ({ id, kind: 'template', label: id, module: null, badges: null })),
    edges: [
      { id: 'e0', source: 'a', target: 'b', kind: 'create', count: 1, group: 'operational', selfLoop: false },
      { id: 'e1', source: 'b', target: 'c', kind: 'exercise', count: 1, group: 'operational', selfLoop: false },
      { id: 'e2', source: 'c', target: 'a', kind: 'archive', count: 1, group: 'operational', selfLoop: false },
    ],
    meta: {},
  };
  const r = layeredLayout(v, { width: 900, height: 600 });
  assert.equal(r.positions.size, 3);
  assert.equal(r.backEdges.length, 1, 'exactly one edge broken to make a DAG');
  assert.ok(r.layers.flat().length === 3, 'every node still gets a layer');
});

test('layout: layered is deterministic and permutation-stable', () => {
  const v = bigView();
  const a = layeredLayout(v, { width: 900, height: 600 });
  const b = layeredLayout({ ...v, nodes: [...v.nodes].reverse(), edges: [...v.edges].reverse() }, { width: 900, height: 600 });
  for (const [id, p] of a.positions) assert.deepEqual(p, b.positions.get(id), `node ${id}`);
  assert.deepEqual(a.layers, b.layers);
});

test('layout: a wide layer wraps into sub-columns instead of a 2000px column', () => {
  // One source fanning out to 40 targets: without wrapping, layer 1 is a single
  // column far taller than any viewport.
  const nodes = [{ id: 'src', kind: 'template', label: 'src', module: null, badges: null }];
  const edges = [];
  for (let i = 0; i < 40; i++) {
    const id = `t${String(i).padStart(2, '0')}`;
    nodes.push({ id, kind: 'template', label: id, module: null, badges: null });
    edges.push({ id: `e${i}`, source: 'src', target: id, kind: 'create', count: 1, group: 'operational', selfLoop: false });
  }
  const r = layeredLayout({ nodes, edges, meta: {} }, { width: 1200, height: 700 });
  const ys = [...r.positions.values()].map((p) => p.y);
  assert.ok(Math.max(...ys) - Math.min(...ys) < 700, 'the drawing fits the viewport height');
  const xs = new Set([...r.positions.values()].map((p) => p.x));
  assert.ok(xs.size > 2, 'the wide layer was split across sub-columns');
});

test('layout: layered falls back to all edges when no lifecycle edge is shown', () => {
  const v = {
    nodes: ['a', 'b'].map((id) => ({ id, kind: 'template', label: id, module: null, badges: null })),
    edges: [
      { id: 'e0', source: 'a', target: 'b', kind: 'implements', count: 1, group: 'structural', selfLoop: false },
    ],
    meta: {},
  };
  const r = layeredLayout(v, { width: 800, height: 600 });
  assert.equal(r.layers.length, 2, 'structural edges still give a direction to follow');
});

test('layout: layoutGraph picks layered for a collapsed lifecycle and force for detail', () => {
  const g = graph();
  const collapsed = buildView(g, {}).view;
  assert.equal(layoutGraph(collapsed, { width: 900, height: 600 }).mode, 'layered');

  const expanded = buildView(g, { expanded: [...buildContainers(g).keys()] }).view;
  assert.ok(layoutGraph(expanded, { width: 900, height: 600 }).mode.startsWith('force'));

  // An explicit mode always wins over the heuristic.
  assert.equal(layoutGraph(collapsed, { mode: 'force' }).mode.startsWith('force'), true);
  assert.equal(layoutGraph(expanded, { mode: 'layered' }).mode, 'layered');
});

test('layout: handles the degenerate cases without throwing', () => {
  const empty = { nodes: [], edges: [], meta: {} };
  assert.equal(forceLayout(empty, {}).positions.size, 0);
  assert.equal(layeredLayout(empty, {}).positions.size, 0);
  assert.equal(layoutGraph(empty, {}).positions.size, 0);

  const one = { nodes: [{ id: 'a', kind: 'template', label: 'a', module: null, badges: null }], edges: [], meta: {} };
  const p = forceLayout(one, { width: 800, height: 600 }).positions.get('a');
  assert.ok(Number.isFinite(p.x) && Number.isFinite(p.y));

  // Edges naming absent nodes must not produce NaN positions.
  const dangling = {
    nodes: [{ id: 'a', kind: 'template', label: 'a', module: null, badges: null }],
    edges: [{ id: 'e', source: 'a', target: 'ghost', kind: 'create', count: 1, group: 'operational', selfLoop: false }],
    meta: {},
  };
  const q = forceLayout(dangling, {}).positions.get('a');
  assert.ok(Number.isFinite(q.x) && Number.isFinite(q.y));
});

test('layout: fitToViewport scales the drawing into the frame', () => {
  const positions = new Map([
    ['a', { x: 0, y: 0 }],
    ['b', { x: 4000, y: 3000 }],
  ]);
  const fit = fitToViewport(positions, 800, 600, 40);
  assert.ok(fit.scale > 0 && fit.scale < 1);
  for (const p of positions.values()) {
    const x = p.x * fit.scale + fit.tx;
    const y = p.y * fit.scale + fit.ty;
    assert.ok(x >= 0 && x <= 800, `x ${x} inside the frame`);
    assert.ok(y >= 0 && y <= 600, `y ${y} inside the frame`);
  }
  assert.deepEqual(fitToViewport(new Map(), 800, 600), { scale: 1, tx: 0, ty: 0 });
});

// ------------------------------------------------- end-to-end on a project

test('buildView: the whole pipeline composes, and collapse really shrinks it', () => {
  const g = projectGraph();
  const collapsed = buildView(g, {});
  assert.ok(collapsed.view.nodes.length < g.nodes.length);
  assert.ok(collapsed.view.nodes.every((n) => n.kind === 'template' || n.kind === 'interface'));

  // Focusing on one template in the collapsed view keeps it and its neighbours.
  const focused = buildView(g, {
    focus: { seeds: ['tpl:Coin'], hops: 1, direction: 'in', mode: 'hide' },
  });
  assert.ok(focused.view.nodes.some((n) => n.id === 'tpl:Coin'));
  assert.ok(focused.hidden.reasons.some((r) => /focus neighbourhood/.test(r)) ||
    focused.view.nodes.length === collapsed.view.nodes.length);
});

test('buildView: layout consumes the view without any further massaging', () => {
  const g = projectGraph();
  const r = buildView(g, {});
  const lay = layoutGraph(r.view, { width: 900, height: 600 });
  assert.equal(lay.positions.size, r.view.nodes.length);
  for (const n of r.view.nodes) assert.ok(lay.positions.has(n.id), `no position for ${n.id}`);
});

// ----------------------------------------------------------------- at scale

/**
 * A graph shaped like the real repository samples: ~28 templates, each with
 * choices, party fields and a key, cross-linked by create/exercise edges.
 * The committed samples (canton: 198 nodes / 371 edges) are not part of this
 * repo, so this stands in for them as a portable regression guard.
 */
function repositoryScaleGraph(templates = 28) {
  const nodes = [];
  const edges = [];
  let e = 0;
  const edge = (source, target, kind) =>
    edges.push({ id: `e${e++}`, source, target, kind, label: kind });
  for (let i = 0; i < templates; i++) {
    const name = `T${String(i).padStart(2, '0')}`;
    const mod = `Mod.Group${i % 6}`;
    nodes.push({ id: `tpl:${name}`, kind: 'template', label: name, module: mod, meta: { external: false } });
    for (const p of ['issuer', 'owner']) {
      nodes.push({ id: `party:${name}.${p}`, kind: 'party', label: p, template: name, owner: name, ownerKind: 'template' });
    }
    edge(`tpl:${name}`, `party:${name}.issuer`, 'signatory');
    edge(`tpl:${name}`, `party:${name}.owner`, 'observer');
    nodes.push({ id: `key:${name}`, kind: 'key', label: `key ${name}`, template: name, owner: name, ownerKind: 'template', meta: { maintainers: ['issuer'] } });
    edge(`tpl:${name}`, `key:${name}`, 'keyed-by');
    edge(`key:${name}`, `party:${name}.issuer`, 'maintainer');
    for (let c = 0; c < 3; c++) {
      const cid = `choice:${name}.C${c}`;
      nodes.push({ id: cid, kind: 'choice', label: `C${c}`, template: name, owner: name, ownerKind: 'template', module: mod, meta: { consuming: c !== 2 } });
      edge(`tpl:${name}`, cid, 'declares');
      edge(cid, `party:${name}.owner`, 'controller');
      edge(cid, `tpl:T${String((i * 7 + c + 1) % templates).padStart(2, '0')}`, c === 0 ? 'create' : c === 1 ? 'exercise' : 'lookupAllByKey');
    }
  }
  return { meta: { source: 'test', modules: ['Mod'], warnings: [] }, nodes, edges };
}

test('scale: a repository-sized graph collapses to something a reader can hold', () => {
  const g = repositoryScaleGraph(28);
  assert.ok(g.nodes.length > 150 && g.edges.length > 300,
    `fixture is repository-sized: ${g.nodes.length} nodes / ${g.edges.length} edges`);

  const collapsed = buildView(g, {});
  assert.equal(collapsed.view.nodes.length, 28, 'one node per template');
  assert.ok(collapsed.view.edges.length < 90, 'and an edge count in the same order');
  // The shrink is the whole point: >5x fewer nodes than the hairball.
  assert.ok(g.nodes.length / collapsed.view.nodes.length > 5);
  // ...and it is honest about it.
  assert.equal(collapsed.hidden.complete, false);
  assert.equal(collapsed.hidden.rawNodes, g.nodes.length);
  assert.match(collapsed.hidden.reasons.join(' '), /folded into 28/);
});

test('scale: the whole interaction round stays well inside a frame budget', () => {
  const g = repositoryScaleGraph(28);
  const all = [...buildContainers(g).keys()];
  const round = (state) => {
    const t0 = Date.now();
    const r = buildView(g, state);
    layoutGraph(r.view, { width: 1400, height: 820 });
    return Date.now() - t0;
  };
  // Warm, then take the best of a few - this is a floor check, not a benchmark.
  round({});
  const collapsedMs = Math.min(round({}), round({}), round({}));
  const expandedMs = Math.min(...[1, 2, 3].map(() => round({ expanded: all })));

  // Generous ceilings: the point is to catch an accidental return to a
  // quadratic-with-no-annealing layout, not to police a few milliseconds.
  assert.ok(collapsedMs < 120, `collapsed round took ${collapsedMs}ms`);
  assert.ok(expandedMs < 600, `expanded round took ${expandedMs}ms`);
});

test('scale: focus narrows a repository graph to a readable neighbourhood', () => {
  const g = repositoryScaleGraph(28);
  const collapsed = buildView(g, {});
  const seed = collapsed.view.nodes[0].id;

  const hidden = buildView(g, { focus: { seeds: [seed], hops: 1, direction: 'in', mode: 'hide' } });
  assert.ok(hidden.view.nodes.length < collapsed.view.nodes.length,
    'focusing shows fewer nodes than the whole collapsed graph');
  assert.ok(hidden.view.nodes.some((n) => n.id === seed), 'the seed survives');
  assert.match(hidden.hidden.reasons.join(' '), /focus neighbourhood/);

  // Every drawn node really is within one hop of the seed, in the right
  // direction: this is the "what can touch this template?" answer.
  const reachable = neighbourhood(collapsed.view, [seed], 1, { direction: 'in' });
  for (const n of hidden.view.nodes) assert.ok(reachable.ids.has(n.id), `${n.id} is not a 1-hop in-neighbour`);
});

test('scale: every drawn node gets a finite position and every edge two endpoints', () => {
  const g = repositoryScaleGraph(28);
  for (const state of [{}, { expanded: [...buildContainers(g).keys()] }]) {
    const r = buildView(g, state);
    const lay = layoutGraph(r.view, { width: 1400, height: 820 });
    const ids = new Set(r.view.nodes.map((n) => n.id));
    assert.equal(lay.positions.size, r.view.nodes.length);
    for (const p of lay.positions.values()) {
      assert.ok(Number.isFinite(p.x) && Number.isFinite(p.y));
    }
    for (const e of r.view.edges) {
      assert.ok(ids.has(e.source) && ids.has(e.target), `dangling view edge ${e.id}`);
      assert.ok(e.count >= 1 && e.members.length === e.count);
    }
  }
});


// ------------------------------------------------- the collapse summary

test('badges: the badge row states what collapse folded away', () => {
  const asset = collapseGraph(graph()).nodes.find((n) => n.id === 'tpl:Asset');
  const text = badgeText(asset);
  // 2 choices, one of them nonconsuming, party fields, a contract key.
  assert.match(text, /2ch\(1nc\)/);
  assert.match(text, /\bkey\b/);
  assert.match(text, /\d+p\b/);
  // The self-create that stayed drawn is also summarised.
  assert.match(text, /createx1/);
});

test('badges: an empty summary is empty, not a row of zeroes', () => {
  assert.equal(badgeText({ badges: null }), '');
  assert.equal(
    badgeText({
      badges: {
        choices: 0, nonconsuming: 0, parties: 0, signatories: 0, observers: 0,
        controllers: 0, maintainers: 0, keyed: false, implements: [], external: false, selfOps: {},
      },
    }),
    ''
  );
});

test('badges: a box is wide enough for its own label', () => {
  const short = boxSize({ label: 'Io', badges: null });
  const long = boxSize({ label: 'BorrowingBaseLoanDetails', badges: null });
  assert.ok(long.w > short.w, 'a longer name gets a wider box');
  assert.ok(long.w > 'BorrowingBaseLoanDetails'.length * 6, 'and the text actually fits');
  // A badge row makes the box taller, so the two lines cannot overlap.
  const withBadges = boxSize({ label: 'Io', badges: { choices: 2, parties: 0, keyed: false, implements: [], selfOps: {} } });
  assert.ok(withBadges.h > short.h);
});
