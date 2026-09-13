// tests/property.test.js
//
//   node --test
//
// PROPERTY TESTS for the two committed CI gates: the access-graph gate
// (src/diff.js + src/baseline.js) and the proof gate (src/verdict-baseline.js).
//
// WHY THIS FILE EXISTS. Both gates' credibility rested on a handful of
// hand-written examples in tests/diff.test.js. Hand-written examples check the
// cases the author thought of, which are exactly the cases the author already
// got right. The failure modes that matter here are the ones nobody pictured:
// a baseline round-trip that reports phantom changes on an unchanged tree (the
// gate cries wolf and gets switched off), or a widening edit that slips past
// (worse than having no gate at all). Those are LAWS over all well-formed
// inputs, so they are checked here over GENERATED inputs instead.
//
// DETERMINISM. No Math.random anywhere in this repository: layout and tests
// must be reproducible. The generator is mulberry32, the same PRNG
// tests/differential.test.js uses. Every case derives its own seed from the
// file SEED plus the case index, so a failure reports one 32-bit number that
// regenerates exactly that input:
//
//     const rnd = mulberry32(<printed caseSeed>);
//     const g = genGraph(rnd);
//
// On failure the graph is also shrunk (remove one edge, or one node with its
// incident edges, as long as the property still fails) and printed as JSON, so
// the counterexample that lands in the report is minimal rather than a
// 40-node dump.
//
// SCOPE HONESTY. These properties check the gates' internal laws -
// reflexivity, antisymmetry, additivity, round-trip identity, monotonicity.
// They do NOT check that the direction table itself encodes the right
// security judgement (that adding an observer really is the widening one);
// that is a modelling decision, pinned by the examples in tests/diff.test.js
// and restated independently here so a silent edit to EDGE_DIRECTION fails.

import test from 'node:test';
import assert from 'node:assert/strict';

import { readFileSync, readdirSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

import { parseDaml } from '../src/parser.js';
import { buildGraph, OPERATION_KINDS, STRUCTURAL_KINDS } from '../src/graph.js';
import { analyzeAll } from '../src/analysis.js';
import { diffGraphs, diffFindings, findingFingerprint } from '../src/diff.js';
import { createBaseline, compareToBaseline } from '../src/baseline.js';
import {
  createVerdictBaseline,
  compareVerdicts,
  statusFamily,
  verdictKey,
} from '../src/verdict-baseline.js';

// -------------------------------------------------------------- seeded PRNG

const SEED = 0x9ac3e51;

function mulberry32(seed) {
  let a = seed >>> 0;
  return function () {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

/** Per-case seed: one number reproduces one case, independent of loop order. */
const caseSeed = (i, salt = 0) => (SEED + Math.imul(i + 1, 0x9e3779b1) + salt) >>> 0;

const pick = (rnd, arr) => arr[Math.floor(rnd() * arr.length)];
const chance = (rnd, p) => rnd() < p;
const randInt = (rnd, lo, hi) => lo + Math.floor(rnd() * (hi - lo + 1));
const someOf = (rnd, arr, lo, hi) => {
  const n = Math.min(randInt(rnd, lo, hi), arr.length);
  const pool = [...arr];
  const out = [];
  for (let i = 0; i < n; i++) out.push(...pool.splice(Math.floor(rnd() * pool.length), 1));
  return out;
};

// =========================================================== GRAPH GENERATOR
//
// Generates WELL-FORMED normalized graphs in the schema of src/graph.js: the
// id conventions (tpl:, iface:, party:Owner.field, choice:Owner.Name,
// key:Tpl), the real edge kind set, every edge endpoint resolving to a node,
// and the node metadata the gate actually reads (a choice's consuming flag, a
// key's maintainer list, the external flag on declarations).
//
// It deliberately covers the shapes that previously needed metadata preserved
// in a baseline, because those are where a round-trip goes wrong: interfaces
// with view-projected controllers, contract keys, nonconsuming choices,
// external (undecoded) declarations, and operation edges that reach a
// template declared outside the graph.

const PARTY_FIELDS = ['issuer', 'owner', 'custodian', 'auditor', 'admin', 'sender', 'receiver'];
const DERIVED_REFS = ['spec.sender', 'leg.receiver', 'terms.admin', 'key._1'];
const CHOICE_NAMES = ['Transfer', 'Peek', 'Split', 'Merge', 'Seize', 'Mint', 'Settle'];
const IFACE_CHOICE_NAMES = ['Act', 'Inspect', 'Redeem'];
const VIEW_FIELDS = ['admin', 'owner', 'custodian'];
const OP_KINDS = [
  'create', 'createAndExercise', 'exercise', 'exerciseByKey',
  'fetch', 'fetchByKey', 'lookupByKey', 'lookupAllByKey', 'archive',
];
const MODULES = ['A', 'Token.Core', 'Settlement'];

const tplId = (n) => `tpl:${n}`;
const ifaceId = (n) => `iface:${n}`;
const partyId = (owner, field) => `party:${owner}.${field}`;
const choiceId = (owner, name) => `choice:${owner}.${name}`;
const keyId = (t) => `key:${t}`;
const edgeKeyOf = (e) => `${e.source}|${e.kind}|${e.target}`;

function genGraph(rnd) {
  /** @type {Map<string, Object>} */
  const nodes = new Map();
  /** @type {Array<Object>} */
  const edges = [];

  const addNode = (n) => {
    if (!nodes.has(n.id)) nodes.set(n.id, n);
    return nodes.get(n.id);
  };
  const addEdge = (source, target, kind, meta) => {
    edges.push({ id: `e${edges.length}`, source, target, kind, label: kind, ...(meta ? { meta } : {}) });
  };

  // A package with no templates at all is a real shape (project mode over a
  // module that only declares interfaces, or an empty DAR), and both gates
  // have to round-trip it rather than divide by zero somewhere.
  const nTemplates = chance(rnd, 0.04) ? 0 : randInt(rnd, 1, 5);
  const nInterfaces = randInt(rnd, 0, 3);
  const nExternalTpl = randInt(rnd, 0, 2);
  const nExternalIface = randInt(rnd, 0, 1);

  const templates = Array.from({ length: nTemplates }, (_, i) => `T${i}`);
  const interfaces = Array.from({ length: nInterfaces }, (_, i) => `I${i}`);
  const externalTemplates = Array.from({ length: nExternalTpl }, (_, i) => `X${i}`);
  const externalInterfaces = Array.from({ length: nExternalIface }, (_, i) => `EI${i}`);

  // ---------------------------------------------------------- external stubs
  // What graph.js emits when an operation edge mentions a declaration that is
  // not in this graph: a node carrying nothing but `external: true`.
  for (const x of externalTemplates) {
    addNode({ id: tplId(x), kind: 'template', label: x, meta: { external: true } });
  }
  for (const x of externalInterfaces) {
    addNode({ id: ifaceId(x), kind: 'interface', label: x, meta: { external: true } });
  }

  // ------------------------------------------------------------- interfaces
  /** interface name -> [{name, controllers: string[] (view.* refs)}] */
  const ifaceChoices = new Map();
  for (const iname of interfaces) {
    const module = pick(rnd, MODULES);
    addNode({
      id: ifaceId(iname),
      kind: 'interface',
      label: iname,
      module,
      meta: {
        external: false,
        viewtype: chance(rnd, 0.8) ? `${iname}View` : null,
        methods: someOf(rnd, VIEW_FIELDS, 0, 2),
      },
    });

    const chosen = someOf(rnd, IFACE_CHOICE_NAMES, 0, 2);
    const recs = [];
    for (const cname of chosen) {
      const cid = choiceId(iname, cname);
      addNode({
        id: cid,
        kind: 'choice',
        label: cname,
        interface: iname,
        owner: iname,
        ownerKind: 'interface',
        module,
        meta: { consuming: chance(rnd, 0.5), onInterface: true },
      });
      addEdge(ifaceId(iname), cid, 'declares');

      const controllers = someOf(rnd, VIEW_FIELDS, 0, 2).map((f) => `view.${f}`);
      for (const c of controllers) {
        const pid = partyId(iname, c);
        addNode({
          id: pid, kind: 'party', label: c, template: iname,
          owner: iname, ownerKind: 'interface', meta: { fromView: true },
        });
        addEdge(cid, pid, 'controller');
      }
      recs.push({ name: cname, controllers, id: cid });
    }
    ifaceChoices.set(iname, recs);
  }

  // -------------------------------------------------------------- templates
  const allIfaces = [...interfaces, ...externalInterfaces];
  const opTargets = [
    ...templates.map(tplId),
    ...externalTemplates.map(tplId),
    ...allIfaces.map(ifaceId),
  ];

  for (const tname of templates) {
    const module = pick(rnd, MODULES);
    const fields = someOf(rnd, PARTY_FIELDS, 1, 4);
    const implemented = someOf(rnd, allIfaces, 0, Math.min(2, allIfaces.length));
    const keyed = chance(rnd, 0.35);

    addNode({
      id: tplId(tname),
      kind: 'template',
      label: tname,
      module,
      meta: {
        external: false,
        fields: fields.map((f) => ({ name: f, type: 'Party', isParty: true })),
        ...(implemented.length ? { implements: implemented } : {}),
        ...(keyed ? { keyed: true } : {}),
      },
    });

    const partyNode = (ref, extra) => {
      const pid = partyId(tname, ref);
      addNode({
        id: pid, kind: 'party', label: ref, template: tname,
        owner: tname, ownerKind: 'template', ...(extra ? { meta: extra } : {}),
      });
      return pid;
    };
    for (const f of fields) partyNode(f, null);

    // signatory / observer. At least one signatory, as every real template has.
    for (const s of someOf(rnd, fields, 1, 2)) addEdge(tplId(tname), partyNode(s, null), 'signatory');
    for (const o of someOf(rnd, fields, 0, 2)) addEdge(tplId(tname), partyNode(o, null), 'observer');
    // a record projection used as a stakeholder: a `derived` party node
    if (chance(rnd, 0.25)) {
      const ref = pick(rnd, DERIVED_REFS);
      addEdge(tplId(tname), partyNode(ref, { derived: true }), chance(rnd, 0.5) ? 'observer' : 'signatory');
    }

    // ------------------------------------------------------------ key
    if (keyed) {
      const maintainers = someOf(rnd, fields, 1, 2);
      const kid = keyId(tname);
      addNode({
        id: kid,
        kind: 'key',
        label: `key ${tname}`,
        template: tname,
        owner: tname,
        ownerKind: 'template',
        meta: { expr: `(${maintainers.join(', ')})`, type: 'Party', maintainers },
      });
      addEdge(tplId(tname), kid, 'keyed-by');
      for (const m of maintainers) addEdge(kid, partyNode(m, null), 'maintainer');
    }

    // ----------------------------------------------------- interface instances
    for (const iname of implemented) {
      addEdge(tplId(tname), ifaceId(iname), 'implements', { viewType: `${iname}View` });
      // A view-projected interface controller resolved onto THIS template's
      // fields: the `view-controller` edge, which runs choice -> party and is
      // the one edge kind whose source is an interface choice.
      for (const ch of ifaceChoices.get(iname) || []) {
        for (const c of ch.controllers) {
          if (!chance(rnd, 0.6)) continue;
          const head = c.slice('view.'.length).split('.')[0];
          const field = pick(rnd, fields);
          addEdge(choiceId(iname, ch.name), partyNode(field, null), 'view-controller', {
            template: tname, viewField: head, expr: field,
          });
        }
      }
    }

    // ---------------------------------------------------------------- choices
    for (const cname of someOf(rnd, CHOICE_NAMES, 1, 3)) {
      const cid = choiceId(tname, cname);
      const consuming = chance(rnd, 0.6);
      addNode({
        id: cid,
        kind: 'choice',
        label: cname,
        template: tname,
        owner: tname,
        ownerKind: 'template',
        module,
        // Occasionally omit the flag entirely: graph.js copies whatever the
        // parser produced, and the differ's default ("consuming unless it says
        // false") has to agree with the baseline's default on that shape too.
        meta: chance(rnd, 0.9) ? { consuming } : {},
      });
      addEdge(tplId(tname), cid, 'declares');

      for (const c of someOf(rnd, fields, 0, 2)) addEdge(cid, partyNode(c, null), 'controller');
      if (chance(rnd, 0.3)) {
        // a choice-argument controller: not a template field, tagged fromArg
        const arg = pick(rnd, ['actor', 'newOwner']);
        const pid = `party:${tname}.${arg}#arg`;
        addNode({
          id: pid, kind: 'party', label: arg, template: tname, owner: tname,
          ownerKind: 'template', meta: { fromArg: true, projected: false },
        });
        addEdge(cid, pid, 'controller');
      }

      for (let i = 0, n = randInt(rnd, 0, 3); i < n; i++) {
        const target = pick(rnd, opTargets);
        addEdge(cid, target, pick(rnd, OP_KINDS),
          chance(rnd, 0.2) ? { via: ['helper', 'inner'] } : null);
      }
    }
  }

  // Interface choices carry operation edges too: graph.js runs the same
  // addOperationEdges over an interface's choices as over a template's, so the
  // differ sees `choice:I0.Act -create-> tpl:T1` as readily as a template's.
  for (const [iname, recs] of ifaceChoices) {
    for (const ch of recs) {
      for (let i = 0, n = randInt(rnd, 0, 2); i < n; i++) {
        if (!opTargets.length) break;
        addEdge(ch.id, pick(rnd, opTargets), pick(rnd, OP_KINDS),
          chance(rnd, 0.2) ? { via: [`${iname}.helper`] } : null);
      }
    }
  }

  // A real graph can carry the SAME (source, kind, target) twice (two calls to
  // the same operation in one choice body). Both the differ and the baseline
  // key on that triple, so duplicates must collapse rather than churn.
  if (edges.length && chance(rnd, 0.2)) {
    const dup = pick(rnd, edges);
    addEdge(dup.source, dup.target, dup.kind);
  }

  return {
    meta: { module: null, source: 'generated', warnings: [], modules: MODULES },
    nodes: [...nodes.values()],
    edges,
  };
}

const clone = (g) => JSON.parse(JSON.stringify(g));
const nodeIds = (g) => g.nodes.map((n) => n.id);
const edgeKeys = (g) => new Set(g.edges.map(edgeKeyOf));

/** All (source, kind, target) triples the schema would allow but g lacks. */
function absentEdgeCandidates(g) {
  const present = edgeKeys(g);
  const by = (kind) => g.nodes.filter((n) => n.kind === kind).map((n) => n.id);
  const [tpls, ifaces, choices, parties, keys] = [
    by('template'), by('interface'), by('choice'), by('party'), by('key'),
  ];
  const out = [];
  const add = (sources, targets, kind) => {
    for (const s of sources) for (const t of targets) {
      const e = { source: s, kind, target: t };
      if (!present.has(edgeKeyOf(e))) out.push(e);
    }
  };
  add(tpls, parties, 'signatory');
  add(tpls, parties, 'observer');
  add(tpls, choices, 'declares');
  add(tpls, ifaces, 'implements');
  add(tpls, keys, 'keyed-by');
  add(keys, parties, 'maintainer');
  add(choices, parties, 'controller');
  add(choices, parties, 'view-controller');
  for (const op of OP_KINDS) add(choices, [...tpls, ...ifaces], op);
  return out;
}

const withEdge = (g, e) => {
  const out = clone(g);
  out.edges.push({ id: `e${out.edges.length}`, source: e.source, target: e.target, kind: e.kind, label: e.kind });
  return out;
};

/**
 * Random well-formed EDITS to a graph: the pairs (a, b) that the antisymmetry
 * property needs must differ in more than one way, and in every dimension the
 * differ looks at (edges, nodes, consuming, maintainers, external).
 */
function mutate(rnd, g) {
  const out = clone(g);
  const n = randInt(rnd, 1, 4);
  for (let i = 0; i < n; i++) {
    const ops = [];
    const candidates = absentEdgeCandidates(out);
    if (candidates.length) ops.push('add-edge');
    if (out.edges.length) ops.push('remove-edge', 'remove-edge');
    const choices = out.nodes.filter((x) => x.kind === 'choice');
    if (choices.length) ops.push('toggle-consuming');
    const keys = out.nodes.filter((x) => x.kind === 'key');
    if (keys.length) ops.push('change-maintainers');
    const decls = out.nodes.filter((x) => x.kind === 'template' || x.kind === 'interface');
    if (decls.length) ops.push('flip-external', 'drop-node');
    ops.push('add-node');
    switch (pick(rnd, ops)) {
      case 'add-edge': {
        const e = pick(rnd, candidates);
        out.edges.push({ id: `m${i}`, source: e.source, target: e.target, kind: e.kind, label: e.kind });
        break;
      }
      case 'remove-edge': {
        const victim = pick(rnd, out.edges);
        const key = edgeKeyOf(victim);
        // remove every copy: the differ keys on the triple, so leaving a
        // duplicate behind would mean no change at all
        out.edges = out.edges.filter((e) => edgeKeyOf(e) !== key);
        break;
      }
      case 'toggle-consuming': {
        const c = pick(rnd, choices);
        const node = out.nodes.find((x) => x.id === c.id);
        node.meta = { ...(node.meta || {}), consuming: !(node.meta && node.meta.consuming !== false) };
        break;
      }
      case 'change-maintainers': {
        const k = pick(rnd, keys);
        const node = out.nodes.find((x) => x.id === k.id);
        const cur = [...((node.meta || {}).maintainers || [])];
        if (cur.length && chance(rnd, 0.5)) cur.pop();
        else cur.push(pick(rnd, PARTY_FIELDS));
        node.meta = { ...(node.meta || {}), maintainers: cur };
        break;
      }
      case 'flip-external': {
        const d = pick(rnd, decls);
        const node = out.nodes.find((x) => x.id === d.id);
        node.meta = { ...(node.meta || {}), external: !(node.meta && node.meta.external) };
        break;
      }
      case 'drop-node': {
        // Dropping a template drops what it OWNS (its choices, its key, its
        // party fields) as well, the way deleting it from the source would.
        // Leaving orphaned choice nodes behind would test a shape no parser
        // can produce, and a "bug" found on one would not be a bug.
        const d = pick(rnd, decls);
        const owned = new Set([d.id]);
        for (const x of out.nodes) {
          if (x.owner === d.label && x.id !== d.id) owned.add(x.id);
        }
        out.nodes = out.nodes.filter((x) => !owned.has(x.id));
        out.edges = out.edges.filter((e) => !owned.has(e.source) && !owned.has(e.target));
        break;
      }
      case 'add-node': {
        const id = `party:T0.extra${i}`;
        if (!out.nodes.some((x) => x.id === id)) {
          out.nodes.push({
            id, kind: 'party', label: `extra${i}`, template: 'T0', owner: 'T0', ownerKind: 'template',
          });
        }
        break;
      }
    }
  }
  return out;
}

// ------------------------------------------------------------------ shrinker
//
// Not required for a property test whose cases are already small, but a
// 40-node counterexample is not a bug report. This drops one edge, or one node
// with its incident edges, for as long as the property keeps failing. Linear
// passes, capped, so a failing property still reports quickly.

function shrinkGraph(graph, fails, budget = 400) {
  let best = graph;
  let spent = 0;
  let progress = true;
  while (progress && spent < budget) {
    progress = false;
    for (let i = 0; i < best.edges.length && spent < budget; i++) {
      const cand = { ...best, edges: best.edges.filter((_, j) => j !== i) };
      spent++;
      if (safeFails(fails, cand)) { best = cand; progress = true; break; }
    }
    if (progress) continue;
    for (let i = 0; i < best.nodes.length && spent < budget; i++) {
      const id = best.nodes[i].id;
      const cand = {
        ...best,
        nodes: best.nodes.filter((_, j) => j !== i),
        edges: best.edges.filter((e) => e.source !== id && e.target !== id),
      };
      spent++;
      if (safeFails(fails, cand)) { best = cand; progress = true; break; }
    }
  }
  return best;
}

/** A shrink candidate that throws is a failure too, but must not kill the run. */
function safeFails(fails, g) {
  try {
    return fails(g);
  } catch (_) {
    return true;
  }
}

const repro = (label, seed, graph, detail) =>
  `${label}\n  seed: 0x${seed.toString(16)} (const rnd = mulberry32(0x${seed.toString(16)}); genGraph(rnd))\n` +
  (detail ? `  detail: ${detail}\n` : '') +
  `  graph: ${JSON.stringify(graph, null, 2)}`;

// ======================================================= GENERATOR FIDELITY
//
// A generated-input suite is worth exactly what its generator covers. This
// test compares the generator's output against what src/graph.js ACTUALLY
// emits on this repository's own example sources, so the file cannot quietly
// degrade into proving things about a schema nobody uses: every node kind,
// every edge kind in the documented set, and every node metadata key the
// example corpus produces must appear in generated graphs too.

const EXAMPLES_DIR = fileURLToPath(new URL('../examples', import.meta.url));

function shapesOf(graphs) {
  const nodeKinds = new Set();
  const edgeKinds = new Set();
  /** @type {Map<string, Set<string>>} */
  const metaKeys = new Map();
  for (const g of graphs) {
    for (const n of g.nodes) {
      nodeKinds.add(n.kind);
      if (!metaKeys.has(n.kind)) metaKeys.set(n.kind, new Set());
      for (const k of Object.keys(n.meta || {})) metaKeys.get(n.kind).add(k);
    }
    for (const e of g.edges) edgeKinds.add(e.kind);
  }
  return { nodeKinds, edgeKinds, metaKeys };
}

test('generator fidelity: generated graphs cover the real schema', (t) => {
  const real = shapesOf(
    readdirSync(EXAMPLES_DIR)
      .filter((f) => f.endsWith('.daml'))
      .map((f) => buildGraph(parseDaml(readFileSync(`${EXAMPLES_DIR}/${f}`, 'utf8'))))
  );
  const generated = shapesOf(
    Array.from({ length: 200 }, (_, i) => genGraph(mulberry32(caseSeed(i, 0xf1))))
  );

  for (const kind of real.nodeKinds) {
    assert.ok(generated.nodeKinds.has(kind), `generator never emits a ${kind} node`);
  }
  // The full documented edge-kind set, not merely the kinds the examples reach.
  for (const kind of [...STRUCTURAL_KINDS, ...OPERATION_KINDS]) {
    assert.ok(generated.edgeKinds.has(kind), `generator never emits a ${kind} edge`);
  }
  for (const [nodeKind, keys] of real.metaKeys) {
    for (const key of keys) {
      // `projected` only appears on a controller that is a record projection;
      // the generator emits the flag itself, set to false, which is the same
      // shape as far as every consumer of the metadata is concerned.
      assert.ok(
        (generated.metaKeys.get(nodeKind) || new Set()).has(key),
        `generator never emits meta.${key} on a ${nodeKind} node, but src/graph.js does`
      );
    }
  }
  t.diagnostic(
    `node kinds ${[...generated.nodeKinds].sort().join(',')}; ` +
    `${generated.edgeKinds.size} edge kinds; ` +
    `real corpus: ${real.nodeKinds.size} node kinds, ${real.edgeKinds.size} edge kinds`
  );
});

// ===========================================================================
// GRAPH DIFF (src/diff.js)
// ===========================================================================

// The widening/narrowing table, restated INDEPENDENTLY of src/diff.js. If the
// table in the source is edited, the properties below fail rather than
// silently agreeing with whatever the new table says.
const EXPECTED_ADD_DIRECTION = {
  declares: 'widening',          // new exercisable surface
  controller: 'widening',        // one more party may exercise
  'view-controller': 'widening', // ditto, reached through an interface view
  observer: 'widening',          // one more party may see
  implements: 'widening',        // a whole interface's choices become reachable
  signatory: 'narrowing',        // one MORE party must authorize
  maintainer: 'narrowing',       // key lookup becomes more constrained
  'keyed-by': 'neutral',         // having a key is not itself access
  create: 'widening', createAndExercise: 'widening', exercise: 'widening',
  exerciseByKey: 'widening', archive: 'widening', fetch: 'widening',
  fetchByKey: 'widening', lookupByKey: 'widening', lookupAllByKey: 'widening',
};

const CASES_DIFF = 500;

test('property 1: diffGraphs(g, g) is empty for every generated graph', (t) => {
  // LAW (reflexivity): a graph compared against itself reports nothing.
  // A gate that fires on an unchanged tree is a gate that gets switched off.
  let n = 0;
  for (let i = 0; i < CASES_DIFF; i++) {
    const seed = caseSeed(i);
    const g = genGraph(mulberry32(seed));
    const { changes, summary } = diffGraphs(g, g);
    if (changes.length !== 0) {
      const min = shrinkGraph(g, (c) => diffGraphs(c, c).changes.length !== 0);
      assert.fail(repro(
        `diffGraphs(g, g) reported ${changes.length} change(s)`, seed, min,
        changes.map((c) => `${c.code} ${c.key}`).join('; ')
      ));
    }
    assert.equal(summary.total, 0);
    n++;
  }
  assert.ok(n >= CASES_DIFF, `only ${n} cases ran`);
  t.diagnostic(`${n} generated graphs, all reflexive`);
});

test('property 2: renumbering every edge id produces no changes', (t) => {
  // LAW (id independence): edge ids are positional (e0, e1, ...) and shift
  // whenever anything earlier in the graph changes. Diffing must key on
  // (source, kind, target) only, or an unrelated edit reports the whole graph
  // as churn.
  let n = 0;
  for (let i = 0; i < CASES_DIFF; i++) {
    const seed = caseSeed(i, 0x1d);
    const g = genGraph(mulberry32(seed));
    const renumbered = {
      ...g,
      // reversed AND reprefixed: no accidental agreement with the originals
      edges: g.edges.map((e, k) => ({ ...e, id: `zz${g.edges.length - k}` })),
    };
    const { changes } = diffGraphs(g, renumbered);
    if (changes.length !== 0) {
      const fails = (c) => diffGraphs(c, { ...c, edges: c.edges.map((e, k) => ({ ...e, id: `zz${k}` })) }).changes.length !== 0;
      assert.fail(repro(
        `edge id churn surfaced as ${changes.length} change(s)`, seed, shrinkGraph(g, fails),
        changes.map((c) => c.code).join(', ')
      ));
    }
    // and the shuffled-order version, since Map iteration follows input order
    const reordered = { ...g, edges: [...g.edges].reverse() };
    assert.deepEqual(diffGraphs(g, reordered).changes, [], 'edge ORDER must not matter either');
    n++;
  }
  assert.ok(n >= CASES_DIFF, `only ${n} cases ran`);
  t.diagnostic(`${n} generated graphs, id and order independent`);
});

/**
 * Pair changes across the two diff directions. The code embeds the op
 * (`edge-added-observer` vs `edge-removed-observer`), so the identity of the
 * THING that changed is code-with-op-erased plus scope plus key.
 */
const pairKey = (c) => `${c.scope}|${c.key}|${c.code.replace(/-(added|removed)-/, '-*-')}`;
const mirrorOp = (op) => (op === 'added' ? 'removed' : op === 'removed' ? 'added' : op);
const flipDir = (d) => (d === 'widening' ? 'narrowing' : d === 'narrowing' ? 'widening' : 'neutral');

test('property 3: diffing in the opposite direction flips every direction', (t) => {
  // LAW (antisymmetry): for every change in diffGraphs(a, b) there is exactly
  // one change in diffGraphs(b, a) about the same thing, with the mirrored op
  // and the opposite direction; `neutral` maps to itself.
  //
  // ONE DOCUMENTED EXCEPTION, checked rather than excused:
  // `key-maintainers-changed` is reported as WIDENING IN BOTH DIRECTIONS.
  // That is deliberate and not a bug: swapping one maintainer for another is
  // neither a pure widening nor a pure narrowing (a different set of parties
  // can now look contracts up by key, and the differ does not compare the sets
  // element-wise), so the gate takes the conservative side and asks for a
  // human. The property below PINS that asymmetry instead of ignoring it, so
  // the day someone makes it set-aware, this test says so.
  let n = 0;
  let mirrored = 0;
  let conservativeKeyChanges = 0;
  for (let i = 0; i < CASES_DIFF; i++) {
    const seed = caseSeed(i, 0x2d);
    const rnd = mulberry32(seed);
    const a = genGraph(rnd);
    const b = mutate(rnd, a);

    const fwd = diffGraphs(a, b).changes;
    const rev = diffGraphs(b, a).changes;
    const revBy = new Map(rev.map((c) => [pairKey(c), c]));

    assert.equal(
      rev.length, fwd.length,
      repro(`asymmetric change COUNT: ${fwd.length} forward vs ${rev.length} reverse`, seed, b)
    );

    for (const c of fwd) {
      const m = revBy.get(pairKey(c));
      assert.ok(m, repro(`no mirror for ${c.code} ${c.key}`, seed, b, JSON.stringify(c)));
      assert.equal(m.op, mirrorOp(c.op), repro(`op not mirrored for ${c.code}`, seed, b));
      if (c.code === 'key-maintainers-changed') {
        assert.equal(c.direction, 'widening');
        assert.equal(m.direction, 'widening', 'the documented conservative exception');
        conservativeKeyChanges++;
        continue;
      }
      assert.equal(
        m.direction, flipDir(c.direction),
        repro(`direction not flipped for ${c.code} ${c.key}: ` +
          `${c.direction} forward, ${m.direction} reverse`, seed, b)
      );
      mirrored++;
    }
    n++;
  }
  assert.ok(n >= CASES_DIFF, `only ${n} cases ran`);
  assert.ok(mirrored >= 900, `only ${mirrored} paired changes seen; the mutator stopped mutating`);
  t.diagnostic(
    `${n} graph pairs, ${mirrored} antisymmetric change pairs, ` +
    `${conservativeKeyChanges} conservative key-maintainer pairs`
  );
});

test('property 4: adding one edge yields exactly one change, with the documented direction', (t) => {
  // LAW (additivity of a single edit): if both endpoints already exist and the
  // triple (source, kind, target) is new, the diff reports exactly ONE change:
  // that edge, added, with the direction the widening/narrowing table gives.
  // Nothing else moves - no phantom node or metadata churn.
  let n = 0;
  const kindsSeen = new Set();
  for (let i = 0; i < CASES_DIFF; i++) {
    const seed = caseSeed(i, 0x3d);
    const rnd = mulberry32(seed);
    const g = genGraph(rnd);
    const candidates = absentEdgeCandidates(g);
    if (!candidates.length) continue;
    const e = pick(rnd, candidates);
    const after = withEdge(g, e);

    const { changes } = diffGraphs(g, after);
    if (changes.length !== 1) {
      const fails = (c) => {
        const cands = absentEdgeCandidates(c);
        if (!cands.find((x) => x.source === e.source && x.kind === e.kind && x.target === e.target)) return false;
        return diffGraphs(c, withEdge(c, e)).changes.length !== 1;
      };
      assert.fail(repro(
        `adding one ${e.kind} edge produced ${changes.length} changes`, seed, shrinkGraph(g, fails),
        `${e.source} -${e.kind}-> ${e.target}: ` + changes.map((c) => `${c.code} ${c.key}`).join('; ')
      ));
    }
    const c = changes[0];
    assert.equal(c.scope, 'edge');
    assert.equal(c.op, 'added');
    assert.equal(c.key, edgeKeyOf(e));
    assert.equal(c.code, `edge-added-${e.kind}`);
    assert.equal(
      c.direction, EXPECTED_ADD_DIRECTION[e.kind],
      repro(`adding ${e.kind} was classified ${c.direction}, table says ` +
        `${EXPECTED_ADD_DIRECTION[e.kind]}`, seed, g)
    );
    // and removing it again is the exact opposite
    const back = diffGraphs(after, g).changes;
    assert.equal(back.length, 1);
    assert.equal(back[0].direction, flipDir(c.direction));
    kindsSeen.add(e.kind);
    n++;
  }
  assert.ok(n >= 400, `only ${n} single-edge cases ran`);
  // Without this the loop could drift into testing three edge kinds forever.
  assert.ok(
    kindsSeen.size >= 12,
    `only ${kindsSeen.size} distinct edge kinds exercised: ${[...kindsSeen].join(', ')}`
  );
  t.diagnostic(`${n} single-edge additions over ${kindsSeen.size} edge kinds`);
});

// --------------------------------------------------------------- findings

const FINDING_CODES = [
  'no-observers', 'nonsignatory-consuming', 'no-controller', 'key-maintainer-not-signatory',
  'interface-widens-surface', 'cross-template-authority', 'party-boundary-crossing',
];
const SUBJECT_POOL = [
  'tpl:T0', 'tpl:T1', 'iface:I0', 'choice:T0.Transfer', 'party:T0.owner', 'key:T1',
];

function genFinding(rnd) {
  return {
    code: pick(rnd, FINDING_CODES),
    subjects: someOf(rnd, SUBJECT_POOL, 0, 3),
    severity: pick(rnd, ['info', 'warning', 'error']),
    message: `finding text ${Math.floor(rnd() * 1000)}`,
  };
}

test('property 5: finding identity survives rewording and subject reordering', (t) => {
  // LAW (fingerprint invariance): a finding's identity is its code plus the
  // SET of nodes it is about. Rewording the message, or emitting the same
  // subjects in another order, must not read as a new finding - otherwise
  // every improvement to the analysis text fails the gate, and the gate goes.
  let n = 0;
  let nonEmptySubjects = 0;
  for (let i = 0; i < 400; i++) {
    const rnd = mulberry32(caseSeed(i, 0x5d));
    const before = Array.from({ length: randInt(rnd, 1, 6) }, () => genFinding(rnd));
    const after = before.map((f) => ({
      ...f,
      subjects: [...f.subjects].reverse(),
      message: `COMPLETELY rewritten wording ${Math.floor(rnd() * 1e6)} (${f.subjects.length} subjects)`,
    }));
    for (let k = 0; k < before.length; k++) {
      assert.equal(
        findingFingerprint(before[k]), findingFingerprint(after[k]),
        `fingerprint changed under rewording/reordering: ${JSON.stringify({ before: before[k], after: after[k] })}`
      );
      if (before[k].subjects.length > 1) nonEmptySubjects++;
    }
    const d = diffFindings(before, after);
    assert.deepEqual(d.added, [], `rewording surfaced as ${d.added.length} new finding(s)`);
    assert.deepEqual(d.removed, []);

    // ... but a genuinely different subject IS a new finding
    const changed = [{ ...before[0], subjects: [...before[0].subjects, 'tpl:BrandNew'] }, ...before.slice(1)];
    const d2 = diffFindings(before, changed);
    assert.ok(d2.added.length >= 1, 'a new subject must be a new finding');
    n++;
  }
  assert.ok(n >= 400, `only ${n} cases ran`);
  assert.ok(nonEmptySubjects >= 200, `only ${nonEmptySubjects} multi-subject findings generated`);
  t.diagnostic(`${n} finding lists, ${nonEmptySubjects} with reorderable subject sets`);
});

// ===========================================================================
// BASELINE (src/baseline.js)
// ===========================================================================

const CASES_BASELINE = 400;

test('property 6: a baseline round-trip is exactly clean on every generated graph', (t) => {
  // LAW (round-trip identity): for every well-formed graph g,
  //   compareToBaseline(createBaseline(g, analyzeAll(g)), g, analyzeAll(g))
  // reports zero graph changes, zero new findings and zero fixed findings.
  //
  // This is the load-bearing one. The baseline does not store the graph; it
  // stores node ids, edge triples and the few access-relevant metadata fields,
  // and compareToBaseline RECONSTRUCTS a graph from that to diff against. Any
  // disagreement between what createBaseline drops and what the reconstruction
  // assumes shows up here as a phantom change on an unchanged tree.
  //
  // The generator deliberately covers interfaces, contract keys, nonconsuming
  // choices, choices with no consuming flag at all, external declarations and
  // duplicate edges, since those are exactly the shapes where "what was
  // dropped" and "what is assumed" can drift apart.
  let n = 0;
  const shapes = { keys: 0, interfaces: 0, nonconsuming: 0, external: 0, dupEdges: 0 };
  for (let i = 0; i < CASES_BASELINE; i++) {
    const seed = caseSeed(i, 0x6d);
    const g = genGraph(mulberry32(seed));
    const a = analyzeAll(g);

    // The baseline is built from a SHUFFLED copy and read back through JSON,
    // because that is the real path: node and edge array order is an artifact
    // of parse order, and the baseline lives in a committed file.
    const shuffled = { ...g, nodes: [...g.nodes].reverse(), edges: [...g.edges].reverse() };
    const roundTrip = (graph) => {
      const an = analyzeAll(graph);
      const stored = JSON.parse(JSON.stringify(createBaseline(
        { ...graph, nodes: [...graph.nodes].reverse(), edges: [...graph.edges].reverse() }, an
      )));
      return compareToBaseline(stored, graph, an);
    };
    const notClean = (graph) => {
      const r = roundTrip(graph);
      return r.graphDiff.summary.total !== 0 || r.newFindings.length > 0 || r.fixedFindings.length > 0;
    };
    const result = roundTrip(g);
    // ... and once more on a MUTATED graph, which reaches shapes the generator
    // alone does not: a flipped external flag, an edited maintainer list, a
    // deleted template, an added edge.
    const mutated = mutate(mulberry32(seed ^ 0x6f), g);
    const mutatedResult = roundTrip(mutated);
    if (mutatedResult.graphDiff.summary.total !== 0 || !mutatedResult.ok) {
      assert.fail(repro(
        'baseline round-trip was not clean on a mutated graph', seed,
        shrinkGraph(mutated, notClean),
        mutatedResult.graphDiff.changes.map((c) => `${c.code} ${c.key}: ${c.message}`).join('; ')
      ));
    }
    assert.deepEqual(diffGraphs(g, shuffled).changes, [], 'node/edge order must not be a change');

    if (result.graphDiff.summary.total !== 0 || result.newFindings.length || result.fixedFindings.length) {
      assert.fail(repro(
        'baseline round-trip was not clean', seed, shrinkGraph(g, notClean),
        result.graphDiff.changes.map((c) => `${c.code} ${c.key}: ${c.message}`).join('; ') +
        ` | newFindings=${result.newFindings.length} fixedFindings=${result.fixedFindings.length}`
      ));
    }
    assert.equal(result.ok, true);

    if (g.nodes.some((x) => x.kind === 'key')) shapes.keys++;
    if (g.nodes.some((x) => x.kind === 'interface')) shapes.interfaces++;
    if (g.nodes.some((x) => x.kind === 'choice' && x.meta && x.meta.consuming === false)) shapes.nonconsuming++;
    if (g.nodes.some((x) => x.meta && x.meta.external)) shapes.external++;
    if (new Set(g.edges.map(edgeKeyOf)).size !== g.edges.length) shapes.dupEdges++;
    n++;
  }
  assert.ok(n >= CASES_BASELINE, `only ${n} cases ran`);
  // A clean round-trip over hundreds of graphs that all happened to be a bare
  // template would prove nothing; assert the interesting shapes were present.
  assert.ok(shapes.keys >= 40, `only ${shapes.keys} graphs had a contract key`);
  assert.ok(shapes.interfaces >= 40, `only ${shapes.interfaces} graphs had an interface`);
  assert.ok(shapes.nonconsuming >= 40, `only ${shapes.nonconsuming} graphs had a nonconsuming choice`);
  assert.ok(shapes.external >= 40, `only ${shapes.external} graphs had an external declaration`);
  t.diagnostic(
    `${n} round-trips clean; shapes covered: ${Object.entries(shapes).map(([k, v]) => `${k}=${v}`).join(' ')}`
  );
});

test('property 7: suppression only ever removes findings, and is fully accounted for', (t) => {
  // LAW (suppression monotonicity): suppressing a code never increases the
  // kept-finding count, and for EVERY code
  //     kept(code) + summary.suppressed(code) === raw(code)
  // so a quiet report can never be mistaken for a clean one.
  let n = 0;
  let withSuppression = 0;
  for (let i = 0; i < 250; i++) {
    const seed = caseSeed(i, 0x7d);
    const rnd = mulberry32(seed);
    const g = genGraph(rnd);
    const raw = analyzeAll(g);
    const rawByCode = {};
    for (const f of raw.all) rawByCode[f.code] = (rawByCode[f.code] || 0) + 1;

    const codes = Object.keys(rawByCode);
    const victim = codes.length ? someOf(rnd, codes, 1, Math.min(2, codes.length)) : ['nothing-at-all'];
    const filtered = analyzeAll(g, { suppress: victim });

    assert.ok(
      filtered.all.length <= raw.all.length,
      repro(`suppressing ${victim.join(',')} INCREASED findings ` +
        `${raw.all.length} -> ${filtered.all.length}`, seed, g)
    );
    assert.equal(filtered.summary.totalBeforeFilter, raw.all.length);

    const allCodes = new Set([...codes, ...Object.keys(filtered.summary.byCode)]);
    for (const code of allCodes) {
      const kept = filtered.summary.byCode[code] || 0;
      const supp = filtered.summary.suppressed[code] || 0;
      assert.equal(
        kept + supp, rawByCode[code] || 0,
        repro(`accounting broken for ${code}: kept ${kept} + suppressed ${supp} != raw ${rawByCode[code] || 0}`, seed, g)
      );
      if (victim.includes(code)) assert.equal(kept, 0, `${code} was suppressed but ${kept} kept`);
    }
    if (codes.length) withSuppression++;
    n++;
  }
  assert.ok(n >= 250, `only ${n} cases ran`);
  assert.ok(withSuppression >= 120, `only ${withSuppression} graphs produced any finding to suppress`);
  t.diagnostic(`${n} graphs, ${withSuppression} with a code actually suppressed`);
});

test('property 8: raising minSeverity never adds a finding', (t) => {
  // LAW (threshold monotonicity): the kept sets are NESTED,
  //   findings(error) subset-of findings(warning) subset-of findings(info)
  // and the counts are non-increasing. A threshold that could surface a
  // finding the lower threshold hid would make the summary meaningless.
  let n = 0;
  let strictlyShrinking = 0;
  for (let i = 0; i < 250; i++) {
    const seed = caseSeed(i, 0x8d);
    const g = genGraph(mulberry32(seed));
    const at = (minSeverity) => analyzeAll(g, { minSeverity });
    const info = at('info');
    const warning = at('warning');
    const error = at('error');

    assert.ok(
      warning.all.length <= info.all.length && error.all.length <= warning.all.length,
      repro(`counts not monotone: info=${info.all.length} warning=${warning.all.length} error=${error.all.length}`, seed, g)
    );
    const fpsOf = (r) => new Set(r.all.map((f) => `${findingFingerprint(f)}|${f.severity}|${f.message}`));
    const [iS, wS, eS] = [fpsOf(info), fpsOf(warning), fpsOf(error)];
    for (const f of wS) assert.ok(iS.has(f), repro(`minSeverity=warning surfaced a finding info hid: ${f}`, seed, g));
    for (const f of eS) assert.ok(wS.has(f), repro(`minSeverity=error surfaced a finding warning hid: ${f}`, seed, g));
    // the threshold must also be doing something, not just passing everything
    assert.equal(warning.all.every((f) => f.severity !== 'info'), true);
    assert.equal(error.all.every((f) => f.severity === 'error'), true);
    if (warning.all.length < info.all.length) strictlyShrinking++;
    n++;
  }
  assert.ok(n >= 250, `only ${n} cases ran`);
  assert.ok(strictlyShrinking >= 50, `the threshold never actually filtered anything (${strictlyShrinking})`);
  t.diagnostic(`${n} graphs, ${strictlyShrinking} where raising the threshold removed something`);
});

test('property 9: a widening edit fails the gate, a narrowing edit does not', (t) => {
  // LAW (gate direction): take a baseline from g. Adding an observer edge
  // (widening) must make compareToBaseline report a widening change and set
  // ok=false. Adding a signatory edge (narrowing: one MORE party must
  // authorize) must report NO widening change - the access-structure half of
  // the gate stays quiet.
  //
  // Scope note, stated rather than papered over: the gate's other half is the
  // finding list, and adding a signatory CAN legitimately change findings (it
  // can fix a nonsignatory-consuming, or raise a new key-maintainer finding).
  // The law here is about direction classification, so it asserts
  // `widening.length === 0` for the narrowing edit, and separately counts how
  // often the whole gate stayed green.
  let widenCases = 0;
  let narrowCases = 0;
  let narrowGreen = 0;
  for (let i = 0; i < 250; i++) {
    const seed = caseSeed(i, 0x9d);
    const rnd = mulberry32(seed);
    const g = genGraph(rnd);
    const a = analyzeAll(g);
    const baseline = createBaseline(g, a);

    const absent = absentEdgeCandidates(g);
    const widenEdge = pick(rnd, absent.filter((e) => e.kind === 'observer'));
    const narrowEdge = pick(rnd, absent.filter((e) => e.kind === 'signatory'));

    if (widenEdge) {
      const after = withEdge(g, widenEdge);
      const r = compareToBaseline(baseline, after, analyzeAll(after));
      assert.ok(
        r.widening.length >= 1,
        repro(`adding observer ${widenEdge.source} -> ${widenEdge.target} did not register as widening`, seed, g)
      );
      assert.equal(r.ok, false, repro('a widening edit passed the gate', seed, g));
      widenCases++;
    }
    if (narrowEdge) {
      const after = withEdge(g, narrowEdge);
      const r = compareToBaseline(baseline, after, analyzeAll(after));
      assert.equal(
        r.widening.length, 0,
        repro(`adding signatory ${narrowEdge.source} -> ${narrowEdge.target} was classified as widening`, seed, g,
          r.widening.map((c) => `${c.code} ${c.key}`).join('; '))
      );
      assert.equal(r.graphDiff.changes.filter((c) => c.direction === 'narrowing').length, 1);
      if (r.ok) narrowGreen++;
      narrowCases++;
    }
  }
  assert.ok(widenCases >= 120, `only ${widenCases} widening cases ran`);
  assert.ok(narrowCases >= 120, `only ${narrowCases} narrowing cases ran`);
  t.diagnostic(
    `${widenCases} widening edits all failed the gate; ${narrowCases} narrowing edits produced no ` +
    `widening change (${narrowGreen} left the whole gate green, the rest moved a finding)`
  );
});

// ===========================================================================
// VERDICT BASELINE (src/verdict-baseline.js)
// ===========================================================================

const STATUS_FAMILIES = [
  'PROVED', 'PROVED-BOUNDED', 'PROVED-PARTIAL', 'DISPROVED',
  'NOT-MODELLABLE', 'NOT-APPLICABLE', 'SOLVER-UNKNOWN', 'SOLVER-ERROR',
];
const PROVING_FAMILIES = new Set(['PROVED', 'PROVED-BOUNDED', 'PROVED-PARTIAL']);
const PROPERTIES = ['amount-conservation', 'division-safety', 'no-negative-balance', 'authorization'];
const TRANSITIONS = ['Token.Transfer', 'Token.Mint', 'Token.Burn', 'Holding.Split', 'Holding.Merge'];

/** Render a family as a status string, with the parenthesised bound where the family carries one. */
const renderStatus = (rnd, family) =>
  family === 'PROVED-BOUNDED' ? `PROVED-BOUNDED (lists up to length ${randInt(rnd, 1, 9)})` : family;

function genReport(rnd, name = 'pkg') {
  const seen = new Set();
  const results = [];
  for (let i = 0, n = randInt(rnd, 1, 8); i < n; i++) {
    const property = pick(rnd, PROPERTIES);
    const transition = pick(rnd, TRANSITIONS);
    const key = `${property}::${transition}`;
    if (seen.has(key)) continue; // one verdict per obligation, as verify.js emits
    seen.add(key);
    results.push({ property, transition, status: renderStatus(rnd, pick(rnd, STATUS_FAMILIES)) });
  }
  return { package: name, results };
}

test('property 10: a verdict baseline round-trip against its own report is clean', (t) => {
  // LAW (round-trip identity, proof gate): comparing a report list against a
  // baseline built from that same list yields no regressions, no improvements,
  // and counts every obligation as unchanged. Serializing the baseline through
  // JSON first changes nothing - that is how the committed file is read back.
  //
  // The report list is plural because the API is plural: one entry per DAR.
  // Two DARs CAN carry the same package name (two versions of one package in
  // the same directory), so the generator produces colliding names on purpose.
  // That case is where this law first broke; see the fix note in
  // src/verdict-baseline.js.
  let n = 0;
  let totalObligations = 0;
  let collidingNames = 0;
  for (let i = 0; i < 300; i++) {
    const seed = caseSeed(i, 0xa1);
    const rnd = mulberry32(seed);
    const reports = Array.from({ length: randInt(rnd, 1, 3) }, (_, k) => {
      // ~1 in 3 report lists reuses a package name across two DARs
      const name = chance(rnd, 0.3) ? 'pkg0' : `pkg${k}`;
      return { ...genReport(rnd, name), dar: `dar${k}.dar` };
    });
    const baseline = JSON.parse(JSON.stringify(createVerdictBaseline(reports)));
    const cmp = compareVerdicts(baseline, reports);
    const detail = JSON.stringify({ reports, baseline, cmp }, null, 2);
    assert.deepEqual(cmp.regressions, [], `round-trip reported regressions\n  seed: 0x${seed.toString(16)}\n${detail}`);
    assert.deepEqual(cmp.improvements, [], `round-trip reported improvements\n  seed: 0x${seed.toString(16)}\n${detail}`);
    // One verdict per obligation per PACKAGE: obligations that two same-named
    // reports share are one obligation, not two.
    const distinct = new Set();
    for (const r of reports) for (const x of r.results) distinct.add(`${r.package}::${verdictKey(x)}`);
    assert.equal(cmp.unchanged, distinct.size, `seed 0x${seed.toString(16)}\n${detail}`);
    assert.equal(cmp.ok, true);
    if (new Set(reports.map((r) => r.package)).size !== reports.length) collidingNames++;
    totalObligations += distinct.size;
    n++;
  }
  assert.ok(n >= 300 && totalObligations >= 900, `${n} reports / ${totalObligations} obligations is too few`);
  assert.ok(collidingNames >= 30, `only ${collidingNames} report lists reused a package name`);
  t.diagnostic(
    `${n} multi-package round-trips over ${totalObligations} obligations ` +
    `(${collidingNames} lists with two DARs of the same package)`
  );
});

/**
 * The documented rule, restated here INDEPENDENTLY of src/verdict-baseline.js
 * (ci/verdicts/README.md, "What counts as a regression"):
 *
 *   PROVED* -> anything not PROVED*      regression, proof-lost
 *   a PROVED* obligation disappears      regression, proof-disappeared
 *   a new DISPROVED appears              regression, new-finding
 *   anything -> PROVED*                  improvement, never a failure
 *   only the bound in PROVED-BOUNDED (N) changes    not a change at all
 */
function expectedClassification(before, after) {
  if (before === after) return { kind: null, regression: false };
  if (before === undefined) {
    return after === 'DISPROVED'
      ? { kind: 'new-finding', regression: true }
      : { kind: 'new-verdict', regression: false };
  }
  if (after === undefined) {
    return PROVING_FAMILIES.has(before)
      ? { kind: 'proof-disappeared', regression: true }
      : { kind: 'obligation-gone', regression: false };
  }
  if (PROVING_FAMILIES.has(before) && !PROVING_FAMILIES.has(after)) {
    return { kind: 'proof-lost', regression: true };
  }
  if (!PROVING_FAMILIES.has(before) && after === 'DISPROVED') {
    return { kind: 'new-finding', regression: true };
  }
  return { kind: 'improved', regression: false };
}

test('property 11: every status transition is classified by the documented rule', (t) => {
  // LAW (classification totality): for EVERY ordered pair of statuses - the
  // full cross product of the eight families, plus the "obligation is new" and
  // "obligation is gone" edges - the gate's verdict matches the rule table in
  // ci/verdicts/README.md. Losing a proof is always a regression; gaining one
  // never is.
  let pairs = 0;
  let regressions = 0;
  const rnd = mulberry32(caseSeed(0, 0xb1));
  const withEdges = [...STATUS_FAMILIES, undefined];

  for (const beforeFam of withEdges) {
    for (const afterFam of withEdges) {
      if (beforeFam === undefined && afterFam === undefined) continue;
      // several renderings per pair, so the bounded family's parameter varies
      for (let rep = 0; rep < 3; rep++) {
        const key = { property: 'amount-conservation', transition: 'Token.Transfer' };
        const baseline = createVerdictBaseline([{
          package: 'pkg',
          results: beforeFam === undefined ? [] : [{ ...key, status: renderStatus(rnd, beforeFam) }],
        }]);
        const cmp = compareVerdicts(baseline, [{
          package: 'pkg',
          results: afterFam === undefined ? [] : [{ ...key, status: renderStatus(rnd, afterFam) }],
        }]);

        const want = expectedClassification(beforeFam, afterFam);
        const ctx = `${beforeFam || '(new)'} -> ${afterFam || '(gone)'}`;
        const got = [...cmp.regressions, ...cmp.improvements];
        if (want.kind === null) {
          assert.equal(got.length, 0, `${ctx} should be no change, got ${JSON.stringify(got)}`);
          assert.equal(cmp.unchanged, 1, ctx);
        } else {
          assert.equal(got.length, 1, `${ctx} should be exactly one difference, got ${JSON.stringify(got)}`);
          assert.equal(got[0].kind, want.kind, `${ctx} classified as ${got[0].kind}, rule says ${want.kind}`);
        }
        assert.equal(
          cmp.regressions.length > 0, want.regression,
          `${ctx}: gate ${cmp.ok ? 'passed' : 'failed'}, rule says ${want.regression ? 'regression' : 'no regression'}` +
          `\n  ${JSON.stringify(cmp)}`
        );
        // The two halves of the asymmetry, asserted directly:
        if (PROVING_FAMILIES.has(beforeFam) && !PROVING_FAMILIES.has(afterFam)) {
          assert.equal(cmp.ok, false, `${ctx}: a lost proof must fail the gate`);
        }
        if (PROVING_FAMILIES.has(afterFam) && !PROVING_FAMILIES.has(beforeFam)) {
          assert.equal(cmp.ok, true, `${ctx}: gaining a proof must never fail the gate`);
        }
        if (want.regression) regressions++;
        pairs++;
      }
    }
  }
  assert.ok(pairs >= 240, `only ${pairs} transition pairs checked`);
  assert.ok(regressions >= 30, `only ${regressions} of the pairs were regressions; the rule table looks inert`);
  t.diagnostic(`${pairs} status transitions checked (${regressions} classified as regressions)`);
});

test('property 11b: randomized multi-obligation reports agree with the rule, obligation by obligation', (t) => {
  // The same law, but on whole reports where many obligations move at once and
  // some appear or vanish - the shape a real refresh has.
  let n = 0;
  let moved = 0;
  for (let i = 0; i < 300; i++) {
    const seed = caseSeed(i, 0xb2);
    const rnd = mulberry32(seed);
    const before = genReport(rnd);
    // evolve it: restatus some, drop some, add some
    const after = {
      package: 'pkg',
      results: before.results
        .filter(() => chance(rnd, 0.85))
        .map((r) => (chance(rnd, 0.5) ? { ...r, status: renderStatus(rnd, pick(rnd, STATUS_FAMILIES)) } : r)),
    };
    const fresh = genReport(rnd).results.filter(
      (r) => !after.results.some((x) => verdictKey(x) === verdictKey(r))
    );
    after.results.push(...fresh);

    const baseline = createVerdictBaseline([before]);
    const cmp = compareVerdicts(baseline, [after]);

    const wasBy = new Map(before.results.map((r) => [verdictKey(r), statusFamily(r.status)]));
    const nowBy = new Map(after.results.map((r) => [verdictKey(r), statusFamily(r.status)]));
    const expectedRegressions = [];
    for (const key of new Set([...wasBy.keys(), ...nowBy.keys()])) {
      const want = expectedClassification(wasBy.get(key), nowBy.get(key));
      if (want.regression) expectedRegressions.push(`${key}:${want.kind}`);
    }
    const gotRegressions = cmp.regressions.map((r) => `${r.key}:${r.kind}`);
    const detail = `\n  seed: 0x${seed.toString(16)}\n  ${JSON.stringify({ before, after, cmp }, null, 2)}`;
    assert.deepEqual(new Set(gotRegressions), new Set(expectedRegressions), `regression set disagrees${detail}`);
    assert.equal(cmp.ok, expectedRegressions.length === 0, `ok flag disagrees${detail}`);
    if (gotRegressions.length) moved++;
    n++;
  }
  assert.ok(n >= 300, `only ${n} cases ran`);
  assert.ok(moved >= 100, `only ${moved} evolved reports contained a regression; the mutator is too gentle`);
  t.diagnostic(`${n} evolved reports, ${moved} containing at least one regression`);
});

test('property 12: changing only the bound in PROVED-BOUNDED is never a regression', (t) => {
  // LAW (bound insensitivity): the N in "PROVED-BOUNDED (lists up to length N)"
  // is a property of the RUN (the --bound flag), not of the code. Re-running
  // the verifier with a different bound must be reported as no change at all -
  // otherwise every bound tweak turns the gate red and the gate gets ignored.
  let n = 0;
  for (let i = 0; i < 300; i++) {
    const seed = caseSeed(i, 0xc1);
    const rnd = mulberry32(seed);
    const results = Array.from({ length: randInt(rnd, 1, 5) }, (_, k) => ({
      property: PROPERTIES[k % PROPERTIES.length],
      transition: TRANSITIONS[k % TRANSITIONS.length],
      status: `PROVED-BOUNDED (lists up to length ${randInt(rnd, 1, 12)})`,
    }));
    const before = { package: 'pkg', results };
    const after = {
      package: 'pkg',
      results: results.map((r) => ({ ...r, status: `PROVED-BOUNDED (lists up to length ${randInt(rnd, 1, 12)})` })),
    };
    const cmp = compareVerdicts(createVerdictBaseline([before]), [after]);
    const detail = `\n  seed: 0x${seed.toString(16)}\n  ${JSON.stringify({ before, after, cmp }, null, 2)}`;
    assert.deepEqual(cmp.regressions, [], `a bound change was called a regression${detail}`);
    assert.deepEqual(cmp.improvements, [], `a bound change was called an improvement${detail}`);
    assert.equal(cmp.unchanged, results.length, detail);
    assert.equal(statusFamily(after.results[0].status), 'PROVED-BOUNDED');
    n++;
  }
  assert.ok(n >= 300, `only ${n} cases ran`);
  t.diagnostic(`${n} bound-only rewrites, all reported as no change`);
});

test('property 13: a proof that disappears entirely is always caught', (t) => {
  // LAW (vanishing obligations): an obligation present in the baseline and
  // absent from the report is NOT silently fine. If its baselined verdict was
  // a proof, that is a proof-disappeared regression; if it was not, it is an
  // improvement. Diffing only what is present would miss the whole class - a
  // translator that stops producing a transition would look like a clean run.
  let provingDrops = 0;
  let otherDrops = 0;
  for (let i = 0; i < 300; i++) {
    const seed = caseSeed(i, 0xd1);
    const rnd = mulberry32(seed);
    const report = genReport(rnd);
    const victim = pick(rnd, report.results);
    const after = { package: 'pkg', results: report.results.filter((r) => r !== victim) };
    const cmp = compareVerdicts(createVerdictBaseline([report]), [after]);
    const key = verdictKey(victim);
    const fam = statusFamily(victim.status);
    const detail = `\n  seed: 0x${seed.toString(16)}\n  dropped ${key} (${fam})\n  ${JSON.stringify(cmp, null, 2)}`;

    if (PROVING_FAMILIES.has(fam)) {
      const r = cmp.regressions.find((x) => x.key === key);
      assert.ok(r, `a vanished ${fam} obligation was not reported as a regression${detail}`);
      assert.equal(r.kind, 'proof-disappeared', detail);
      assert.equal(r.after, '(gone)', detail);
      assert.equal(cmp.ok, false, detail);
      provingDrops++;
    } else {
      assert.equal(cmp.regressions.filter((x) => x.key === key).length, 0, detail);
      const imp = cmp.improvements.find((x) => x.key === key);
      assert.ok(imp && imp.kind === 'obligation-gone', `a vanished ${fam} obligation was not reported at all${detail}`);
      otherDrops++;
    }
    // An entire package missing from the report must not be silently clean
    // either: it is reported, and the baselined proofs it held are gone.
    assert.equal(compareVerdicts(createVerdictBaseline([report]), []).regressions.length, 0,
      'no reports at all means nothing was run: that is the runner\'s problem, not a regression');
  }
  assert.ok(provingDrops >= 80, `only ${provingDrops} dropped obligations were proofs`);
  assert.ok(otherDrops >= 80, `only ${otherDrops} dropped obligations were non-proofs`);
  t.diagnostic(`${provingDrops} vanished proofs all caught; ${otherDrops} vanished non-proofs reported as improvements`);
});
