// tests/project.test.js
//
//   node --test
//
// Project mode (src/project.js) and the helper-function call graph
// (src/callgraph.js): the cross-module resolution that a single-file parse
// cannot do.

import test from 'node:test';
import assert from 'node:assert/strict';

import { parseDaml } from '../src/parser.js';
import { parseProject } from '../src/project.js';
import { expandCalls } from '../src/callgraph.js';
import { buildGraph } from '../src/graph.js';
import { analyzeAll } from '../src/analysis.js';

const file = (path, source) => ({ path, source });

test('resolves a cross-module `exercise` by choice name', () => {
  const proj = parseProject([
    file('Caller.daml', `module Caller where
template Caller with p : Party where
  signatory p
  choice Go : ()
    controller p
    do
      exercise otherCid Bump
      return ()
`),
    file('Target.daml', `module Target where
template Target with p : Party where
  signatory p
  choice Bump : ()
    controller p
    do return ()
`),
  ]);

  const go = proj.templates.find((t) => t.name === 'Caller').choices[0];
  const ex = go.operations.find((o) => o.kind === 'exercise');
  assert.equal(ex.target, 'Target');
  assert.equal(ex.resolvedVia, 'project-choice-lookup');
  assert.equal(proj.stats.opsResolvedByProject, 1);

  const g = buildGraph(proj, { source: 'project-source' });
  assert.ok(g.edges.some((e) => e.kind === 'exercise' && e.target === 'tpl:Target'));
});

test('refuses to guess when two templates declare the same choice name', () => {
  const proj = parseProject([
    file('Caller.daml', `module Caller where
template Caller with p : Party where
  signatory p
  choice Go : ()
    controller p
    do
      exercise someCid Bump
      return ()
`),
    file('A.daml', `module A where
template A1 with p : Party where
  signatory p
  choice Bump : ()
    controller p
    do return ()
`),
    file('B.daml', `module B where
template B1 with p : Party where
  signatory p
  choice Bump : ()
    controller p
    do return ()
`),
  ]);

  const ex = proj.templates
    .find((t) => t.name === 'Caller')
    .choices[0].operations.find((o) => o.kind === 'exercise');
  assert.equal(ex.target, null, 'ambiguous target must stay null, not be guessed');
  assert.ok(proj.diagnostics.some((d) => d.code === 'ambiguous-choice-owner'));
  assert.equal(proj.stats.opsAmbiguous, 1);
});

test('a module-qualified call site disambiguates a shared choice name', () => {
  const proj = parseProject([
    file('Caller.daml', `module Caller where
template Caller with p : Party where
  signatory p
  choice Go : ()
    controller p
    do
      exercise someCid B.Bump
      return ()
`),
    file('A.daml', `module A where
template A1 with p : Party where
  signatory p
  choice Bump : ()
    controller p
    do return ()
`),
    file('B.daml', `module B where
template B1 with p : Party where
  signatory p
  choice Bump : ()
    controller p
    do return ()
`),
  ]);

  const ex = proj.templates
    .find((t) => t.name === 'Caller')
    .choices[0].operations.find((o) => o.kind === 'exercise');
  assert.equal(ex.target, 'B1', 'the `B.` qualifier picks module B');
  assert.ok(!proj.diagnostics.some((d) => d.code === 'ambiguous-choice-owner'));
});

test('reports an unknown choice as external rather than inventing an edge', () => {
  const proj = parseProject([
    file('Caller.daml', `module Caller where
template Caller with p : Party where
  signatory p
  choice Go : ()
    controller p
    do
      exercise cid ChoiceFromAnImportedDar
      return ()
`),
  ]);
  assert.ok(proj.diagnostics.some((d) => d.code === 'unknown-choice'));
  const ex = proj.templates[0].choices[0].operations.find((o) => o.kind === 'exercise');
  assert.equal(ex.target, null);
});

test('links an interface declared in a sibling module', () => {
  const proj = parseProject([
    file('Iface.daml', `module Iface where
interface Utxo where
  viewtype UtxoView

  choice Split : ()
    controller (view this).admin
    do return ()
`),
    file('Tok.daml', `module Tok where
template Tok with admin : Party where
  signatory admin

  choice Burn : ()
    controller admin
    do return ()

  interface instance Utxo for Tok where
    view = UtxoView with admin = admin
`),
  ]);

  assert.deepEqual(proj.interfaces.map((i) => i.name), ['Utxo']);
  // the interface is local to the project, so it must NOT be reported external
  assert.ok(!proj.diagnostics.some((d) => d.code === 'external-interface'));

  const g = buildGraph(proj, { source: 'project-source' });
  const iface = g.nodes.find((n) => n.kind === 'interface' && n.label === 'Utxo');
  assert.ok(iface);
  assert.equal(iface.meta.external, false);
  assert.ok(g.edges.some((e) => e.kind === 'implements' && e.source === 'tpl:Tok'));

  // the interface choice is now visible as exercisable on Tok
  const findings = analyzeAll(g).interfaces;
  assert.ok(findings.some((f) => f.code === 'interface-choice-exercisable' && /on Tok/.test(f.message)));
});

test('qualifies template names that collide across modules', () => {
  const proj = parseProject([
    file('A.daml', `module A where
template Mirror with p : Party where
  signatory p
`),
    file('B.daml', `module B where
template Mirror with p : Party where
  signatory p
`),
  ]);
  assert.deepEqual(proj.templates.map((t) => t.name).sort(), ['A:Mirror', 'B:Mirror']);
  assert.ok(proj.diagnostics.some((d) => d.code === 'qualified-names'));

  const g = buildGraph(proj, { source: 'project-source' });
  assert.equal(new Set(g.nodes.filter((n) => n.kind === 'template').map((n) => n.id)).size, 2);
});

test('call graph: a helper function’s create is attributed to the calling choice', () => {
  const proj = parseProject([
    file('Factory.daml', `module Factory where

import qualified Internal.Upsert as Upsert

template Factory with admin : Party where
  signatory admin

  choice CreateMirror : ()
    with contractData : Data
    controller admin
    do
      Upsert.tenantMirror admin contractData
      return ()
`),
    file('Internal/Upsert.daml', `module Internal.Upsert where

tenantMirror : Party -> Data -> Update (ContractId TenantMirror.TenantMirror)
tenantMirror admin contractData = do
  create TenantMirror.TenantMirror with
    admin = admin
    contractData = contractData
`),
    file('TenantMirror.daml', `module TenantMirror where
template TenantMirror with admin : Party where
  signatory admin
`),
  ]);

  const ch = proj.templates.find((t) => t.name === 'Factory').choices[0];
  assert.equal(ch.operations.length, 0, 'the choice body performs no direct ledger op');
  assert.equal(ch.inheritedOperations.length, 1);
  const inherited = ch.inheritedOperations[0];
  assert.equal(inherited.kind, 'create');
  assert.equal(inherited.target, 'TenantMirror');
  assert.deepEqual(inherited.via, ['Internal.Upsert.tenantMirror']);
  assert.ok(proj.diagnostics.some((d) => d.code === 'callgraph-attributed'));

  // the edge exists in the graph and carries its justification
  const g = buildGraph(proj, { source: 'project-source' });
  const edge = g.edges.find((e) => e.kind === 'create' && e.target === 'tpl:TenantMirror');
  assert.ok(edge, 'a create edge should reach TenantMirror');
  assert.deepEqual(edge.meta.via, ['Internal.Upsert.tenantMirror']);
});

test('call graph: transitive helper chains are followed', () => {
  const proj = parseProject([
    file('T.daml', `module T where

template T with p : Party where
  signatory p

  choice Go : ()
    controller p
    do
      outer p
      return ()

outer : Party -> Update ()
outer p = do
  inner p

inner : Party -> Update (ContractId Leaf)
inner p = do
  create Leaf with p = p
`),
    file('Leaf.daml', `module Leaf where
template Leaf with p : Party where
  signatory p
`),
  ]);

  const ch = proj.templates.find((t) => t.name === 'T').choices[0];
  const create = ch.inheritedOperations.find((o) => o.kind === 'create');
  assert.ok(create, 'a create two calls deep should be attributed');
  assert.equal(create.target, 'Leaf');
  assert.deepEqual(create.via, ['T.outer', 'T.inner']);
});

test('call graph: same-module helper resolves for a single pasted file too', () => {
  const model = expandCalls(
    parseDaml(`module A where

template T with p : Party where
  signatory p

  choice Go : ()
    controller p
    do
      makeLeaf p
      return ()

template Leaf with p : Party where
  signatory p

makeLeaf : Party -> Update (ContractId Leaf)
makeLeaf p = create Leaf with p = p
`)
  );
  const ch = model.templates.find((t) => t.name === 'T').choices[0];
  assert.ok(ch.inheritedOperations.some((o) => o.kind === 'create' && o.target === 'Leaf'));
});

test('call graph: recursion terminates', () => {
  const proj = parseProject([
    file('R.daml', `module R where

template T with p : Party where
  signatory p
  choice Go : ()
    controller p
    do
      loopy p
      return ()

loopy : Party -> Update ()
loopy p = do
  loopy p
`),
  ]);
  const ch = proj.templates[0].choices[0];
  assert.deepEqual(ch.inheritedOperations, []);
});

test('project mode drops per-file diagnostics it has superseded', () => {
  const proj = parseProject([
    file('Caller.daml', `module Caller where
template Caller with p : Party where
  signatory p
  choice Go : ()
    controller p
    do
      exercise otherCid Bump
      return ()
`),
    file('Target.daml', `module Target where
template Target with p : Party where
  signatory p
  choice Bump : ()
    controller p
    do return ()
`),
  ]);
  // the single-file "could not infer target" is stale once resolved
  assert.ok(!proj.diagnostics.some((d) => d.code === 'ambiguous-target'));
  // and a calculation module with no templates is unremarkable in a project
  const withCalc = parseProject([
    file('Calc.daml', 'module Calc where\n\nadd : Int -> Int -> Int\nadd a b = a + b\n'),
    file('Target.daml', 'module Target where\ntemplate Target with p : Party where\n  signatory p\n'),
  ]);
  assert.ok(!withCalc.diagnostics.some((d) => d.code === 'no-templates'));
});

test('every project-mode edge endpoint resolves to a node', () => {
  const proj = parseProject([
    file('Iface.daml', `module Iface where
interface I where
  viewtype V
  choice Act : ()
    controller (view this).admin
    do return ()
`),
    file('T.daml', `module T where
template T with admin : Party, other : Party where
  signatory admin
  observer other
  key (admin, other) : (Party, Party)
  maintainer key._1

  choice Go : ()
    with actor : Party
    controller actor
    do
      exercise cid Act
      create this with admin = admin
      return ()

  interface instance I for T where
    view = V with admin = admin
`),
  ]);
  const g = buildGraph(proj, { source: 'project-source' });
  const ids = new Set(g.nodes.map((n) => n.id));
  for (const e of g.edges) {
    assert.ok(ids.has(e.source), `edge source ${e.source} has a node`);
    assert.ok(ids.has(e.target), `edge target ${e.target} has a node`);
  }
  assert.equal(g.meta.module, null);
  assert.deepEqual(g.meta.modules, ['Iface', 'T']);
});
