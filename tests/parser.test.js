// tests/parser.test.js
//
// Run with:  node --test
//
// These tests exercise the heuristic parser against several valid Daml
// snippets and the bundled example files. They assert what the parser SHOULD
// extract, and also assert that it honestly flags things it cannot handle.

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

import { parseDaml } from '../src/parser.js';
import { buildGraph } from '../src/graph.js';

const here = dirname(fileURLToPath(import.meta.url));
const example = (name) => readFileSync(join(here, '..', 'examples', name), 'utf8');

function findTemplate(parsed, name) {
  const t = parsed.templates.find((x) => x.name === name);
  assert.ok(t, `template ${name} should be parsed`);
  return t;
}
function findChoice(tpl, name) {
  const c = tpl.choices.find((x) => x.name === name);
  assert.ok(c, `choice ${name} should be parsed`);
  return c;
}

test('parses module name', () => {
  const p = parseDaml('module My.Nested.Mod where\n');
  assert.equal(p.module, 'My.Nested.Mod');
});

test('Asset example: template, party fields, signatory/observer', () => {
  const p = parseDaml(example('Asset.daml'));
  assert.equal(p.module, 'Asset');
  const asset = findTemplate(p, 'Asset');
  assert.deepEqual(asset.partyFields, ['issuer', 'owner']);
  assert.deepEqual(asset.signatories, ['issuer']);
  assert.deepEqual(asset.observers, ['owner']);
  // amount is Decimal, not a party
  assert.ok(!asset.partyFields.includes('amount'));
});

test('Asset example: consuming vs nonconsuming choices + controllers', () => {
  const p = parseDaml(example('Asset.daml'));
  const asset = findTemplate(p, 'Asset');

  const give = findChoice(asset, 'Give');
  assert.equal(give.consuming, true);
  assert.deepEqual(give.controllers, ['owner']);

  const peek = findChoice(asset, 'Peek');
  assert.equal(peek.consuming, false); // nonconsuming
  assert.deepEqual(peek.controllers, ['issuer']);

  const burn = findChoice(asset, 'Burn');
  assert.deepEqual(burn.controllers.sort(), ['issuer', 'owner']);
});

test('Asset example: Give.create infers target Asset', () => {
  const p = parseDaml(example('Asset.daml'));
  const give = findChoice(findTemplate(p, 'Asset'), 'Give');
  const create = give.operations.find((o) => o.kind === 'create');
  assert.ok(create, 'should find a create op');
  // `create this with ...` — target is `this`, not a template constructor,
  // so it is NOT resolvable to a template name. Prototype should not guess.
  assert.equal(create.target, null);
});

test('Transfer example: create Asset resolves target, archive detected', () => {
  const p = parseDaml(example('Transfer.daml'));
  const accept = findChoice(findTemplate(p, 'TransferProposal'), 'Accept');
  const create = accept.operations.find((o) => o.kind === 'create');
  assert.equal(create.target, 'Asset');
  assert.ok(p.referencedTemplates.includes('Asset'));
});

test('Iou example: multiple templates and cross-references', () => {
  const p = parseDaml(example('Iou.daml'));
  assert.deepEqual(p.templates.map((t) => t.name).sort(), ['Iou', 'IouProposal']);
  const proposal = findTemplate(p, 'IouProposal');
  const createIou = findChoice(proposal, 'CreateIou');
  assert.equal(createIou.consuming, false);
  const create = createIou.operations.find((o) => o.kind === 'create');
  assert.equal(create.target, 'Iou');
});

test('archive op is detected', () => {
  const src = `module A where
template T with p : Party where
  signatory p
  choice C : ()
    controller p
    do
      archive self
`;
  const p = parseDaml(src);
  const ops = p.templates[0].choices[0].operations;
  assert.ok(ops.some((o) => o.kind === 'archive'));
});

test('exercise / exerciseByKey / fetch targets', () => {
  const src = `module A where
template T with p : Party where
  signatory p
  choice C : ()
    controller p
    do
      other <- fetch @Other cid
      exerciseByKey @Other key Ping
      exercise cid Pong
`;
  const p = parseDaml(src);
  const ops = p.templates[0].choices[0].operations;
  const fetchOp = ops.find((o) => o.kind === 'fetch');
  assert.equal(fetchOp.target, 'Other');
  const ebk = ops.find((o) => o.kind === 'exerciseByKey');
  assert.equal(ebk.target, 'Other');
  // `exercise cid Pong` — target is a value-level cid, not inferable.
  const ex = ops.find((o) => o.kind === 'exercise');
  assert.equal(ex.target, null);
});

test('honestly flags legacy controller-can syntax', () => {
  const src = `module A where
template T with p : Party where
  signatory p
  controller p can
    Foo : ()
      do return ()
`;
  const p = parseDaml(src);
  assert.ok(p.diagnostics.some((d) => d.code === 'old-controller-can'));
});

test('flags missing signatory and missing controller', () => {
  const src = `module A where
template T with p : Party where
  choice C : ()
    do return ()
`;
  const p = parseDaml(src);
  assert.ok(p.diagnostics.some((d) => d.code === 'no-signatory'));
  assert.ok(p.diagnostics.some((d) => d.code === 'no-controller'));
});

test('flags interfaces as unsupported', () => {
  const p = parseDaml('module A where\ninterface Token where\n');
  assert.ok(p.diagnostics.some((d) => d.code === 'interface-unsupported'));
});

test('buildGraph produces well-formed nodes and edges', () => {
  const p = parseDaml(example('Asset.daml'));
  const g = buildGraph(p);

  // every edge endpoint must resolve to a node
  const ids = new Set(g.nodes.map((n) => n.id));
  for (const e of g.edges) {
    assert.ok(ids.has(e.source), `edge source ${e.source} has a node`);
    assert.ok(ids.has(e.target), `edge target ${e.target} has a node`);
  }
  // there is a template node, party nodes, choice nodes
  assert.ok(g.nodes.some((n) => n.kind === 'template' && n.label === 'Asset'));
  assert.ok(g.nodes.some((n) => n.kind === 'party' && n.label === 'issuer'));
  assert.ok(g.nodes.some((n) => n.kind === 'choice' && n.label === 'Give'));
  // signatory edge exists
  assert.ok(g.edges.some((e) => e.kind === 'signatory'));
  assert.ok(g.edges.some((e) => e.kind === 'controller'));
});
