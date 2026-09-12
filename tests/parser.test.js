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

test('Asset example: `create this` resolves to the enclosing template', () => {
  const p = parseDaml(example('Asset.daml'));
  const give = findChoice(findTemplate(p, 'Asset'), 'Give');
  const create = give.operations.find((o) => o.kind === 'create');
  assert.ok(create, 'should find a create op');
  // `create this with ...` inside template Asset definitionally creates an
  // Asset. This is resolution, not a guess, and it is flagged as such.
  assert.equal(create.target, 'Asset');
  assert.equal(create.selfCreate, true);
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
  // `exercise cid Pong` - target is a value-level cid, not inferable.
  const ex = ops.find((o) => o.kind === 'exercise');
  assert.equal(ex.target, null);
});

test('dotted record projections stay one party, comma-separated split into many', () => {
  const src = `module A where
template CoinAllocation with registry : Party, spec : AllocationSpecification where
  signatory registry, spec.transferLeg.sender
  observer spec.settlement.executor, spec.transferLeg.receiver
`;
  const t = parseDaml(src).templates[0];
  // NOT split on the dots - projection is a single party reference
  assert.deepEqual(t.signatories, ['registry', 'spec.transferLeg.sender']);
  assert.deepEqual(t.observers, ['spec.settlement.executor', 'spec.transferLeg.receiver']);

  const g = buildGraph(parseDaml(src));
  // projected refs become derived party nodes with signatory/observer edges
  assert.ok(g.nodes.some((n) => n.kind === 'party' && n.label === 'spec.transferLeg.sender' && n.meta && n.meta.derived));
  assert.ok(g.edges.some((e) => e.kind === 'signatory' && e.target === 'party:CoinAllocation.spec.transferLeg.sender'));
});

test('list-literal observers unwrap into multiple parties', () => {
  const src = `module A where
template T with a : Party, b : Party where
  signatory a
  observer [a, b]
`;
  const t = parseDaml(src).templates[0];
  assert.deepEqual(t.observers, ['a', 'b']);
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

test('interfaces: declaration, viewtype, and choices are modeled', () => {
  const src = `module A where
interface Token where
  viewtype TokenView

  transferImpl : ContractId Token -> Party -> Update (ContractId Token)

  choice Transfer : ContractId Token
    with newOwner : Party
    controller (view this).admin
    do
      transferImpl this self newOwner

  nonconsuming choice Peek : Decimal
    controller (view this).admin
    do
      return 1.0
`;
  const p = parseDaml(src);
  assert.equal(p.interfaces.length, 1);
  const iface = p.interfaces[0];
  assert.equal(iface.name, 'Token');
  assert.equal(iface.viewtype, 'TokenView');
  assert.deepEqual(iface.choices.map((c) => c.name), ['Transfer', 'Peek']);
  assert.equal(iface.choices[0].consuming, true);
  assert.equal(iface.choices[1].consuming, false);
  // `(view this).admin` is one party, recorded as a view projection
  assert.deepEqual(iface.choices[0].controllers, ['view.admin']);
  assert.ok(iface.methods.includes('transferImpl'));
  // interfaces are no longer reported as unsupported
  assert.ok(!p.diagnostics.some((d) => d.code === 'interface-unsupported'));
});

test('interface instance blocks record which interfaces a template implements', () => {
  const src = `module A where
template Tok
  with
    admin : Party
    amount : Decimal
  where
    signatory admin

    choice Burn : ()
      controller admin
      do return ()

    interface instance Holding for Tok where
      view = HoldingView with owner = admin

    interface instance Utxo for Tok where
      view = UtxoView with admin = admin
`;
  const p = parseDaml(src);
  const t = findTemplate(p, 'Tok');
  assert.deepEqual(t.implements.sort(), ['Holding', 'Utxo']);
  // `interface instance` must NOT be mistaken for an interface declaration
  assert.equal(p.interfaces.length, 0);
  // both are declared elsewhere, and that is reported
  assert.ok(p.diagnostics.some((d) => d.code === 'external-interface'));
  // the instance body's `view = … owner = admin` must not become a signatory
  assert.deepEqual(t.signatories, ['admin']);

  const g = buildGraph(p);
  assert.equal(g.edges.filter((e) => e.kind === 'implements').length, 2);
  assert.ok(g.nodes.some((n) => n.kind === 'interface' && n.label === 'Holding' && n.meta.external));
});

test('`this.field` controllers resolve to the template field, not a choice arg', () => {
  const src = `module A where
template T
  with
    admin : Party
  where
    signatory admin

    choice C : ()
      controller this.admin
      do return ()
`;
  const t = parseDaml(src).templates[0];
  assert.deepEqual(t.choices[0].controllers, ['admin']);

  const g = buildGraph(parseDaml(src));
  // resolves to the real party field node, NOT a `#arg` placeholder
  assert.ok(g.edges.some((e) => e.kind === 'controller' && e.target === 'party:T.admin'));
  assert.ok(!g.nodes.some((n) => n.id.endsWith('#arg')));
});

test('contract keys: multi-line key, type annotation, positional maintainer', () => {
  const src = `module A where
template M
  with
    admin : Party
    contractData : Data
  where
    signatory admin

    key (admin, contractData.relationshipId,
         if contractData.backdated == Some True then Some d else None)
      : (Party, Text, Optional Time)
    maintainer key._1

    choice C : ()
      controller admin
      do return ()
`;
  const t = parseDaml(src).templates[0];
  assert.ok(t.key, 'key should be parsed');
  assert.equal(t.key.type, '(Party, Text, Optional Time)');
  // `key._1` resolves positionally to the first key component
  assert.deepEqual(t.key.maintainers, ['admin']);
  assert.deepEqual(t.key.parties, ['admin']);

  const g = buildGraph(parseDaml(src));
  assert.ok(g.nodes.some((n) => n.kind === 'key' && n.template === 'M'));
  assert.ok(g.edges.some((e) => e.kind === 'keyed-by'));
  assert.ok(g.edges.some((e) => e.kind === 'maintainer' && e.target === 'party:M.admin'));
});

test('key without maintainer is flagged', () => {
  const src = `module A where
template M with admin : Party where
  signatory admin
  key admin : Party
`;
  const p = parseDaml(src);
  assert.ok(p.diagnostics.some((d) => d.code === 'key-no-maintainer'));
});

test('lookupAllByKey is recognized as a read operation', () => {
  const src = `module A where
template T with p : Party where
  signatory p
  choice C : ()
    controller p
    do
      rows <- lookupAllByKey @Other (p, "x")
      return ()
`;
  const ops = parseDaml(src).templates[0].choices[0].operations;
  const op = ops.find((o) => o.kind === 'lookupAllByKey');
  assert.ok(op, 'lookupAllByKey should be detected');
  assert.equal(op.target, 'Other');
  // must not also be double-counted as a plain `lookupByKey`
  assert.ok(!ops.some((o) => o.kind === 'lookupByKey'));
});

test('module-qualified exercise recovers the choice name and module hint', () => {
  const src = `module A where
template T with p : Party where
  signatory p
  choice C : ()
    controller p
    do
      mapA_ (\cid -> exercise cid ArBorrowingBase.ArchiveSubtypeToken) cids
`;
  const ops = parseDaml(src).templates[0].choices[0].operations;
  const ex = ops.find((o) => o.kind === 'exercise');
  assert.equal(ex.target, null, 'target template is not syntactically present');
  assert.equal(ex.choice, 'ArchiveSubtypeToken');
  assert.equal(ex.moduleHint, 'ArBorrowingBase');
});

test('top-level helper functions and their operations are parsed', () => {
  const src = `module A where

template Mirror with admin : Party where
  signatory admin

  choice Make : ()
    controller admin
    do
      upsertMirror admin
      return ()

upsertMirror : Party -> Update (ContractId Mirror)
upsertMirror admin = do
  create Mirror with admin = admin
`;
  const p = parseDaml(src);
  const fn = p.functions.find((f) => f.name === 'upsertMirror');
  assert.ok(fn, 'helper defined after a template should still be found');
  assert.ok(fn.operations.some((o) => o.kind === 'create' && o.target === 'Mirror'));
  // the calling choice records the reference used to reach it
  const ch = findChoice(findTemplate(p, 'Mirror'), 'Make');
  assert.ok(ch.refs.includes('upsertMirror'));
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

test('party expressions split on cons and semigroup operators', () => {
  // `signatory admin :: optionalParty governance.approvalParty` previously
  // yielded only `admin`, under-reporting stakeholders across a whole repo.
  const src = `module A where
template T
  with
    admin : Party
    owner : Party
    governance : GovernanceParties
  where
    signatory admin :: optionalParty governance.approvalParty
    observer owner :: optionalParty governance.registrar <> optionalParty governance.controllerParty
`;
  const t = parseDaml(src).templates[0];
  assert.deepEqual(t.signatories, ['admin', 'governance.approvalParty']);
  assert.deepEqual(t.observers, [
    'owner',
    'governance.registrar',
    'governance.controllerParty',
  ]);
});

test('an applied party helper resolves to its argument, not the function', () => {
  const src = `module A where
template T with governance : GovernanceParties where
  signatory optionalParty governance.approver
`;
  const t = parseDaml(src).templates[0];
  assert.deepEqual(t.signatories, ['governance.approver']);
});

test('interface instance view bindings handle punning and nesting', () => {
  const src = `module A where
template Tok
  with
    admin : Party
    owner : Party
    amount : Decimal
    contractLock : Lock
  where
    signatory admin
    observer owner

    interface instance Utxo for Tok where
      view = UtxoView with
        holding = HoldingView with
          owner
          amount
        admin
        lock = Some contractLock
`;
  const t = parseDaml(src).templates[0];
  assert.equal(t.interfaceInstances.length, 1);
  const inst = t.interfaceInstances[0];
  assert.equal(inst.interface, 'Utxo');
  assert.equal(inst.viewType, 'UtxoView');
  // `admin` alone is record punning for `admin = admin`
  assert.equal(inst.viewBindings.admin, 'admin');
  assert.equal(inst.viewBindings.lock, 'Some contractLock');
  // a nested record is recorded as nested, not mis-parsed into a binding
  assert.deepEqual(inst.nestedViewFields, ['holding']);
  assert.ok(!('holding' in inst.viewBindings));
  assert.ok(!('owner' in inst.viewBindings), 'nested fields must not leak to the top level');
});

test('single-line view bindings are parsed', () => {
  const src = `module A where
template Tok with admin : Party, amount : Decimal where
  signatory admin
  interface instance Utxo for Tok where
    view = UtxoView with admin, amount = amount
`;
  const inst = parseDaml(src).templates[0].interfaceInstances[0];
  assert.equal(inst.viewBindings.admin, 'admin');
  assert.equal(inst.viewBindings.amount, 'amount');
});
