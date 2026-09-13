# Daml Access Graph

A small, framework-free visualizer for the **access structure** of Daml
templates. Paste Daml source and it extracts templates, interfaces, `Party`
fields, signatories, observers, contract keys and their maintainers, choices
(consuming vs. nonconsuming), controllers, and the ledger operations each
choice performs (`create`, `exercise`, `fetch`, …), then renders them as an
interactive graph.

Three ingest modes, one output schema:

| Mode | Needs the SDK? | Resolves cross-module references? | Sound? |
| --- | --- | --- | --- |
| single file (paste / one `.daml`) | no | no | no, heuristic |
| **project** (a repo of `.daml` files) | no | yes | no, heuristic |
| **Daml-LF** (a built `.dar`) | **no** | within the package | yes |

Nothing here needs a Daml toolchain any more. The LF path decodes the DAR's
protobuf directly (see [Daml-LF backend](#daml-lf-extraction-backend)), and
project mode decodes any DARs it finds under the roots so that interfaces
declared in imported packages resolve too.

Project mode is what you want on a real repository: cross-module `exercise`
targets, interfaces declared in sibling modules, and ledger operations
performed by shared helper functions only resolve when every module is in hand
at once. See [Project mode](#project-mode).

> ⚠️ **The browser parser is a prototype, not a sound Daml frontend.** It uses
> regexes and indentation heuristics. It will miss or misread some valid Daml.
> Everywhere it gives up or guesses, it emits a **diagnostic** so the UI can be
> honest about what it does and doesn't understand. For anything load-bearing,
> use the planned Daml-LF backend (see [Roadmap](#roadmap)).

## Running locally

No build step, no dependencies. You only need a static file server (ES modules
don't load over `file://`).

```bash
cd daml-access-graph

# any static server works; pick one:
npm run serve                 # python3 -m http.server 8000
# or
npx serve .
# or
python3 -m http.server 8000
```

Then open <http://localhost:8000>.

Pick a built-in example from the dropdown, or paste your own Daml into the
left pane and click **Analyze ▶**. The graph, diagnostics, and the normalized
graph JSON update together.

## Tests

The parser has a test suite using Node's built-in test runner (no deps):

```bash
npm test        # node --test
```

Tests cover the bundled examples plus targeted snippets, including cases the
tool is expected to **flag rather than resolve**:

- [`tests/parser.test.js`](tests/parser.test.js) - templates, interfaces,
  contract keys, party-reference normalization, helper-function discovery
- [`tests/project.test.js`](tests/project.test.js) - cross-module resolution,
  ambiguity refusal, name collisions, the helper call graph
- [`tests/analysis.test.js`](tests/analysis.test.js) - every analysis family,
  plus the false-positive cases that must stay silent
- [`tests/dalf.test.js`](tests/dalf.test.js) - the protobuf and zip readers,
  and the Daml-LF 2 field numbers, asserted against an in-memory DALF built
  field by field (no third-party DAR is vendored)
- [`tests/diff.test.js`](tests/diff.test.js) - the diff's widening/narrowing
  classification, and that a baseline round-trip is exactly clean
- [`tests/codegen.test.js`](tests/codegen.test.js) - that the generated schema
  matches the vendored protos, that the confusable field numbers are the ones
  the proto states, and that every message in the real schema survives a wire
  round-trip
- [`tests/lf-parser.test.js`](tests/lf-parser.test.js) - the legacy text backend

## Project layout

```
daml-access-graph/
├── index.html              # UI shell
├── styles.css
├── src/
│   ├── parser.js           # (A) Daml source -> structural model (heuristic)
│   ├── project.js          # (B) many files -> one model, cross-module resolution
│   ├── callgraph.js        # helper-function operations -> calling choices
│   ├── diff.js             # compare two graphs, classify widening/narrowing
│   ├── baseline.js         # the committed accepted-state record for CI
│   ├── graph.js            # structural model -> normalized graph JSON (shared)
│   ├── analysis.js         # static analyses over the graph IR (shared)
│   ├── view.js             # collapse, filter, focus, hidden-accounting (pure)
│   ├── layout.js           # deterministic force and layered layouts (pure)
│   ├── renderer.js         # normalized graph -> interactive SVG (drawing only)
│   └── app.js              # wiring: read -> parse -> build -> analyze -> render
├── backend/                # Node CLIs and the compiled-package reader
│   ├── verify.js           # CLI: prove properties of a DAR via SMT (cvc5/z3)
│   ├── lfir.js             # LF expressions -> guarded-transition IR (total)
│   ├── smt.js              # IR -> SMT-LIB 2 queries + property definitions
│   ├── check.js            # CLI: the CI gate (baseline compare, graph diff)
│   ├── extract-project.js  # CLI: a repo of .daml (+ its DARs) -> graph JSON
│   ├── extract-dar.js      # (C) CLI: DAR -> graph JSON
│   ├── dalf.js             # decodes a DAR/DALF protobuf -> structural model
│   ├── lf2-schema.js        # aliases + semantics only, NO field numbers
│   ├── lf2-schema.generated.js  # GENERATED from the vendored protos
│   ├── proto/               # vendored official schemas + PROVENANCE.md
│   ├── protobuf.js         # minimal protobuf wire-format reader
│   ├── zip.js              # minimal zip reader (node:zlib, no `unzip`)
│   ├── lf-parser.js        # legacy: parses `damlc inspect` text
│   └── dar.js              # legacy: DAR manifest via `unzip`
├── examples/               # sample .daml files (also used by tests)
│   ├── Asset.daml
│   ├── Transfer.daml
│   ├── Iou.daml
│   ├── TokenInterface.daml # interfaces + keys + helper-function indirection
│   └── ConfidentialAuction.daml
├── tools/                  # build-time only, not shipped to the browser
│   ├── proto-parse.js      # a proto3 parser for the subset the schemas use
│   └── codegen.js          # proto -> lf2-schema.generated.js
├── tests/
│   ├── parser.test.js      # source parser
│   ├── project.test.js     # project mode + call graph
│   ├── analysis.test.js    # static analyses
│   ├── codegen.test.js     # schema drift, grounding, wire round-trip
│   ├── dalf.test.js        # protobuf/zip readers + LF2 field numbers
│   ├── diff.test.js        # graph diff + CI baseline
│   ├── verify.test.js      # IR helpers, SMT emitter, live cvc5 proofs
│   ├── lf-parser.test.js   # legacy text backend (fixtures/Asset.lf.txt)
│   └── fixtures/Asset.lf.txt
└── package.json
```

## What the parser extracts

| Feature | Support |
| --- | --- |
| `module` name | ✅ |
| templates | ✅ |
| `Party` fields (incl. `[Party]`, `Optional Party`) | ✅ |
| signatories / observers | ✅ (resolved to party fields) |
| `choice` / `nonconsuming choice` | ✅ |
| consuming vs. nonconsuming | ✅ |
| controllers (`choice … controller …` form) | ✅ |
| `create`, `createAndExercise` | ✅ + target inference |
| `exercise`, `exerciseByKey` | ✅ (`@Template` / `ByKey` inferable) |
| `fetch`, `fetchByKey`, `lookupByKey` | ✅ (target inferable via `@`) |
| `archive` | ✅ (target usually not inferable) |
| referenced target templates | ✅ (best-effort) |
| legacy `controller … can` blocks | ⚠️ flagged, partial |
| interfaces | ⚠️ flagged, not modeled |
| generic instances / advanced type-level code | ❌ ignored |

Target-template inference is heuristic: `create Foo with …` resolves to `Foo`,
`fetch @Foo cid` resolves to `Foo`, but `exercise cid SomeChoice` sees only a
value-level contract id and is reported as ambiguous rather than guessed.

## Normalized graph schema

Both this browser parser and the future Daml-LF backend emit the **same**
JSON shape, so the renderer (and any static analysis) can consume either:

```jsonc
{
  "meta": {
    "module": "Asset",          // string | null
    "source": "browser-prototype", // provenance of this graph
    "warnings": ["..."]          // human-readable warnings (from diagnostics)
  },
  "nodes": [
    {
      "id": "tpl:Asset",         // stable, unique
      "kind": "template",        // "template" | "party" | "choice"
      "label": "Asset",
      "meta": { "external": false }
    },
    {
      "id": "party:Asset.owner",
      "kind": "party",
      "label": "owner",
      "template": "Asset"        // owning template
    },
    {
      "id": "choice:Asset.Give",
      "kind": "choice",
      "label": "Give",
      "template": "Asset",
      "meta": { "consuming": true }
    }
  ],
  "edges": [
    {
      "id": "e0",
      "source": "tpl:Asset",     // node id
      "target": "party:Asset.owner",
      "kind": "observer",        // see edge kinds below
      "label": "observer"
    }
  ]
}
```

**Node kinds**

`template`, `interface`, `party`, `choice`, `key`.

**Node id conventions**

- `tpl:<Template>`
- `iface:<Interface>`
- `party:<Owner>.<field>` (or `party:<Owner>.<name>#arg` for a party that comes
  from a choice argument, or from a projection into a non-`Party` field, rather
  than a template party field)
- `choice:<Owner>.<Choice>` - `<Owner>` is a template *or* an interface
- `key:<Template>`

In **project mode**, a name declared in more than one module is qualified as
`Module:Name` (so `tpl:Internal.Fees:FeeRecord`), and only then - unique names
stay bare, which keeps ids stable between single-file and project mode. Choice
nodes carry `owner` and `ownerKind` (`template` | `interface`), and nodes carry
`module` where it is known.

**Edge kinds**

- Structural: `declares` (template/interface → choice), `signatory`, `observer`
  (template → party), `controller` (choice → party), `view-controller`
  (interface choice → a party of one implementing template), `implements`
  (template → interface), `keyed-by` (template → key), `maintainer`
  (key → party).
- Operational: `create`, `createAndExercise`, `exercise`, `exerciseByKey`,
  `fetch`, `fetchByKey`, `lookupByKey`, `lookupAllByKey`, `archive`
  (choice → target template/interface).

An operational edge may carry `meta`:

- `meta.via` - the helper-function call path the operation was reached through
  (see [Project mode](#project-mode)). Absent means the operation appears
  directly in the choice body.
- `meta.resolvedVia` - how a target with no name at the call site was resolved,
  e.g. `project-choice-lookup`.

An `implements` edge carries `meta.viewType` and `meta.viewBindings` (the
implementing template's `view` record). A `view-controller` edge carries
`meta.template`, `meta.viewField`, `meta.expr`, and `meta.heuristic` when the
view field was bound to an applied expression rather than a plain reference.

Every edge's `source` and `target` are guaranteed to reference an existing
node id (asserted in the tests, for both single-file and project mode).

## Architecture

Three front-ends produce the **same** normalized graph JSON; everything
downstream (renderer, analyses) consumes that one schema:

```
 (A) quick preview      (B) project mode          (C) sound backend
 ─────────────────      ────────────────          ─────────────────
 one Daml source        a repo of .daml files     .daml files
     │                       │                        │  daml build
     │                       ▼                        ▼
     │                  src/parser.js  (per file)  DAR (compiled Daml-LF)
     │                       │                        │  damlc inspect
     ▼                       ▼                        ▼
 src/parser.js          src/project.js            backend/lf-parser.js
 (regex heuristics)     - name/collision index    (parses Daml-LF text)
     │                  - choice -> declarer            │
     │                  - interface index               │
     │                       │                          │
     │                       ▼                          │
     └──── src/callgraph.js (helper fns -> callers) ─────┤
                             │                          │
                             ▼                          ▼
                      Structural model  ◄───────────────┘
                             │
                             ▼
            src/graph.js  ──▶  Normalized graph JSON
                             │   meta.source: browser-prototype
                             │                | project-source
                             │                | daml-lf
                     ┌───────┴────────┐
                     ▼                ▼
               src/renderer.js   src/analysis.js
               (interactive SVG) (authorization / visibility /
                                  information-flow / keys / interfaces)
```

## Project mode

Point it at a checkout. No SDK, no build.

```bash
node backend/extract-project.js path/to/repo --analyze --stats --out graph.json
node backend/extract-project.js path/to/repo --no-tests --min-severity warning
node backend/extract-project.js dir-a dir-b --suppress no-observers,terminal-template
```

Then open the app and use **Load graph JSON**. In the browser you can also pick
several `.daml` files at once with **Load .daml file(s)** and they are parsed as
one project.

Three things resolve here that cannot resolve from a single file:

**1. Cross-module operation targets.** `exercise cid Foo` names a choice, not a
template. Project mode indexes every choice to its declaring template or
interface and resolves the target - or reports it as ambiguous when several
templates declare that name. A module-qualified call site (`exercise cid
ArBorrowingBase.ArchiveSubtypeToken`) uses the qualifier to disambiguate.

**2. Interfaces declared elsewhere.** `interface instance Holding for Tok`
links to the real `Holding` declaration when it is in a sibling module, and is
marked external - with a warning that the exercisable surface is
*under*-reported - only when it genuinely comes from an imported DAR.

**3. Operations inside helper functions.** Idiomatic Canton code keeps choice
bodies thin:

```haskell
-- Factory.daml
choice CreateTenantMirror : ContractId TenantMirror.TenantMirror
  with contractData : TenantMirror.TenantData
  controller admin
  do Upsert.tenantMirror admin approver reader contractData

-- Internal/Upsert.daml
tenantMirror admin approver reader contractData = do
  create TenantMirror.TenantMirror with ...
```

A parser that only reads choice bodies sees no operation at all here.
[`src/callgraph.js`](src/callgraph.js) walks from each choice through the
helpers it references, transitively, and records what it reaches as
`inheritedOperations` - each carrying the `via` call path that justifies it, so
a direct `create` stays distinguishable from one two calls away.

Measured on a 27-package, 76-module Canton repository, project mode plus the
call graph took the graph from 2 `create` edges and 1 `exercise` edge to 58 and
29 respectively, and cut residual "could not infer target" diagnostics from 32
to 0 (the 27 that remain all say, correctly, that the choice is declared in an
imported DAR).

### Honest limits of project mode

- Reference collection for the call graph is **name-based**. A local binding
  that shares a top-level helper's name can produce a spurious edge. Every
  inherited edge carries `via`, so it is auditable rather than invisible.
- Higher-order calls (a helper passed as an argument) are not followed.
- A bare helper name defined in several modules is **not** followed at all,
  rather than resolved by guess.
- Everything the single-file parser cannot do soundly, project mode also cannot
  do soundly. It resolves *references*; it does not typecheck.

## Daml-LF extraction backend

For a package you have already built, the graph can come from the compiled
artifact instead of the source:

```bash
node backend/extract-dar.js path/to/project.dar --analyze --out graph.json
```

No Daml SDK required. This decodes the DAR's Daml-LF protobuf directly:

```
 foo.dar  (zip)
   |  backend/zip.js        central directory + node:zlib, no `unzip` binary
   v
 main .dalf  (protobuf)
   |  backend/protobuf.js   wire-format reader
   |  backend/lf2-schema.js field numbers from the official daml_lf2.proto
   v
 backend/dalf.js  ->  structural model  ->  src/graph.js  ->  graph JSON
                                                      meta.source = "daml-lf"
```

What it recovers: package name/version/id and LF version, module names,
templates with their signatories and observers, choices with their consuming
flag and controllers, contract keys, `implements` relationships, and the
ledger operations each choice performs with targets resolved from the compiled
`Update` nodes (so no target is ever guessed).

### The schema is generated, not transcribed

No field number in the decoder is hand-copied. The official protos are vendored
under [`backend/proto/`](backend/proto/) with their provenance recorded, and
`backend/lf2-schema.generated.js` is produced from them:

```bash
npm run codegen        # proto -> generated schema
npm test               # fails if the committed generated file is stale
```

`backend/lf2-schema.js` is now a thin layer holding only what a schema cannot
tell you: aliases from the decoder's names to fully qualified message names,
and the semantic mapping from `Update` cases to access-graph operation kinds.
A wrong alias throws at import; a wrong field number would not.

That distinction is the whole point, because two traps here fail SILENTLY:

- **Daml-LF 2 renumbered nearly every field** relative to LF 1. The LF1 proto,
  and the `daml_lf2.proto` shipped at Daml 2.x tags (which still carried LF1
  numbering), do not apply. A decoder built on those produces nonsense on a
  real LF 2.x package, with no error.
- `Expr.RecProj` and `Expr.RecUpd` are near-identical messages that put
  `field_interned_str` in different slots (4 and 2), and `FieldWithExpr` puts
  it in a third (3). Reading RecProj with RecUpd's number throws nothing: every
  signatory, observer and controller expression simply comes back empty, so a
  package decodes "successfully" with no stakeholders at all. This was a real
  bug during development, and generation removes the class of it.

Three layers of checking, in [`tests/codegen.test.js`](tests/codegen.test.js):

| Check | What it catches |
| --- | --- |
| drift | a proto updated without regenerating, or a hand-edited generated file |
| grounding | the confusable numbers are re-read from the proto and compared |
| round-trip | every message in the real schema encodes and decodes back, so the wire reader is exercised against the actual shapes Daml-LF uses rather than a toy |

The generated decoder was also checked differentially against the hand-written
one it replaced: on a real 13-module Canton package it produces an identical
node set, an identical edge set, and identical findings.

### Reading a repo's bundled DARs

Project mode decodes any `.dar` under its roots, which is what makes an
interface declared in an imported package resolve. On the tokens repo, whose
CIP-56 Splice interfaces ship as three vendored DARs:

| | DARs ignored (`--no-dars`) | DARs decoded (default) |
| --- | --- | --- |
| interfaces in the graph | 1 | 1 + 4 imported |
| `declares` edges | 34 | 44 |
| `interface-choice-exercisable` | 2 | 19 |
| `template-external-interfaces-only` | 14 | 0 |
| `external-interface-surface` | 2 | 0 |

Without the DARs, 14 of 16 templates could only be reported as "implements
something we cannot see". With them, each interface choice is attributed to the
templates it is exercisable on, with its controller.

### Limits of the compiled path

The compiled form has lost things the source still has, and the tool says so
rather than reporting them as absent:

- **Key maintainers.** The key is found, but its maintainer expression often
  yields no field name from compiled form (`key-maintainer-unrecovered`). The
  source parser resolves `maintainer key._1` positionally, so prefer project
  mode when maintainer analysis matters.
- **`interface instance` view bindings.** The compiler rewrites the view record,
  so the view-field-to-template-field map that resolves `(view this).admin` is
  not recoverable from the DAR yet. Project mode reads it from source.
- **Projection roots.** The optimizer hoists `view this` into a let-binding, so
  some projection chains are rooted in a compiler-introduced variable rather
  than the parameter or the choice argument. Those are reported as bare field
  paths with a `party-root-unattributed` diagnostic instead of being guessed as
  `view.` or `#arg`.
- **Helper indirection** does not exist in compiled code: calls are inlined or
  hoisted into values, which the decoder follows, so there is no call graph to
  reconstruct.

The legacy `damlc inspect` text path is still available for comparison:

```bash
node backend/extract-dar.js foo.dar --damlc          # needs the SDK on PATH
daml damlc inspect foo.dar > dump.lf
node backend/extract-dar.js --lf-file dump.lf        # parse a saved dump
```

**View backend output in the browser:** click **Load graph JSON** in the app
and pick a file either CLI wrote. The same visualizer renders it, and if the
file was produced with `--analyze`, its findings show in the Static analysis
panel.

## Verification

`backend/verify.js` proves properties of a compiled package with an SMT solver
(cvc5 by default; z3 works too):

```bash
node backend/verify.js path/to/package.dar
node backend/verify.js pkg.dar --property amount-conservation --template RecToken
```

```
DAR --readDarRaw--> LF protobuf --lfir.js--> guarded transitions --smt.js--> query --cvc5--> verdict
```

The point of deriving the model from the DAR, rather than writing it by hand
next to the code, is the correspondence gap: a hand-written symbolic model
proves things about the MODEL, and "does the model match the contract?" stays
an unproven comment. Here the transition system is extracted from the compiled
package - beta-reducing the hoisted choice workers, chasing create arguments to
their call-site record constructions - so the correspondence holds by
construction for the translated fragment, and the fragment's edges are
machine-reported (`NOT-MODELLABLE` with a reason), never elided.

Verdicts: `PROVED` (unsat - no counterexample exists), `DISPROVED` (a concrete
counterexample, printed), `NOT-MODELLABLE`, `NOT-APPLICABLE`, `SOLVER-UNKNOWN`.

Measured on a real Canton token package (16 templates, 48 choices):

| Verdict | Transitions | Meaning |
| --- | --- | --- |
| PROVED | 9 | every lock/unlock/convert choice preserves `amount` - the README claim "locked forms preserve the same amount", now a theorem |
| DISPROVED | 3 | the three admin `Set*Amount` choices do not conserve, with counterexamples (`newAmount = -1, amount = 0`) - true, they are mint/burn authority |

What `PROVED` does not mean, stated in the tool's own output:

- **Numeric 10 is modelled as exact `Real`.** Sound for division-safety, sign
  and ordering; unsound for exact equalities on paths that round. Transitions
  carrying rounding builtins are REFUSED for equality properties, not proved
  wrongly.
- **Untranslatable guards are dropped, and each drop is reported.** Dropping an
  assumption is sound for a universal proof (the property is proved over a
  superset of the reachable states); what it costs is completeness, and a
  DISPROVED whose counterexample might be excluded by a dropped `ensure` says
  so.
- **The translator is tested, not verified.** `lfir.js` is the trust root of
  this pipeline, exactly as `damlc` is the trust root of the ledger.

## Diffing and the CI gate

A graph tells you what the access structure IS. A diff tells you what a change
DID to it, which is the question a reviewer actually has. `backend/check.js`
does both.

```bash
# accept the current state, then commit the file
node backend/check.js daml/ --baseline access-baseline.json --update

# in CI
node backend/check.js daml/ --baseline access-baseline.json

# or compare two graphs directly, no baseline involved
node backend/check.js --diff before.json after.json
```

Exit codes are pipeline-shaped: `0` clean, `1` gate failed, `2` usage error.

### Widening vs. narrowing

Access-structure changes are not symmetric, so every change carries a
direction. Adding an observer, adding a controller, adding a choice, adding an
`implements`, or flipping a choice to consuming all WIDEN what some party can
see or do. Adding a signatory NARROWS it, because one more party must now
authorize. Removing a signatory widens, for the same reason in reverse.

The gate fails on widening by default (`--fail-on widening | findings | any |
never`), which is what makes it usable: a real repository starts with dozens of
legitimate informational findings, so "fail if there are findings" is noise.
What matters is whether *this change* added something.

A worked example. Adding this to a token template:

```haskell
choice SeizeRecToken : ContractId RecToken
  with seizer : Party
  controller owner
  do create this with owner = seizer
```

produces:

```
access structure vs baseline: 4 change(s) - 3 widening, 0 narrowing, 1 neutral

changes that WIDEN the access structure:
  WIDENS   RecToken -declares-> SeizeRecToken
  WIDENS   SeizeRecToken -controller-> owner
  WIDENS   SeizeRecToken -create-> RecToken

findings not in the baseline (1):
  [info] nonsignatory-consuming: Consuming choice RecToken.SeizeRecToken lets
         non-signatory party field(s) [owner] archive/replace the contract.
```

### The baseline file

A baseline records the accepted state: finding FINGERPRINTS (code plus subject
node ids, never message text, which gets reworded whenever the analysis
improves), the node and edge sets, and the handful of node properties that are
themselves access-relevant (a choice's consuming flag, a key's maintainers,
whether a declaration is external).

Two properties it is built to have:

- **A round-trip is exactly clean.** Comparing a tree against a baseline taken
  from that same tree reports zero changes. A gate that fires on an unchanged
  tree gets switched off, so this is asserted in the tests, including for the
  cases that need the preserved metadata (interfaces, keys, nonconsuming
  choices).
- **There is no blanket ignore.** Accepting a finding means it appears in the
  baseline by name, in a committed file, where a reviewer sees it in the PR.

Edges are matched on `source|kind|target`, never on `id`: ids are positional
(`e0`, `e1`, ...) and shift whenever anything earlier in the graph changes, so
comparing them would report the entire graph as churn.

## Static analyses

`src/analysis.js` runs five families over the normalized graph IR, so they work
on **any** front-end's output - though results are only as sound as the graph
feeding them:

| Family | Example findings |
| --- | --- |
| **authorization** | choices with no controller; consuming choices archivable by a non-signatory; `create X` where the acting authority may not cover `X`'s required signatories |
| **visibility** | templates with no observers (signatory-only visibility); party fields that control a choice without being declared stakeholders |
| **information-flow** | authority crossing a party boundary (choice acting as party A creates a contract signed by party B); contract-lifecycle cycles; lifecycle leaf templates |
| **keys** | key maintainers that are not signatories; keys with no resolvable maintainer; `lookupAllByKey` reads that may match several contracts |
| **interfaces** | which interface choices are exercisable on which implementing templates and under whose control, with view projections resolved to the implementing template's own fields; an interface choice whose resolved controller is neither signatory nor observer of the template; templates whose interfaces are declared outside the graph, so their exercisable surface is under-reported |

Findings are shown in the app's **Static analysis** panel and can be emitted by
either CLI with `--analyze` (added under an `analysis` key in the JSON).

### Precision

A finding list nobody reads is worth nothing, so `analyzeAll` returns a
`summary` (counts by code, severity, and category) and accepts filters:

```js
analyzeAll(graph, {
  suppress: ['no-observers', 'terminal-template'],
  minSeverity: 'warning',
});
```

Suppression is never silent: `summary.suppressed` records what was filtered and
how much of it, so a quiet report cannot be mistaken for a clean one. The CLI
exposes the same via `--suppress` and `--min-severity`, and `--stats` prints
the summary including a `SUPPRESSED` line.

Two fixes to the analyses themselves mattered more than any filter:

- **Choice-argument controllers are no longer treated as missing
  stakeholders.** `controller actor` where `actor` is a choice argument is
  supplied by the exercising party at call time; Daml makes it an observer of
  the exercise, and it is not expected in `signatory` / `observer`. Only a
  declared party *field* of the template is now compared against stakeholders.
- **`this.field` is normalized to `field`.** It is the dominant controller form
  in Canton codebases and denotes the same party; treating the two as distinct
  turned every such choice into a false positive.

Together these took one real 39-choice factory template from 42 findings
(37 of them bogus `controller-not-stakeholder`) to 5.

A third fix was about *under*-reporting rather than noise: party expressions
built with `::` and `<>` (`signatory admin :: optionalParty
governance.approvalParty`) were being read as just their first element. On the
tokens repo that hid half the signatory edges and two thirds of the observer
edges, which means every visibility finding there was computed on an incomplete
stakeholder set.

**Soundness limit we do not hide:** party nodes are keyed by *field name per
template* (`party:Asset.issuer`). The analyses cannot know whether `issuer` in
one template is the same ledger `Party` as `from` in another, so every
cross-template authority finding says so explicitly rather than asserting a
violation. True party-identity/dataflow analysis is future work on top of the
Daml-LF backend.

Interface-choice controllers are the one place this limit has been lifted.
`controller (view this).admin` used to be unplaceable, but each
`interface instance` writes down its own `view` record, so the projection is
joined to the implementing template's field:

```haskell
interface Utxo where
  choice Split_Utxo : [ContractId Holding]
    controller (view this).admin        -- which party is this?

template TransferableRecToken with admin : Party ... where
  interface instance Utxo for TransferableRecToken where
    view = UtxoView with
      admin                            -- this one: TransferableRecToken.admin
```

That resolution is exact when the view field is bound to a plain reference or a
record pun. When it is bound to a nested record or an applied expression, the
finding says which case it hit rather than asserting a party.

## Roadmap

1. ✅ Browser parser - fast, offline, no-toolchain preview.
2. ✅ Daml-LF extraction backend (`backend/`) - reads a compiled DAR, emits the
   same normalized graph JSON with sound target inference.
3. ✅ Static analyses on the graph IR - authorization, visibility,
   information-flow.
4. ✅ Interfaces, contract keys, and `lookupAllByKey` in the model and schema,
   with dedicated analysis families.
5. ✅ Project mode - whole-repository ingest, cross-module target resolution,
   name-collision handling, and helper-function attribution via a call graph.
6. ✅ Finding precision - severity filtering, explicit reported suppression,
   and removal of the choice-argument / `this.field` false positives.
7. ✅ Decode the DALF **protobuf** directly (no SDK, no reliance on the
   `damlc inspect` text format), covering interfaces, contract keys and
   `implements` the way the source parser does.
8. ⏳ Party-identity / dataflow analysis to turn heuristic cross-template
   authority findings into sound ones; add privilege-escalation checks.
9. ✅ Resolve view-projected interface controllers (`(view this).admin`) to the
   implementing template's fields by reading each `interface instance`'s `view`
   record, and check the resolved party against the template's stakeholders.
10. ✅ Read a package's bundled DARs so interfaces declared in an imported
   package (Splice `Holding`, `TransferFactory`, …) stop being reported as
   unknown externals.
11. ✅ Graph diff mode plus a CI gate with a baseline, so a PR that widens the
   access structure fails the build.
12. ⏳ Recover `interface instance` view bindings and key maintainers from
   compiled form, and follow let-bindings so every projection root is
   attributable.

## License

MIT
