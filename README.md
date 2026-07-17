# Daml Access Graph

A small, framework-free visualizer for the **access structure** of Daml
templates. Paste Daml source and it extracts templates, `Party` fields,
signatories, observers, choices (consuming vs. nonconsuming), controllers, and
the ledger operations each choice performs (`create`, `exercise`, `fetch`, …),
then renders them as an interactive graph.

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

Tests live in [`tests/parser.test.js`](tests/parser.test.js) and cover the
bundled examples plus targeted snippets, including cases the parser is
expected to flag rather than resolve.

## Project layout

```
daml-access-graph/
├── index.html              # UI shell
├── styles.css
├── src/
│   ├── parser.js           # (A) Daml source -> structural model (heuristic)
│   ├── graph.js            # structural model -> normalized graph JSON (shared)
│   ├── analysis.js         # static analyses over the graph IR (shared)
│   ├── renderer.js         # normalized graph -> interactive SVG (force layout)
│   └── app.js              # wiring: read -> parse -> build -> analyze -> render
├── backend/                # (B) sound Daml-LF pipeline (Node CLI)
│   ├── extract-dar.js      # CLI: DAR -> damlc inspect -> graph JSON [--analyze]
│   ├── lf-parser.js        # parses Daml-LF text -> structural model
│   └── dar.js              # reads DAR manifest metadata (via `unzip`)
├── examples/               # sample .daml files (also used by tests)
│   ├── Asset.daml
│   ├── Transfer.daml
│   └── Iou.daml
├── tests/
│   ├── parser.test.js      # browser parser
│   ├── lf-parser.test.js   # Daml-LF backend (uses fixtures/Asset.lf.txt)
│   ├── analysis.test.js    # static analyses
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

**Node id conventions**

- `tpl:<Template>`
- `party:<Template>.<field>` (or `party:<Template>.<name>#arg` for a party that
  comes from a choice argument rather than a template field)
- `choice:<Template>.<Choice>`

**Edge kinds**

- Structural: `declares` (template → choice), `signatory`, `observer`
  (template → party), `controller` (choice → party).
- Operational: `create`, `createAndExercise`, `exercise`, `exerciseByKey`,
  `fetch`, `fetchByKey`, `lookupByKey`, `archive` (choice → target template).

Every edge's `source` and `target` are guaranteed to reference an existing
node id (asserted in the tests).

## Architecture

Two front-ends produce the **same** normalized graph JSON; everything
downstream (renderer, analyses) consumes that one schema:

```
 (A) quick preview           (B) sound backend
 ─────────────────           ──────────────────
 Daml source                 .daml files
     │                            │  daml build
     ▼                            ▼
 src/parser.js               DAR (compiled Daml-LF)
 (regex heuristics)              │  damlc inspect
     │                            ▼
     │                       backend/lf-parser.js
     │                       (parses Daml-LF text)
     └──────────┬─────────────────┘
                ▼
       Structural model
                │
                ▼
       src/graph.js  ──▶  Normalized graph JSON  (meta.source: prototype | daml-lf)
                │
        ┌───────┴────────┐
        ▼                ▼
  src/renderer.js   src/analysis.js
  (interactive SVG) (authorization / visibility / information-flow)
```

## Daml-LF extraction backend

The browser parser is a heuristic **quick-preview mode**. For sound results,
`backend/` extracts the access graph from compiled, typechecked **Daml-LF**:

```
.daml  ──daml build──▶  DAR  ──damlc inspect──▶  Daml-LF text
                                                     │  backend/lf-parser.js
                                                     ▼
                                              structural model
                                                     │  src/graph.js
                                                     ▼
                                        normalized graph JSON (meta.source="daml-lf")
```

Why it is sounder than the regex parser: it reads the compiled package, so
operation target templates come from explicit `@Module:Template` type
applications (e.g. `create @Asset:Asset`) rather than being guessed, and
signatory/observer/controller party fields come from the actual record
projections in the compiled expressions.

**Usage** (requires the [Daml SDK](https://docs.daml.com) — `daml`/`damlc` — on PATH):

```bash
# from a DAR you built with `daml build`:
node backend/extract-dar.js path/to/project.dar --out graph.json
node backend/extract-dar.js path/to/project.dar --analyze        # include static analysis

# without the SDK, from a saved LF dump (also how the tests run):
daml damlc inspect project.dar > dump.lf
node backend/extract-dar.js --lf-file dump.lf --analyze
```

If the SDK is not installed, the CLI exits with an actionable message rather
than failing obscurely.

**View backend output in the browser:** click **Load graph JSON** in the app
and pick a file the backend wrote (e.g. `graph.json`, or the bundled
[`examples/sample-graph.daml-lf.json`](examples/sample-graph.daml-lf.json)).
The same visualizer renders it — no Daml is re-parsed — and if the file was
produced with `--analyze`, its findings show in the Static analysis panel.

> **Honest caveat:** the *textual* output of `damlc inspect` is not a stable
> public API and varies across Daml-LF versions; `backend/lf-parser.js` targets
> the Daml-LF 2.x style. If it recovers nothing from non-empty input it emits a
> diagnostic rather than silently returning an empty model. The fully
> version-proof route is to decode the DALF protobuf directly — a natural next
> step, and the parser already isolates that concern behind `parseLfPretty`.

## Static analyses

`src/analysis.js` runs three families over the normalized graph IR (so they
work on **either** front-end's output — though results are only as sound as the
graph feeding them):

| Family | Example findings |
| --- | --- |
| **authorization** | choices with no controller; consuming choices archivable by a non-signatory; `create X` where the acting authority may not cover `X`'s required signatories |
| **visibility** | templates with no observers (signatory-only visibility); controllers that are not explicit stakeholders |
| **information-flow** | authority crossing a party boundary (choice acting as party A creates a contract signed by party B); contract-lifecycle cycles; lifecycle leaf templates |

Findings are shown in the app's **Static analysis** panel and can be emitted by
the backend CLI with `--analyze` (added under an `analysis` key in the JSON).

**Soundness limit we do not hide:** party nodes are keyed by *field name per
template* (`party:Asset.issuer`). The analyses cannot know whether `issuer` in
one template is the same ledger `Party` as `from` in another, so every
cross-template authority finding says so explicitly rather than asserting a
violation. True party-identity/dataflow analysis is future work on top of the
Daml-LF backend.

## Roadmap

1. ✅ Browser parser — fast, offline, no-toolchain preview.
2. ✅ Daml-LF extraction backend (`backend/`) — reads a compiled DAR, emits the
   same normalized graph JSON with sound target inference.
3. ✅ Static analyses on the graph IR — authorization, visibility,
   information-flow.
4. ⏳ Decode the DALF **protobuf** directly (version-proof, no reliance on the
   `damlc inspect` text format).
5. ⏳ Party-identity / dataflow analysis to turn heuristic cross-template
   authority findings into sound ones; add contract-lifecycle and
   privilege-escalation checks.

## License

MIT
