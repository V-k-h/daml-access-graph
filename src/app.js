// src/app.js
//
// Wires the UI together: read Daml source -> parse -> build graph -> render,
// and surface diagnostics + the raw graph JSON.

import { parseDaml } from './parser.js';
import { parseProject } from './project.js';
import { expandCalls } from './callgraph.js';
import { buildGraph } from './graph.js';
import { renderGraph, NODE_STYLE, EDGE_STYLE } from './renderer.js';
import { analyzeAll } from './analysis.js';

const els = {
  source: document.getElementById('source'),
  analyze: document.getElementById('analyze'),
  examples: document.getElementById('examples'),
  svg: document.getElementById('graph'),
  diagnostics: document.getElementById('diagnostics'),
  json: document.getElementById('json'),
  findings: document.getElementById('findings'),
  stats: document.getElementById('stats'),
  legend: document.getElementById('legend'),
  loadJson: document.getElementById('load-json'),
  jsonFile: document.getElementById('json-file'),
  loadDaml: document.getElementById('load-daml'),
  damlFile: document.getElementById('daml-file'),
};

// Small built-in examples so the app is usable without loading files.
const EXAMPLES = {
  Asset: `module Asset where

template Asset
  with
    issuer : Party
    owner : Party
    amount : Decimal
  where
    signatory issuer
    observer owner

    choice Give : ContractId Asset
      with newOwner : Party
      controller owner
      do
        create this with owner = newOwner

    nonconsuming choice Peek : Decimal
      controller issuer
      do
        return amount
`,
  Transfer: `module Transfer where

template TransferProposal
  with
    from : Party
    to : Party
    assetCid : ContractId Asset
  where
    signatory from
    observer to

    choice Accept : ContractId Asset
      controller to
      do
        archive assetCid
        create Asset with issuer = from, owner = to, amount = 1.0

    choice Reject : ()
      controller to
      do
        return ()
`,
};

// Parse-and-render the Daml source in the editor.
function run() {
  const src = els.source.value;
  // Resolve same-module helper functions even for a single pasted file, so a
  // choice whose body just calls a local helper still shows its real
  // create/exercise edges.
  const parsed = expandCalls(parseDaml(src));
  const graph = buildGraph(parsed);
  showGraph(graph, { diagnostics: parsed.diagnostics });
}

// Parse several .daml files as one project: cross-module `exercise` targets,
// interface declarations, and helper functions all resolve against the whole
// set rather than being reported as unknown.
function runProject(files) {
  const project = parseProject(files);
  const graph = buildGraph(project, { source: 'project-source' });
  showGraph(graph, {
    diagnostics: [
      {
        severity: 'info',
        message:
          `Project mode: ${project.stats.files} file(s), ${project.stats.modules} module(s), ` +
          `${project.stats.templates} template(s), ${project.stats.interfaces} interface(s). ` +
          `${project.stats.opsResolvedByProject} operation target(s) resolved across modules, ` +
          `${project.stats.opsViaHelpers || 0} attributed via helper functions.`,
      },
      ...project.diagnostics,
    ],
  });
  els.source.value =
    `-- Project mode: ${files.length} file(s) loaded.\n` +
    `-- The editor is not the source of this graph; re-pick files to reload.\n` +
    files.map((f) => `--   ${f.path}`).join('\n');
}

// Render an already-built graph (from source, or loaded JSON).
function showGraph(graph, { diagnostics, findings } = {}) {
  renderGraph(els.svg, graph);
  renderDiagnostics(diagnostics || []);
  // Prefer analysis embedded by `extract-dar.js --analyze`; otherwise compute.
  renderFindings(findings || analyzeAll(graph).all);
  renderStats(graph);
  els.json.textContent = JSON.stringify(graph, null, 2);
}

// Validate + render a normalized graph JSON (e.g. from the Daml-LF backend).
function loadGraphJson(text, fileName) {
  let data;
  try {
    data = JSON.parse(text);
  } catch (e) {
    renderDiagnostics([{ severity: 'error', message: `Not valid JSON: ${e.message}` }]);
    return;
  }
  const graph = data && data.nodes && data.edges ? data : null;
  if (!graph || !Array.isArray(graph.nodes) || !Array.isArray(graph.edges)) {
    renderDiagnostics([
      { severity: 'error', message: 'JSON does not look like a normalized graph (missing `nodes` / `edges` arrays).' },
    ]);
    return;
  }
  graph.meta = graph.meta || {};
  // `--analyze` output nests the graph under top-level keys plus `analysis`.
  const embedded = data.analysis && Array.isArray(data.analysis.all) ? data.analysis.all : null;
  showGraph(graph, {
    diagnostics: [
      {
        severity: 'info',
        message: `Loaded ${fileName || 'graph JSON'} (source: ${graph.meta.source || 'unknown'}) - visualization only, no Daml was parsed.`,
      },
    ],
    findings: embedded,
  });
}

function renderFindings(findings) {
  els.findings.innerHTML = '';
  if (findings.length === 0) {
    const li = document.createElement('li');
    li.className = 'diag diag-info';
    li.textContent = 'No findings from authorization / visibility / information-flow analyses.';
    els.findings.appendChild(li);
    return;
  }
  const catOrder = { authorization: 0, keys: 1, interfaces: 2, visibility: 3, 'information-flow': 4 };
  const sevOrder = { error: 0, warning: 1, info: 2 };
  [...findings]
    .sort((a, b) => (catOrder[a.category] - catOrder[b.category]) || (sevOrder[a.severity] - sevOrder[b.severity]))
    .forEach((f) => {
      const li = document.createElement('li');
      li.className = `diag diag-${f.severity}`;
      const tag = f.category.replace('information-flow', 'info-flow');
      li.innerHTML = `<span class="finding-tag finding-${f.category}">${tag}</span> ${escapeHtml(f.message)}`;
      els.findings.appendChild(li);
    });
}

function escapeHtml(s) {
  return s.replace(/[&<>]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c]));
}

function renderDiagnostics(diags) {
  els.diagnostics.innerHTML = '';
  if (diags.length === 0) {
    const li = document.createElement('li');
    li.className = 'diag diag-info';
    li.textContent = 'No diagnostics. (This does not mean the parse is complete - it is a prototype.)';
    els.diagnostics.appendChild(li);
    return;
  }
  const order = { error: 0, warning: 1, info: 2 };
  [...diags]
    .sort((a, b) => (order[a.severity] - order[b.severity]) || ((a.line || 0) - (b.line || 0)))
    .forEach((d) => {
      const li = document.createElement('li');
      li.className = `diag diag-${d.severity}`;
      const where = d.line ? ` (line ${d.line})` : '';
      li.textContent = `${d.severity.toUpperCase()}${where}: ${d.message}`;
      els.diagnostics.appendChild(li);
    });
}

function renderStats(graph) {
  const internal = (n) => !(n.meta && n.meta.external);
  const templates = graph.nodes.filter((n) => n.kind === 'template' && internal(n)).length;
  const ifaces = graph.nodes.filter((n) => n.kind === 'interface' && internal(n)).length;
  const choices = graph.nodes.filter((n) => n.kind === 'choice').length;
  const keys = graph.nodes.filter((n) => n.kind === 'key').length;
  const src = graph.meta && graph.meta.source ? ` [${graph.meta.source}]` : '';
  const scope =
    graph.meta && graph.meta.modules
      ? `${graph.meta.modules.length} modules`
      : `module ${(graph.meta && graph.meta.module) || '(none)'}`;
  els.stats.textContent =
    `${scope}${src} · ${templates} templates · ` +
    (ifaces ? `${ifaces} interfaces · ` : '') +
    `${choices} choices · ` +
    (keys ? `${keys} keys · ` : '') +
    `${graph.nodes.length} nodes · ${graph.edges.length} edges`;
}

function buildLegend() {
  const items = [
    ['node', NODE_STYLE.template.fill, 'template'],
    ['node', NODE_STYLE.party.fill, 'party field'],
    ['node', NODE_STYLE.choice.fill, 'choice'],
    ['node', NODE_STYLE.interface.fill, 'interface'],
    ['node', NODE_STYLE.key.fill, 'contract key'],
    ['edge', EDGE_STYLE.signatory.color, 'signatory'],
    ['edge', EDGE_STYLE.observer.color, 'observer'],
    ['edge', EDGE_STYLE.controller.color, 'controller'],
    ['edge', EDGE_STYLE.create.color, 'create'],
    ['edge', EDGE_STYLE.exercise.color, 'exercise'],
    ['edge', EDGE_STYLE.archive.color, 'archive'],
    ['edge', EDGE_STYLE.implements.color, 'implements'],
    ['edge', EDGE_STYLE.maintainer.color, 'maintainer'],
  ];
  els.legend.innerHTML = '';
  for (const [type, color, label] of items) {
    const span = document.createElement('span');
    span.className = 'legend-item';
    span.innerHTML =
      `<span class="legend-swatch legend-${type}" style="background:${type === 'node' ? color : 'transparent'};border-color:${color}"></span>${label}`;
    els.legend.appendChild(span);
  }
}

// Larger examples live as real .daml files under examples/ and are fetched on
// demand (they also serve as parser test fixtures, so there is one copy, not
// two). EXAMPLES above stays inline so the app still works if fetch fails.
const FILE_EXAMPLES = {
  Iou: 'examples/Iou.daml',
  TokenInterface: 'examples/TokenInterface.daml',
  ConfidentialAuction: 'examples/ConfidentialAuction.daml',
};

function initExamples() {
  for (const name of [...Object.keys(EXAMPLES), ...Object.keys(FILE_EXAMPLES)]) {
    const opt = document.createElement('option');
    opt.value = name;
    opt.textContent = name;
    els.examples.appendChild(opt);
  }
  els.examples.addEventListener('change', async () => {
    const key = els.examples.value;
    if (EXAMPLES[key]) {
      els.source.value = EXAMPLES[key];
      run();
      return;
    }
    const path = FILE_EXAMPLES[key];
    if (!path) return;
    try {
      const res = await fetch(path);
      if (!res.ok) throw new Error(`HTTP ${res.status}`);
      els.source.value = await res.text();
      run();
    } catch (err) {
      renderDiagnostics([
        {
          severity: 'error',
          message:
            `Could not load ${path} (${err.message}). Bundled file examples need the app to be served ` +
            `over HTTP (npm run serve), not opened from file://.`,
        },
      ]);
    }
  });
}

els.analyze.addEventListener('click', run);
els.loadDaml.addEventListener('click', () => els.damlFile.click());
els.damlFile.addEventListener('change', async (e) => {
  const picked = [...(e.target.files || [])];
  els.damlFile.value = ''; // allow re-loading the same selection
  if (picked.length === 0) return;
  els.examples.value = '';

  const read = (file) =>
    new Promise((resolve, reject) => {
      const reader = new FileReader();
      reader.onload = () => resolve({ path: file.webkitRelativePath || file.name, source: String(reader.result) });
      reader.onerror = () => reject(reader.error);
      reader.readAsText(file);
    });

  try {
    const files = await Promise.all(picked.map(read));
    if (files.length === 1) {
      els.source.value = files[0].source;
      run();
    } else {
      runProject(files);
    }
  } catch (err) {
    renderDiagnostics([{ severity: 'error', message: `Could not read files: ${err.message}` }]);
  }
});
els.loadJson.addEventListener('click', () => els.jsonFile.click());
els.jsonFile.addEventListener('change', (e) => {
  const file = e.target.files && e.target.files[0];
  if (!file) return;
  const reader = new FileReader();
  reader.onload = () => loadGraphJson(String(reader.result), file.name);
  reader.readAsText(file);
  els.jsonFile.value = ''; // allow re-loading the same file
});
buildLegend();
initExamples();
els.source.value = EXAMPLES.Asset;
run();
