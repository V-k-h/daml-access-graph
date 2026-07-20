// src/app.js
//
// Wires the UI together: read Daml source -> parse -> build graph -> render,
// and surface diagnostics + the raw graph JSON.

import { parseDaml } from './parser.js';
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
  const parsed = parseDaml(src);
  const graph = buildGraph(parsed);
  showGraph(graph, { diagnostics: parsed.diagnostics });
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
        message: `Loaded ${fileName || 'graph JSON'} (source: ${graph.meta.source || 'unknown'}) — visualization only, no Daml was parsed.`,
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
  const catOrder = { authorization: 0, visibility: 1, 'information-flow': 2 };
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
    li.textContent = 'No diagnostics. (This does not mean the parse is complete — it is a prototype.)';
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
  const templates = graph.nodes.filter((n) => n.kind === 'template' && !(n.meta && n.meta.external)).length;
  const choices = graph.nodes.filter((n) => n.kind === 'choice').length;
  const src = graph.meta && graph.meta.source ? ` [${graph.meta.source}]` : '';
  els.stats.textContent =
    `module ${(graph.meta && graph.meta.module) || '(none)'}${src} · ` +
    `${templates} templates · ${choices} choices · ` +
    `${graph.nodes.length} nodes · ${graph.edges.length} edges`;
}

function buildLegend() {
  const items = [
    ['node', NODE_STYLE.template.fill, 'template'],
    ['node', NODE_STYLE.party.fill, 'party field'],
    ['node', NODE_STYLE.choice.fill, 'choice'],
    ['edge', EDGE_STYLE.signatory.color, 'signatory'],
    ['edge', EDGE_STYLE.observer.color, 'observer'],
    ['edge', EDGE_STYLE.controller.color, 'controller'],
    ['edge', EDGE_STYLE.create.color, 'create'],
    ['edge', EDGE_STYLE.exercise.color, 'exercise'],
    ['edge', EDGE_STYLE.archive.color, 'archive'],
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

function initExamples() {
  for (const name of Object.keys(EXAMPLES)) {
    const opt = document.createElement('option');
    opt.value = name;
    opt.textContent = name;
    els.examples.appendChild(opt);
  }
  els.examples.addEventListener('change', () => {
    const key = els.examples.value;
    if (EXAMPLES[key]) {
      els.source.value = EXAMPLES[key];
      run();
    }
  });
}

els.analyze.addEventListener('click', run);
els.loadDaml.addEventListener('click', () => els.damlFile.click());
els.damlFile.addEventListener('change', (e) => {
  const file = e.target.files && e.target.files[0];
  if (!file) return;
  const reader = new FileReader();
  reader.onload = () => {
    els.source.value = String(reader.result);
    els.examples.value = '';
    run();
  };
  reader.readAsText(file);
  els.damlFile.value = ''; // allow re-loading the same file
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
