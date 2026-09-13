// src/app.js
//
// Wires the UI together: read Daml source -> parse -> build graph -> render,
// and surface diagnostics + the raw graph JSON.
//
// The app owns the VIEW STATE (what is expanded, what is filtered, what is
// focused) and hands it to renderGraph on every change. The view state is a
// plain object, and every transformation it drives lives in src/view.js, so
// what the user sees is reproducible from {graph, viewState} alone.

import { parseDaml } from './parser.js';
import { parseProject } from './project.js';
import { expandCalls } from './callgraph.js';
import { buildGraph } from './graph.js';
import { renderGraph, NODE_STYLE, EDGE_STYLE } from './renderer.js';
import { analyzeAll } from './analysis.js';
import { modulesOf, edgeKindsOf, OPERATIONAL, STRUCTURAL } from './view.js';

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
  // view controls
  layoutMode: document.getElementById('layout-mode'),
  collapseAll: document.getElementById('collapse-all'),
  expandAll: document.getElementById('expand-all'),
  focusTarget: document.getElementById('focus-target'),
  focusHops: document.getElementById('focus-hops'),
  focusDirection: document.getElementById('focus-direction'),
  focusMode: document.getElementById('focus-mode'),
  focusClear: document.getElementById('focus-clear'),
  edgesStructural: document.getElementById('edges-structural'),
  edgesOperational: document.getElementById('edges-operational'),
  edgeKinds: document.getElementById('edge-kinds'),
  nodeKinds: document.getElementById('node-kinds'),
  moduleList: document.getElementById('module-list'),
  moduleSummary: document.getElementById('module-summary'),
  modulePrefix: document.getElementById('module-prefix'),
  modulesAll: document.getElementById('modules-all'),
  modulesNone: document.getElementById('modules-none'),
  hideIsolated: document.getElementById('hide-isolated'),
  hiddenReport: document.getElementById('hidden-report'),
};

// ------------------------------------------------------------- view state

/** The currently rendered graph, and how it is being looked at. */
let currentGraph = null;
let viewState = freshViewState();

function freshViewState() {
  return {
    expanded: new Set(),
    layout: 'auto',
    filters: {
      edgeKinds: null,   // null = every kind
      nodeKinds: null,
      modules: null,
      modulePrefix: '',
      hideIsolated: false,
    },
    focus: { seeds: [], hops: 2, direction: 'both', mode: 'dim' },
  };
}

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
  currentGraph = graph;
  // A new graph invalidates every selection: node ids from the old one would
  // silently match nothing, which would look like an empty focus rather than
  // a stale one.
  viewState = freshViewState();
  viewState.layout = els.layoutMode.value || 'auto';

  // Start collapsed on anything large enough to be a hairball, expanded on the
  // small pasted examples where the detail IS the point. The threshold is
  // about the reader, not the renderer: a dozen nodes is readable in full.
  if (graph.nodes.length > 40) {
    viewState.expanded = new Set();
  } else {
    viewState.expanded = new Set(
      graph.nodes.filter((n) => n.kind === 'template' || n.kind === 'interface').map((n) => n.id)
    );
  }

  buildFilterControls(graph);
  rerender();
  renderDiagnostics(diagnostics || []);
  // Prefer analysis embedded by `extract-dar.js --analyze`; otherwise compute.
  renderFindings(findings || analyzeAll(graph).all);
  renderStats(graph);
  els.json.textContent = JSON.stringify(graph, null, 2);
}

/** Re-run the view pipeline and repaint. Cheap enough to call on every input. */
function rerender() {
  if (!currentGraph) return;
  const info = renderGraph(els.svg, currentGraph, viewState, {
    onSelect: (id) => {
      // Clicking an already-focused node clears the focus, so a click is a
      // toggle rather than a trap.
      const seeds = viewState.focus.seeds;
      viewState.focus.seeds = seeds.length === 1 && seeds[0] === id ? [] : [id];
      syncFocusLabel();
      rerender();
    },
    onToggleExpand: (containerId) => {
      if (viewState.expanded.has(containerId)) viewState.expanded.delete(containerId);
      else viewState.expanded.add(containerId);
      rerender();
    },
  });
  renderLegend(info.legend);
  renderHiddenReport(info);
}

function syncFocusLabel() {
  const seeds = viewState.focus.seeds;
  els.focusTarget.textContent = seeds.length === 0
    ? 'none selected'
    : seeds.map((s) => s.replace(/^(tpl|iface|choice|party|key):/, '')).join(', ');
}

/**
 * The hidden-node report.
 *
 * This is not decoration. The tool's discipline is that it never shows a
 * subset without saying so, and collapse / filter / focus all show subsets by
 * design. If every node and every underlying edge is on screen, it says so
 * plainly instead of staying silent, so "no message" is never ambiguous.
 */
function renderHiddenReport(info) {
  const h = info.hidden;
  const head =
    `Showing ${h.shownNodes} of ${h.rawNodes} node(s) and ${h.rawEdgesShown} of ${h.rawEdges} edge(s) ` +
    `(${h.shownEdges} drawn after aggregation).`;
  const labels = info.labelsTotal > info.labelsShown
    ? ` ${info.labelsTotal - info.labelsShown} label(s) suppressed to avoid overlap.`
    : '';
  const timing = ` [${info.layout.mode}, layout ${info.layout.ms.toFixed(1)}ms, total ${info.timing.totalMs.toFixed(1)}ms]`;

  els.hiddenReport.className = 'hidden-report' + (h.complete && !labels ? ' complete' : ' partial');
  if (h.complete && h.reasons.length === 0) {
    els.hiddenReport.textContent = `${head} Nothing is hidden.${labels}${timing}`;
    return;
  }
  els.hiddenReport.textContent = `${head} ${h.reasons.join('; ')}.${labels}${timing}`;
}

/** Build the per-graph filter checkboxes from what the graph actually holds. */
function buildFilterControls(graph) {
  // --- edge kinds
  const kinds = edgeKindsOf(graph);
  els.edgeKinds.innerHTML = '';
  for (const { kind, count, group } of kinds) {
    els.edgeKinds.appendChild(checkbox(`ek-${kind}`, `${kind} (${count})`, true, () => {
      syncEdgeFilter();
      rerender();
    }, { 'data-kind': kind, 'data-group': group }));
  }
  els.edgesStructural.checked = true;
  els.edgesOperational.checked = true;

  // --- node kinds
  const nodeKinds = [...new Set(graph.nodes.map((n) => n.kind))].sort();
  els.nodeKinds.innerHTML = '';
  for (const k of nodeKinds) {
    const count = graph.nodes.filter((n) => n.kind === k).length;
    els.nodeKinds.appendChild(checkbox(`nk-${k}`, `${k} (${count})`, true, () => {
      syncNodeKindFilter();
      rerender();
    }, { 'data-kind': k }));
  }

  // --- modules (derived through containers, so templates whose own `module`
  // field is missing still land in the right bucket - see view.js deriveModule)
  const mods = modulesOf(graph);
  els.moduleList.innerHTML = '';
  for (const { module, count } of mods) {
    els.moduleList.appendChild(checkbox(`mod-${module}`, `${module} (${count})`, true, () => {
      syncModuleFilter();
      rerender();
    }, { 'data-module': module }));
  }
  els.moduleSummary.textContent = `modules (${mods.length})`;
  els.modulePrefix.value = '';
  els.hideIsolated.checked = false;
}

function syncEdgeFilter() {
  const boxes = [...els.edgeKinds.querySelectorAll('input[type=checkbox]')];
  const on = boxes.filter((b) => b.checked).map((b) => b.dataset.kind);
  viewState.filters.edgeKinds = on.length === boxes.length ? null : new Set(on);
  // Keep the two group toggles honest about the per-kind state.
  const groupState = (test) => {
    const inGroup = boxes.filter((b) => test(b.dataset.kind));
    return inGroup.length > 0 && inGroup.every((b) => b.checked);
  };
  els.edgesStructural.checked = groupState((k) => STRUCTURAL.has(k));
  els.edgesOperational.checked = groupState((k) => OPERATIONAL.has(k));
  if (on.length === 0) viewState.filters.edgeKinds = new Set([' none']);
}

function syncNodeKindFilter() {
  const boxes = [...els.nodeKinds.querySelectorAll('input[type=checkbox]')];
  const on = boxes.filter((b) => b.checked).map((b) => b.dataset.kind);
  viewState.filters.nodeKinds = on.length === boxes.length ? null : new Set(on);
  if (on.length === 0) viewState.filters.nodeKinds = new Set([' none']);
}

function syncModuleFilter() {
  const boxes = [...els.moduleList.querySelectorAll('input[type=checkbox]')];
  const on = boxes.filter((b) => b.checked).map((b) => b.dataset.module);
  viewState.filters.modules = on.length === boxes.length ? null : new Set(on);
  if (on.length === 0) viewState.filters.modules = new Set([' none']);
}

function setGroup(test, checked) {
  for (const b of els.edgeKinds.querySelectorAll('input[type=checkbox]')) {
    if (test(b.dataset.kind)) b.checked = checked;
  }
  syncEdgeFilter();
  rerender();
}

function checkbox(id, label, checked, onChange, data = {}) {
  const wrap = document.createElement('label');
  wrap.className = 'chk';
  wrap.htmlFor = id;
  const box = document.createElement('input');
  box.type = 'checkbox';
  box.id = id;
  box.checked = checked;
  for (const [k, v] of Object.entries(data)) box.setAttribute(k, v);
  box.addEventListener('change', onChange);
  wrap.appendChild(box);
  wrap.appendChild(document.createTextNode(' ' + label));
  return wrap;
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

/**
 * The legend describes the graph that is ON SCREEN, not the schema.
 * Edge kinds that were filtered out, or that this graph never had, are absent;
 * listing them would imply the reader should be able to find them.
 */
function renderLegend(legend) {
  els.legend.innerHTML = '';
  const add = (type, color, label, title) => {
    const span = document.createElement('span');
    span.className = 'legend-item';
    span.title = title || label;
    const sw = document.createElement('span');
    sw.className = `legend-swatch legend-${type}`;
    sw.style.borderColor = color;
    if (type === 'node') sw.style.background = color;
    span.appendChild(sw);
    span.appendChild(document.createTextNode(label));
    els.legend.appendChild(span);
  };
  for (const k of legend.nodeKinds) {
    add('node', (NODE_STYLE[k] || NODE_STYLE.template).fill, k);
  }
  let group = null;
  for (const e of legend.edgeKinds) {
    if (e.group !== group) {
      group = e.group;
      const sep = document.createElement('span');
      sep.className = 'legend-group';
      sep.textContent = group;
      els.legend.appendChild(sep);
    }
    add('edge', (EDGE_STYLE[e.kind] || EDGE_STYLE.declares).color, `${e.kind} (${e.count})`,
      `${e.count} underlying edge(s) in ${e.groups} drawn edge(s)`);
  }
  if (legend.edgeKinds.length === 0) {
    const span = document.createElement('span');
    span.className = 'legend-item';
    span.textContent = 'no edges shown';
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

// ------------------------------------------------------------------ events

els.analyze.addEventListener('click', run);

els.layoutMode.addEventListener('change', () => {
  viewState.layout = els.layoutMode.value;
  rerender();
});
els.collapseAll.addEventListener('click', () => {
  viewState.expanded = new Set();
  rerender();
});
els.expandAll.addEventListener('click', () => {
  if (!currentGraph) return;
  viewState.expanded = new Set(
    currentGraph.nodes.filter((n) => n.kind === 'template' || n.kind === 'interface').map((n) => n.id)
  );
  rerender();
});
els.focusHops.addEventListener('change', () => {
  viewState.focus.hops = Number(els.focusHops.value);
  rerender();
});
els.focusDirection.addEventListener('change', () => {
  viewState.focus.direction = els.focusDirection.value;
  rerender();
});
els.focusMode.addEventListener('change', () => {
  viewState.focus.mode = els.focusMode.value;
  rerender();
});
els.focusClear.addEventListener('click', () => {
  viewState.focus.seeds = [];
  syncFocusLabel();
  rerender();
});
els.edgesStructural.addEventListener('change', () =>
  setGroup((k) => STRUCTURAL.has(k), els.edgesStructural.checked));
els.edgesOperational.addEventListener('change', () =>
  setGroup((k) => OPERATIONAL.has(k), els.edgesOperational.checked));
els.modulePrefix.addEventListener('input', () => {
  viewState.filters.modulePrefix = els.modulePrefix.value.trim();
  rerender();
});
els.modulesAll.addEventListener('click', () => {
  for (const b of els.moduleList.querySelectorAll('input')) b.checked = true;
  syncModuleFilter();
  rerender();
});
els.modulesNone.addEventListener('click', () => {
  for (const b of els.moduleList.querySelectorAll('input')) b.checked = false;
  syncModuleFilter();
  rerender();
});
els.hideIsolated.addEventListener('change', () => {
  viewState.filters.hideIsolated = els.hideIsolated.checked;
  rerender();
});

// Re-layout on resize: the layout is a pure function of the graph AND the
// viewport, so a resize genuinely changes the answer.
let resizeTimer = null;
window.addEventListener('resize', () => {
  if (resizeTimer) clearTimeout(resizeTimer);
  resizeTimer = setTimeout(rerender, 160);
});

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

initExamples();
syncFocusLabel();
els.source.value = EXAMPLES.Asset;
run();
