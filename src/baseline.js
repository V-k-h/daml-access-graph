// src/baseline.js
//
// A BASELINE is the committed record of a codebase's accepted access structure:
// which findings are known-and-accepted, and what the graph's edge set looked
// like when that was decided.
//
// It exists so a CI gate can answer "did this change widen the access
// structure, or introduce a finding nobody has looked at?" rather than "are
// there any findings?" - the latter is useless on a real repository, which
// starts with dozens of legitimate informational findings.
//
// Design decisions worth stating:
//
//   * Findings are recorded by FINGERPRINT (code + subject node ids), not by
//     message. Messages embed party lists and counts and get reworded when the
//     analysis improves; fingerprints survive that.
//   * The graph is recorded as a sorted list of `source|kind|target` edge keys
//     plus the node ids, not the full graph: that is what the diff compares, it
//     stays readable in review, and it does not carry layout noise.
//   * Alongside those, `nodeMeta` keeps the few node properties that are
//     themselves access-relevant - a choice's consuming flag, a key's
//     maintainers, whether a declaration is external. Dropping them would make
//     a baseline round-trip report every nonconsuming choice and every keyed
//     template as changed, which is exactly the false alarm a gate must not
//     produce.
//   * There is no "ignore everything" switch. Accepting a finding means it
//     appears in the baseline by name, in a committed file, where a reviewer
//     can see it.

import { diffGraphs, diffFindings, findingFingerprint } from './diff.js';

export const BASELINE_VERSION = 1;

const edgeKey = (e) => `${e.source}|${e.kind}|${e.target}`;

/**
 * Build a baseline from a graph and its analysis.
 *
 * @param {import('./graph.js').Graph} graph
 * @param {{all: Array<Object>}} analysis
 * @param {{source?: string, note?: string}} [meta]
 */
export function createBaseline(graph, analysis, meta = {}) {
  const findings = (analysis && analysis.all) || [];
  return {
    version: BASELINE_VERSION,
    source: meta.source || (graph.meta && graph.meta.source) || null,
    note: meta.note || null,
    // Counts are informational; the gate uses the lists below.
    counts: {
      nodes: graph.nodes.length,
      edges: graph.edges.length,
      findings: findings.length,
    },
    findings: [...new Set(findings.map(findingFingerprint))].sort(),
    graph: {
      nodes: [...new Set(graph.nodes.map((n) => n.id))].sort(),
      edges: [...new Set(graph.edges.map(edgeKey))].sort(),
      nodeMeta: accessRelevantMeta(graph),
    },
  };
}

/**
 * The node metadata the diff compares, and nothing else.
 * Omitted when it equals the default, so the baseline stays small and a review
 * diff shows only meaningful entries.
 */
function accessRelevantMeta(graph) {
  /** @type {Record<string, Object>} */
  const out = {};
  for (const n of graph.nodes) {
    const meta = n.meta || {};
    const rec = {};
    if (n.kind === 'choice' && meta.consuming === false) rec.consuming = false;
    if (n.kind === 'key') rec.maintainers = [...(meta.maintainers || [])].sort();
    if (meta.external) rec.external = true;
    if (Object.keys(rec).length) out[n.id] = rec;
  }
  return out;
}

/**
 * Reconstruct the minimal graph shape the differ needs from a baseline.
 * Node kind/label are recovered from the id prefix, which is enough for the
 * diff's messages and exactly what the baseline stores.
 */
function graphFromBaseline(baseline) {
  const nodeMeta = (baseline.graph && baseline.graph.nodeMeta) || {};
  const nodes = (baseline.graph.nodes || []).map((id) => {
    const [prefix, rest = ''] = [id.slice(0, id.indexOf(':')), id.slice(id.indexOf(':') + 1)];
    const kind =
      { tpl: 'template', iface: 'interface', party: 'party', choice: 'choice', key: 'key' }[prefix] ||
      'template';
    const label = kind === 'key' ? `key ${rest}` : rest.includes('.') ? rest.slice(rest.lastIndexOf('.') + 1) : rest;
    const owner = rest.includes('.') ? rest.slice(0, rest.lastIndexOf('.')) : undefined;
    const stored = nodeMeta[id] || {};
    return {
      id,
      kind,
      label,
      owner,
      template: kind === 'key' ? rest : owner,
      // Defaults must MATCH what the differ treats as default, or a round-trip
      // reports phantom changes: choices are consuming unless stated, keys have
      // an explicit maintainer list, declarations are internal unless stated.
      meta: {
        ...(kind === 'choice' ? { consuming: stored.consuming !== false } : {}),
        ...(kind === 'key' ? { maintainers: stored.maintainers || [] } : {}),
        external: !!stored.external,
      },
    };
  });
  const edges = (baseline.graph.edges || []).map((k, i) => {
    const [source, kind, target] = k.split('|');
    return { id: `b${i}`, source, kind, target, label: kind };
  });
  return { meta: { source: baseline.source }, nodes, edges };
}

/**
 * Compare a current graph + analysis against a baseline.
 *
 * @param {Object} baseline
 * @param {import('./graph.js').Graph} graph
 * @param {{all: Array<Object>}} analysis
 * @returns {{
 *   graphDiff: ReturnType<typeof diffGraphs>,
 *   findingDiff: ReturnType<typeof diffFindings>,
 *   newFindings: Array<Object>,
 *   fixedFindings: string[],
 *   widening: Array<Object>,
 *   ok: boolean
 * }}
 */
export function compareToBaseline(baseline, graph, analysis) {
  if (!baseline || baseline.version !== BASELINE_VERSION) {
    throw new Error(
      `Unsupported baseline version ${baseline && baseline.version}; expected ${BASELINE_VERSION}. ` +
        'Regenerate it with --update.'
    );
  }

  const findings = (analysis && analysis.all) || [];
  const known = new Set(baseline.findings || []);
  const current = new Map(findings.map((f) => [findingFingerprint(f), f]));

  const newFindings = [...current.entries()]
    .filter(([fp]) => !known.has(fp))
    .map(([, f]) => f);
  const fixedFindings = [...known].filter((fp) => !current.has(fp));

  const graphDiff = diffGraphs(graphFromBaseline(baseline), graph);
  // A baseline written before `nodeMeta` existed cannot support metadata
  // comparison; drop those changes rather than reporting them as real.
  if (!baseline.graph || !baseline.graph.nodeMeta) {
    graphDiff.changes = graphDiff.changes.filter((c) => c.scope !== 'meta');
    graphDiff.summary = {
      total: graphDiff.changes.length,
      byDirection: graphDiff.changes.reduce(
        (acc, c) => ({ ...acc, [c.direction]: (acc[c.direction] || 0) + 1 }),
        { widening: 0, narrowing: 0, neutral: 0 }
      ),
      byCode: graphDiff.changes.reduce((acc, c) => ({ ...acc, [c.code]: (acc[c.code] || 0) + 1 }), {}),
    };
  }
  const widening = graphDiff.changes.filter((c) => c.direction === 'widening');

  // A synthetic before-list is enough for the finding diff: the baseline stores
  // fingerprints, and that is what the diff keys on.
  const findingDiff = diffFindings(
    [...known].map((fp) => fingerprintToStub(fp)),
    findings
  );

  return {
    graphDiff,
    findingDiff,
    newFindings,
    fixedFindings,
    widening,
    ok: newFindings.length === 0 && widening.length === 0,
  };
}

/** Turn a stored fingerprint back into the minimal object the differ needs. */
function fingerprintToStub(fingerprint) {
  const [code, subjects = ''] = fingerprint.split('#');
  return {
    code,
    subjects: subjects ? subjects.split(',') : [],
    severity: 'info',
    message: `(baselined ${code})`,
  };
}
