// src/diff.js
//
// Compare two normalized graphs and classify what changed.
//
// Why this is the piece that makes the tool useful more than once: a graph you
// generate and read by hand tells you what the access structure IS. A diff
// tells you what a change DID to it, which is the question a reviewer actually
// has. "This PR adds a consuming choice controlled by a non-signatory" is
// reviewable; a 371-edge graph is not.
//
// The central idea is that access-structure changes are not symmetric. Adding
// an observer, adding a controller, or flipping a choice to consuming all
// WIDEN the set of things some party can see or do. Removing them narrows it.
// A CI gate wants to fail on the first kind and stay quiet about the second,
// so every change carries a `direction`.
//
// Edges are matched on (source, kind, target), never on `id`: edge ids are
// positional (`e0`, `e1`, ...) and shift whenever anything earlier in the
// graph changes, so comparing them would report the whole graph as churn.

/**
 * @typedef {Object} Change
 * @property {'node'|'edge'|'meta'} scope
 * @property {'added'|'removed'|'changed'} op
 * @property {'widening'|'narrowing'|'neutral'} direction
 * @property {string} code
 * @property {string} key      stable identity of the thing that changed
 * @property {string} message
 */

/** Edge kinds that grant read or write reach when added. */
const REACH_KINDS = new Set([
  'create', 'createAndExercise', 'exercise', 'exerciseByKey', 'archive',
  'fetch', 'fetchByKey', 'lookupByKey', 'lookupAllByKey',
]);

/**
 * How to read the addition of each edge kind. The removal is the opposite,
 * except for `neutral` kinds.
 */
const EDGE_DIRECTION = {
  declares: 'widening',       // a new choice is new exercisable surface
  controller: 'widening',     // a new party may exercise
  'view-controller': 'widening',
  observer: 'widening',       // a new party may see
  implements: 'widening',     // a whole interface's choices become exercisable
  signatory: 'narrowing',     // one MORE party must authorize
  maintainer: 'narrowing',    // key lookup becomes more constrained
  'keyed-by': 'neutral',
};

const edgeKey = (e) => `${e.source}|${e.kind}|${e.target}`;

const flip = (direction) =>
  direction === 'widening' ? 'narrowing' : direction === 'narrowing' ? 'widening' : 'neutral';

function directionFor(kind, op) {
  const base = EDGE_DIRECTION[kind] || (REACH_KINDS.has(kind) ? 'widening' : 'neutral');
  return op === 'added' ? base : flip(base);
}

/**
 * Diff two normalized graphs.
 *
 * @param {import('./graph.js').Graph} before
 * @param {import('./graph.js').Graph} after
 * @returns {{changes: Change[], summary: Object}}
 */
export function diffGraphs(before, after) {
  /** @type {Change[]} */
  const changes = [];

  const beforeNodes = new Map((before.nodes || []).map((n) => [n.id, n]));
  const afterNodes = new Map((after.nodes || []).map((n) => [n.id, n]));

  const describeNode = (n) => `${n.kind} ${n.label}${n.owner && n.owner !== n.label ? ` (of ${n.owner})` : ''}`;

  // ------------------------------------------------------------------ nodes
  for (const [id, n] of afterNodes) {
    if (beforeNodes.has(id)) continue;
    changes.push({
      scope: 'node',
      op: 'added',
      // A node on its own grants nothing; its edges do. Reported as neutral so
      // the gate keys off the edges rather than double-counting.
      direction: 'neutral',
      code: `node-added-${n.kind}`,
      key: id,
      message: `new ${describeNode(n)}`,
    });
  }
  for (const [id, n] of beforeNodes) {
    if (afterNodes.has(id)) continue;
    changes.push({
      scope: 'node',
      op: 'removed',
      direction: 'neutral',
      code: `node-removed-${n.kind}`,
      key: id,
      message: `removed ${describeNode(n)}`,
    });
  }

  // ------------------------------------------------------------------ edges
  const beforeEdges = new Map((before.edges || []).map((e) => [edgeKey(e), e]));
  const afterEdges = new Map((after.edges || []).map((e) => [edgeKey(e), e]));

  const label = (id, nodes) => {
    const n = nodes.get(id);
    return n ? n.label : id;
  };

  for (const [key, e] of afterEdges) {
    if (beforeEdges.has(key)) continue;
    changes.push({
      scope: 'edge',
      op: 'added',
      direction: directionFor(e.kind, 'added'),
      code: `edge-added-${e.kind}`,
      key,
      message:
        `${label(e.source, afterNodes)} -${e.kind}-> ${label(e.target, afterNodes)}` +
        (e.meta && e.meta.via ? ` (via ${e.meta.via.join(' -> ')})` : ''),
    });
  }
  for (const [key, e] of beforeEdges) {
    if (afterEdges.has(key)) continue;
    changes.push({
      scope: 'edge',
      op: 'removed',
      direction: directionFor(e.kind, 'removed'),
      code: `edge-removed-${e.kind}`,
      key,
      message: `${label(e.source, beforeNodes)} -${e.kind}-> ${label(e.target, beforeNodes)} is gone`,
    });
  }

  // --------------------------------------------------------------- metadata
  // Only the metadata that changes what a party can do.
  for (const [id, a] of afterNodes) {
    const b = beforeNodes.get(id);
    if (!b) continue;

    const bMeta = b.meta || {};
    const aMeta = a.meta || {};

    if (a.kind === 'choice') {
      const bConsuming = bMeta.consuming !== false;
      const aConsuming = aMeta.consuming !== false;
      if (bConsuming !== aConsuming) {
        changes.push({
          scope: 'meta',
          op: 'changed',
          // Becoming consuming means the controller can now archive the
          // contract, which is strictly more power.
          direction: aConsuming ? 'widening' : 'narrowing',
          code: 'choice-consuming-changed',
          key: id,
          message:
            `${a.label} on ${a.owner || a.template} is now ` +
            `${aConsuming ? 'CONSUMING (its controller can archive the contract)' : 'nonconsuming'}`,
        });
      }
    }

    if (a.kind === 'key') {
      const bM = [...(bMeta.maintainers || [])].sort().join(',');
      const aM = [...(aMeta.maintainers || [])].sort().join(',');
      if (bM !== aM) {
        changes.push({
          scope: 'meta',
          op: 'changed',
          direction: 'widening',
          code: 'key-maintainers-changed',
          key: id,
          message:
            `contract key of ${a.template}: maintainers [${bM || '∅'}] -> [${aM || '∅'}], ` +
            `which changes who may look these contracts up by key`,
        });
      }
    }

    if (!!bMeta.external !== !!aMeta.external) {
      changes.push({
        scope: 'meta',
        op: 'changed',
        // Usually just better information (a package got decoded), not a real
        // change to the system.
        direction: 'neutral',
        code: 'external-changed',
        key: id,
        message:
          `${describeNode(a)} is now ${aMeta.external ? 'external (declared outside this graph)' : 'resolved within this graph'}`,
      });
    }
  }

  return { changes, summary: summarize(changes) };
}

function summarize(changes) {
  const byDirection = { widening: 0, narrowing: 0, neutral: 0 };
  const byCode = {};
  for (const c of changes) {
    byDirection[c.direction]++;
    byCode[c.code] = (byCode[c.code] || 0) + 1;
  }
  return { total: changes.length, byDirection, byCode };
}

/**
 * Diff two finding lists on a fingerprint rather than message text, so a
 * reworded message is not reported as a new finding.
 *
 * @param {Array<{code: string, subjects?: string[], severity: string, message: string}>} before
 * @param {Array<{code: string, subjects?: string[], severity: string, message: string}>} after
 */
export function diffFindings(before, after) {
  const key = (f) => findingFingerprint(f);
  const beforeSet = new Map((before || []).map((f) => [key(f), f]));
  const afterSet = new Map((after || []).map((f) => [key(f), f]));

  const added = [];
  const removed = [];
  for (const [k, f] of afterSet) if (!beforeSet.has(k)) added.push(f);
  for (const [k, f] of beforeSet) if (!afterSet.has(k)) removed.push(f);

  return {
    added,
    removed,
    summary: {
      added: added.length,
      removed: removed.length,
      addedBySeverity: added.reduce((acc, f) => {
        acc[f.severity] = (acc[f.severity] || 0) + 1;
        return acc;
      }, {}),
    },
  };
}

/**
 * A stable identity for a finding: its code plus the nodes it is about.
 *
 * Deliberately NOT the message, which embeds counts and party lists that churn
 * without the underlying issue changing, and which gets reworded whenever the
 * analysis text is improved.
 */
export function findingFingerprint(f) {
  const subjects = [...(f.subjects || [])].sort().join(',');
  return `${f.code}#${subjects}`;
}
