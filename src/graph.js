// src/graph.js
//
// Turns a ParseResult (from parser.js) into a NORMALIZED GRAPH JSON that the
// renderer — or any future Daml-LF backend — can consume. The schema is
// documented in README.md ("Normalized graph schema").

/**
 * @typedef {Object} GraphNode
 * @property {string} id
 * @property {'template'|'party'|'choice'} kind
 * @property {string} label
 * @property {string} [template]   owning template name (for party/choice)
 * @property {Object} [meta]
 */

/**
 * @typedef {Object} GraphEdge
 * @property {string} id
 * @property {string} source
 * @property {string} target
 * @property {'declares'|'signatory'|'observer'|'controller'|'create'|'createAndExercise'|'exercise'|'exerciseByKey'|'fetch'|'fetchByKey'|'lookupByKey'|'archive'} kind
 * @property {string} label
 */

/**
 * @typedef {Object} Graph
 * @property {{module: string|null, source: string, warnings: string[]}} meta
 * @property {GraphNode[]} nodes
 * @property {GraphEdge[]} edges
 */

const OPERATION_KINDS = new Set([
  'create', 'createAndExercise', 'exercise', 'exerciseByKey',
  'fetch', 'fetchByKey', 'lookupByKey', 'archive',
]);

const tplId = (name) => `tpl:${name}`;
const partyId = (tpl, field) => `party:${tpl}.${field}`;
const choiceId = (tpl, name) => `choice:${tpl}.${name}`;

/**
 * @param {import('./parser.js').ParseResult} parsed
 * @param {{source?: string}} [options]  provenance tag written to meta.source
 * @returns {Graph}
 */
export function buildGraph(parsed, options = {}) {
  const source = options.source || 'browser-prototype';
  /** @type {Map<string, GraphNode>} */
  const nodes = new Map();
  /** @type {GraphEdge[]} */
  const edges = [];
  let edgeSeq = 0;

  const addNode = (node) => {
    if (!nodes.has(node.id)) nodes.set(node.id, node);
    return nodes.get(node.id);
  };
  const addEdge = (source, target, kind, label) => {
    edges.push({ id: `e${edgeSeq++}`, source, target, kind, label: label || kind });
  };

  const definedTemplates = new Set(parsed.templates.map((t) => t.name));

  // Templates + their party fields.
  for (const t of parsed.templates) {
    addNode({ id: tplId(t.name), kind: 'template', label: t.name, meta: { external: false, fields: t.fields } });

    for (const pf of t.partyFields) {
      addNode({ id: partyId(t.name, pf), kind: 'party', label: pf, template: t.name });
    }

    // signatory / observer edges (only when the referenced id is a party field)
    for (const s of t.signatories) {
      if (t.partyFields.includes(s)) {
        addNode({ id: partyId(t.name, s), kind: 'party', label: s, template: t.name });
        addEdge(tplId(t.name), partyId(t.name, s), 'signatory');
      }
    }
    for (const o of t.observers) {
      if (t.partyFields.includes(o)) {
        addNode({ id: partyId(t.name, o), kind: 'party', label: o, template: t.name });
        addEdge(tplId(t.name), partyId(t.name, o), 'observer');
      }
    }

    // choices
    for (const ch of t.choices) {
      const cid = choiceId(t.name, ch.name);
      addNode({
        id: cid,
        kind: 'choice',
        label: ch.name,
        template: t.name,
        meta: { consuming: ch.consuming },
      });
      addEdge(tplId(t.name), cid, 'declares');

      // controller edges — link to party field when it resolves, else make a
      // param-party node so the controller is still visible.
      for (const c of ch.controllers) {
        let target;
        if (t.partyFields.includes(c)) {
          target = partyId(t.name, c);
          addNode({ id: target, kind: 'party', label: c, template: t.name });
        } else {
          target = `party:${t.name}.${c}#arg`;
          addNode({ id: target, kind: 'party', label: c, template: t.name, meta: { fromArg: true } });
        }
        addEdge(cid, target, 'controller');
      }

      // operation edges: choice -> target template
      for (const op of ch.operations) {
        if (!op.target) continue;
        addNode({
          id: tplId(op.target),
          kind: 'template',
          label: op.target,
          meta: { external: !definedTemplates.has(op.target) },
        });
        addEdge(cid, tplId(op.target), op.kind);
      }
    }
  }

  const warnings = parsed.diagnostics
    .filter((d) => d.severity !== 'info')
    .map((d) => d.message);

  return {
    meta: { module: parsed.module, source, warnings },
    nodes: [...nodes.values()],
    edges,
  };
}

export { OPERATION_KINDS };
