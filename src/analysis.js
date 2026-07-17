// src/analysis.js
//
// Static analyses over the NORMALIZED GRAPH IR (src/graph.js output). Because
// both the browser parser and the Daml-LF backend emit the same schema, these
// analyses work identically on either — though results are only as sound as
// the graph feeding them (the browser prototype's graph is heuristic).
//
// Three analysis families:
//   * authorization    — who can act, and whether acting authority plausibly
//                        covers the authority a ledger action requires.
//   * visibility       — who can see each contract (signatories ∪ observers).
//   * information-flow — how authority/data propagates template -> template,
//                        including party-boundary crossings and cycles.
//
// A hard honesty limit: party nodes are keyed by *field name per template*
// (`party:Asset.issuer`). We cannot know whether `issuer` in one template is
// the same ledger Party as `from` in another. Cross-template authority is
// therefore reported, not asserted — every such finding says so.

/**
 * @typedef {Object} Finding
 * @property {'authorization'|'visibility'|'information-flow'} category
 * @property {'info'|'warning'|'error'} severity
 * @property {string} code
 * @property {string} message
 * @property {string[]} [subjects]   related node ids
 */

const LIFECYCLE_KINDS = new Set(['create', 'createAndExercise', 'exercise', 'exerciseByKey', 'archive']);
const READ_KINDS = new Set(['fetch', 'fetchByKey', 'lookupByKey']);

/**
 * Index the graph into a per-template view that the analyses consume.
 * @param {import('./graph.js').Graph} graph
 */
function indexGraph(graph) {
  const nodeById = new Map(graph.nodes.map((n) => [n.id, n]));

  /** template name -> { id, external, signatories:Set, observers:Set, choices:Map } */
  const templates = new Map();
  const templateNodes = graph.nodes.filter((n) => n.kind === 'template');
  for (const t of templateNodes) {
    templates.set(t.label, {
      id: t.id,
      name: t.label,
      external: !!(t.meta && t.meta.external),
      signatories: new Set(),
      observers: new Set(),
      // choiceName -> { id, consuming, controllers:Set, ops:[{kind,target}] }
      choices: new Map(),
    });
  }

  const partyLabel = (id) => {
    const n = nodeById.get(id);
    return n ? n.label : id;
  };
  const templateName = (id) => {
    const n = nodeById.get(id);
    return n ? n.label : id;
  };

  for (const e of graph.edges) {
    const src = nodeById.get(e.source);
    const tgt = nodeById.get(e.target);
    if (!src || !tgt) continue;

    if (e.kind === 'signatory' && src.kind === 'template') {
      templates.get(src.label)?.signatories.add(tgt.label);
    } else if (e.kind === 'observer' && src.kind === 'template') {
      templates.get(src.label)?.observers.add(tgt.label);
    } else if (e.kind === 'declares' && src.kind === 'template' && tgt.kind === 'choice') {
      const t = templates.get(src.label);
      if (t) {
        t.choices.set(tgt.label, {
          id: tgt.id,
          consuming: !(tgt.meta && tgt.meta.consuming === false),
          controllers: new Set(),
          ops: [],
        });
      }
    }
  }

  // choices belong to a template via their `template` field on the node.
  const choiceOwner = new Map(); // choiceNodeId -> {templateName, choiceName}
  for (const n of graph.nodes) {
    if (n.kind === 'choice') choiceOwner.set(n.id, { templateName: n.template, choiceName: n.label });
  }

  for (const e of graph.edges) {
    const src = nodeById.get(e.source);
    const tgt = nodeById.get(e.target);
    if (!src || !tgt) continue;

    if (e.kind === 'controller' && src.kind === 'choice') {
      const owner = choiceOwner.get(src.id);
      const ch = owner && templates.get(owner.templateName)?.choices.get(owner.choiceName);
      if (ch) ch.controllers.add(tgt.label);
    } else if ((LIFECYCLE_KINDS.has(e.kind) || READ_KINDS.has(e.kind)) && src.kind === 'choice') {
      const owner = choiceOwner.get(src.id);
      const ch = owner && templates.get(owner.templateName)?.choices.get(owner.choiceName);
      if (ch) ch.ops.push({ kind: e.kind, target: templateName(e.target) });
    }
  }

  return { templates, nodeById, partyLabel };
}

const setsDiffer = (a, b) => a.size !== b.size || [...a].some((x) => !b.has(x));
const subset = (a, b) => [...a].every((x) => b.has(x));

/** Authorization: acting authority vs. required authority. */
export function analyzeAuthorization(graph) {
  const { templates } = indexGraph(graph);
  const findings = [];

  for (const t of templates.values()) {
    if (t.external) continue;

    for (const [cname, ch] of t.choices) {
      // acting authority of a choice = template signatories ∪ choice controllers
      const acting = new Set([...t.signatories, ...ch.controllers]);

      if (ch.controllers.size === 0) {
        findings.push({
          category: 'authorization',
          severity: 'warning',
          code: 'no-controller',
          message: `Choice ${t.name}.${cname} has no controller — no party can exercise it.`,
          subjects: [ch.id],
        });
      }

      // a non-signatory-controlled consuming choice can archive the contract
      if (ch.consuming && ch.controllers.size > 0 && !subset(ch.controllers, t.signatories)) {
        const outsiders = [...ch.controllers].filter((c) => !t.signatories.has(c));
        findings.push({
          category: 'authorization',
          severity: 'info',
          code: 'nonsignatory-consuming',
          message: `Consuming choice ${t.name}.${cname} lets non-signatory party field(s) [${outsiders.join(', ')}] archive/replace the contract.`,
          subjects: [ch.id],
        });
      }

      // creates: the target's signatories must be authorized
      for (const op of ch.ops) {
        if (op.kind !== 'create' && op.kind !== 'createAndExercise') continue;
        const target = templates.get(op.target);
        if (!target || target.external) {
          findings.push({
            category: 'authorization',
            severity: 'info',
            code: 'create-external',
            message: `${t.name}.${cname} creates ${op.target} (external/unmodeled) — required signatories cannot be checked here.`,
            subjects: [ch.id],
          });
          continue;
        }
        const required = target.signatories;
        // heuristic, field-name based; cannot resolve real party identity
        if (!subset(required, acting)) {
          findings.push({
            category: 'authorization',
            severity: 'warning',
            code: 'create-authority-gap',
            message:
              `${t.name}.${cname} creates ${op.target}, which requires signatories [${[...required].join(', ') || '∅'}]. ` +
              `Acting authority here is [${[...acting].join(', ') || '∅'}]. ` +
              `Field names differ — verify a party-propagation path supplies the missing authority (identity not provable from names).`,
            subjects: [ch.id, target.id],
          });
        }
      }
    }
  }
  return findings;
}

/** Visibility: stakeholders per template. */
export function analyzeVisibility(graph) {
  const { templates } = indexGraph(graph);
  const findings = [];

  // parties (by field name) that are ever a signatory anywhere
  const everSignatory = new Set();
  for (const t of templates.values()) for (const s of t.signatories) everSignatory.add(s);

  for (const t of templates.values()) {
    if (t.external) continue;

    if (t.signatories.size > 0 && t.observers.size === 0) {
      findings.push({
        category: 'visibility',
        severity: 'info',
        code: 'no-observers',
        message: `${t.name} has no observers — only its signatories [${[...t.signatories].join(', ')}] can see these contracts.`,
        subjects: [t.id],
      });
    }

    const stakeholders = new Set([...t.signatories, ...t.observers]);
    for (const [cname, ch] of t.choices) {
      for (const c of ch.controllers) {
        // '#arg' controllers are choice arguments, not template fields — skip
        if (!stakeholders.has(c) && t.choices.has(cname)) {
          // is it even a field of this template? (party node exists as tpl field)
          findings.push({
            category: 'visibility',
            severity: 'info',
            code: 'controller-not-stakeholder',
            message: `Controller [${c}] of ${t.name}.${cname} is not an explicit signatory/observer of ${t.name} (Daml makes controllers observers implicitly, but the model does not state it).`,
            subjects: [ch.id],
          });
        }
      }
    }
  }
  return findings;
}

/** Information flow: template -> template propagation, boundaries, cycles. */
export function analyzeInformationFlow(graph) {
  const { templates } = indexGraph(graph);
  const findings = [];

  // build lifecycle adjacency (create/exercise/archive), skip reads
  const adj = new Map();
  for (const t of templates.values()) adj.set(t.name, new Set());
  for (const t of templates.values()) {
    for (const [cname, ch] of t.choices) {
      for (const op of ch.ops) {
        if (!LIFECYCLE_KINDS.has(op.kind)) continue;
        if (op.target === t.name && op.kind === 'create') continue; // self-replacement is normal
        adj.get(t.name)?.add(op.target);

        // cross-party flow: acting parties -> resulting signatories
        const target = templates.get(op.target);
        if ((op.kind === 'create' || op.kind === 'createAndExercise') && target && !target.external) {
          const acting = new Set([...t.signatories, ...ch.controllers]);
          if (setsDiffer(acting, target.signatories)) {
            findings.push({
              category: 'information-flow',
              severity: 'info',
              code: 'cross-party-flow',
              message: `${t.name}.${cname} (acting: [${[...acting].join(', ') || '∅'}]) creates ${op.target} (signed by: [${[...target.signatories].join(', ') || '∅'}]) — authority crosses a party boundary.`,
              subjects: [ch.id, target.id],
            });
          }
        }
      }
    }
  }

  // cycle detection over lifecycle adjacency (DFS)
  const WHITE = 0, GRAY = 1, BLACK = 2;
  const color = new Map([...adj.keys()].map((k) => [k, WHITE]));
  const cycles = [];
  const stack = [];
  const dfs = (u) => {
    color.set(u, GRAY);
    stack.push(u);
    for (const v of adj.get(u) || []) {
      if (!adj.has(v)) continue; // external target
      if (color.get(v) === GRAY) {
        const at = stack.indexOf(v);
        cycles.push(stack.slice(at).concat(v));
      } else if (color.get(v) === WHITE) {
        dfs(v);
      }
    }
    stack.pop();
    color.set(u, BLACK);
  };
  for (const k of adj.keys()) if (color.get(k) === WHITE) dfs(k);

  const seenCycle = new Set();
  for (const cyc of cycles) {
    const key = [...cyc].sort().join('>');
    if (seenCycle.has(key)) continue;
    seenCycle.add(key);
    findings.push({
      category: 'information-flow',
      severity: 'warning',
      code: 'lifecycle-cycle',
      message: `Contract lifecycle cycle detected: ${cyc.join(' → ')}. Confirm this terminates.`,
      subjects: cyc.map((n) => templates.get(n)?.id).filter(Boolean),
    });
  }

  // terminal (leaf) templates: internal, defined, no outgoing lifecycle ops
  for (const t of templates.values()) {
    if (t.external) continue;
    const out = adj.get(t.name);
    if (out && out.size === 0 && t.choices.size > 0) {
      findings.push({
        category: 'information-flow',
        severity: 'info',
        code: 'terminal-template',
        message: `${t.name} performs no create/exercise on other templates — a lifecycle leaf.`,
        subjects: [t.id],
      });
    }
  }

  return findings;
}

/**
 * Run every analysis.
 * @param {import('./graph.js').Graph} graph
 * @returns {{authorization: Finding[], visibility: Finding[], informationFlow: Finding[], all: Finding[]}}
 */
export function analyzeAll(graph) {
  const authorization = analyzeAuthorization(graph);
  const visibility = analyzeVisibility(graph);
  const informationFlow = analyzeInformationFlow(graph);
  return {
    authorization,
    visibility,
    informationFlow,
    all: [...authorization, ...visibility, ...informationFlow],
  };
}
