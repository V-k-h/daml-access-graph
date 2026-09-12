// src/analysis.js
//
// Static analyses over the NORMALIZED GRAPH IR (src/graph.js output). Because
// the browser parser, project mode, and the Daml-LF backend all emit the same
// schema, these analyses work identically on any of them - though results are
// only as sound as the graph feeding them.
//
// Analysis families:
//   * authorization    - who can act, and whether acting authority plausibly
//                        covers the authority a ledger action requires.
//   * visibility       - who can see each contract (signatories ∪ observers).
//   * information-flow - how authority/data propagates template -> template,
//                        including party-boundary crossings and cycles.
//   * keys             - contract-key maintainers as an authorization surface.
//   * interfaces       - the exercisable surface an `interface instance` adds
//                        to a template.
//
// A hard honesty limit: party nodes are keyed by *field name per template*
// (`party:Asset.issuer`). We cannot know whether `issuer` in one template is
// the same ledger Party as `from` in another. Cross-template authority is
// therefore reported, not asserted - every such finding says so.

/**
 * @typedef {Object} Finding
 * @property {'authorization'|'visibility'|'information-flow'|'keys'|'interfaces'} category
 * @property {'info'|'warning'|'error'} severity
 * @property {string} code
 * @property {string} message
 * @property {string[]} [subjects]   related node ids
 */

const LIFECYCLE_KINDS = new Set(['create', 'createAndExercise', 'exercise', 'exerciseByKey', 'archive']);
const READ_KINDS = new Set(['fetch', 'fetchByKey', 'lookupByKey', 'lookupAllByKey']);

const SEVERITY_RANK = { info: 0, warning: 1, error: 2 };

/**
 * Index the graph into a per-owner view that the analyses consume. An "owner"
 * is a template OR an interface: both declare choices with controllers, and an
 * interface choice is exercisable on every implementing template, so dropping
 * interfaces here would hide a real part of the access structure.
 *
 * @param {import('./graph.js').Graph} graph
 */
function indexGraph(graph) {
  const nodeById = new Map(graph.nodes.map((n) => [n.id, n]));

  /** label -> owner record */
  const owners = new Map();
  for (const n of graph.nodes) {
    if (n.kind !== 'template' && n.kind !== 'interface') continue;
    owners.set(n.label, {
      id: n.id,
      name: n.label,
      kind: n.kind,
      module: n.module || null,
      external: !!(n.meta && n.meta.external),
      signatories: new Set(),
      observers: new Set(),
      partyFields: new Set(
        ((n.meta && n.meta.fields) || []).filter((f) => f.isParty).map((f) => f.name)
      ),
      implements: new Set(),
      implementedBy: new Set(),
      key: null,
      // choiceName -> { id, consuming, controllers:Set, controllerNodes:[], ops:[] }
      choices: new Map(),
    });
  }

  const templateName = (id) => {
    const n = nodeById.get(id);
    return n ? n.label : id;
  };

  // pass 1: stakeholders, choice declarations, implements, keys
  for (const e of graph.edges) {
    const src = nodeById.get(e.source);
    const tgt = nodeById.get(e.target);
    if (!src || !tgt) continue;

    if (e.kind === 'signatory' && src.kind === 'template') {
      owners.get(src.label)?.signatories.add(tgt.label);
    } else if (e.kind === 'observer' && src.kind === 'template') {
      owners.get(src.label)?.observers.add(tgt.label);
    } else if (e.kind === 'implements') {
      owners.get(src.label)?.implements.add(tgt.label);
      owners.get(tgt.label)?.implementedBy.add(src.label);
    } else if (e.kind === 'keyed-by') {
      const o = owners.get(src.label);
      if (o) {
        o.key = {
          id: tgt.id,
          expr: (tgt.meta && tgt.meta.expr) || null,
          type: (tgt.meta && tgt.meta.type) || null,
          maintainers: new Set((tgt.meta && tgt.meta.maintainers) || []),
        };
      }
    } else if (e.kind === 'declares' && tgt.kind === 'choice') {
      const o = owners.get(src.label);
      if (o) {
        o.choices.set(tgt.label, {
          id: tgt.id,
          consuming: !(tgt.meta && tgt.meta.consuming === false),
          onInterface: !!(tgt.meta && tgt.meta.onInterface),
          controllers: new Set(),
          controllerNodes: [],
          // For an interface choice: implementing template -> the parties its
          // `interface instance` view record actually supplies to a
          // view-projected controller. Populated from `view-controller` edges.
          viewControllers: new Map(),
          ops: [],
        });
      }
    }
  }

  // choice -> owning template/interface, via the node's own `owner` field
  const choiceOwner = new Map();
  for (const n of graph.nodes) {
    if (n.kind === 'choice') {
      choiceOwner.set(n.id, { ownerName: n.owner || n.template, choiceName: n.label });
    }
  }

  // pass 2: controllers and operations
  for (const e of graph.edges) {
    const src = nodeById.get(e.source);
    const tgt = nodeById.get(e.target);
    if (!src || !tgt || src.kind !== 'choice') continue;
    const owner = choiceOwner.get(src.id);
    const ch = owner && owners.get(owner.ownerName)?.choices.get(owner.choiceName);
    if (!ch) continue;

    if (e.kind === 'view-controller') {
      const tname = (e.meta && e.meta.template) || tgt.template;
      if (!ch.viewControllers.has(tname)) ch.viewControllers.set(tname, []);
      ch.viewControllers.get(tname).push({
        party: tgt.label,
        viewField: (e.meta && e.meta.viewField) || null,
        expr: (e.meta && e.meta.expr) || null,
        heuristic: !!(e.meta && e.meta.heuristic),
      });
    } else if (e.kind === 'controller') {
      ch.controllers.add(tgt.label);
      ch.controllerNodes.push({
        label: tgt.label,
        // `fromArg`: a choice argument or a projection into a non-Party field,
        // i.e. NOT a template party field. Such a controller cannot be compared
        // against the template's declared stakeholders, and treating it as a
        // missing stakeholder was this analysis's single largest false-positive
        // source (37 of 42 findings on one real 39-choice factory template).
        fromArg: !!(tgt.meta && tgt.meta.fromArg),
        fromView: !!(tgt.meta && tgt.meta.fromView),
        derived: !!(tgt.meta && tgt.meta.derived),
      });
    } else if (LIFECYCLE_KINDS.has(e.kind) || READ_KINDS.has(e.kind)) {
      ch.ops.push({
        kind: e.kind,
        target: templateName(e.target),
        via: (e.meta && e.meta.via) || null,
      });
    }
  }

  // Back-compat alias: analyses written against templates-only keep working.
  const templates = owners;

  return { owners, templates, nodeById, choiceOwner };
}

const setsDiffer = (a, b) => a.size !== b.size || [...a].some((x) => !b.has(x));
const subset = (a, b) => [...a].every((x) => b.has(x));
const list = (s) => [...s].join(', ') || '∅';

/** Authorization: acting authority vs. required authority. */
export function analyzeAuthorization(graph) {
  const { owners } = indexGraph(graph);
  const findings = [];

  for (const t of owners.values()) {
    if (t.external) continue;

    for (const [cname, ch] of t.choices) {
      // acting authority of a choice = owner signatories ∪ choice controllers
      const acting = new Set([...t.signatories, ...ch.controllers]);

      if (ch.controllers.size === 0) {
        findings.push({
          category: 'authorization',
          severity: 'warning',
          code: 'no-controller',
          message: `Choice ${t.name}.${cname} has no controller - no party can exercise it.`,
          subjects: [ch.id],
        });
      }

      // An interface has no signatories of its own; its choices are authorized
      // against the implementing template, so signatory comparisons below do
      // not apply.
      if (t.kind === 'interface') continue;

      // a non-signatory-controlled consuming choice can archive the contract
      const fieldControllers = new Set(
        ch.controllerNodes.filter((c) => !c.fromArg).map((c) => c.label)
      );
      if (ch.consuming && fieldControllers.size > 0 && !subset(fieldControllers, t.signatories)) {
        const outsiders = [...fieldControllers].filter((c) => !t.signatories.has(c));
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
        const target = owners.get(op.target);
        if (!target || target.external) {
          findings.push({
            category: 'authorization',
            severity: 'info',
            code: 'create-external',
            message: `${t.name}.${cname} creates ${op.target} (external/unmodeled) - required signatories cannot be checked here.`,
            subjects: [ch.id],
          });
          continue;
        }
        // `create this` re-creates the same template with the same signatory
        // structure; the authority is definitionally present.
        if (target.name === t.name) continue;

        const required = target.signatories;
        // heuristic, field-name based; cannot resolve real party identity
        if (!subset(required, acting)) {
          findings.push({
            category: 'authorization',
            severity: 'warning',
            code: 'create-authority-gap',
            message:
              `${t.name}.${cname} creates ${op.target}, which requires signatories [${list(required)}]. ` +
              `Acting authority here is [${list(acting)}]. ` +
              (op.via ? `(Reached via ${op.via.join(' -> ')}.) ` : '') +
              `Field names differ - verify a party-propagation path supplies the missing authority (identity not provable from names).`,
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
  const { owners } = indexGraph(graph);
  const findings = [];

  for (const t of owners.values()) {
    if (t.external || t.kind === 'interface') continue;

    if (t.signatories.size > 0 && t.observers.size === 0) {
      findings.push({
        category: 'visibility',
        severity: 'info',
        code: 'no-observers',
        message: `${t.name} has no observers - only its signatories [${list(t.signatories)}] can see these contracts.`,
        subjects: [t.id],
      });
    }

    const stakeholders = new Set([...t.signatories, ...t.observers]);
    for (const [cname, ch] of t.choices) {
      for (const c of ch.controllerNodes) {
        // Only a declared PARTY FIELD of this template can be compared against
        // the template's stakeholders. A choice-argument controller is supplied
        // by the exercising party at call time; Daml makes it an observer of
        // the exercise, and it is not expected to appear in `signatory` /
        // `observer`. Flagging those produced pure noise.
        if (c.fromArg) continue;
        if (!stakeholders.has(c.label)) {
          findings.push({
            category: 'visibility',
            severity: 'info',
            code: 'controller-not-stakeholder',
            message:
              `Controller [${c.label}] of ${t.name}.${cname} is a party field of ${t.name} but is not an explicit ` +
              `signatory/observer (Daml makes controllers observers implicitly, but the model does not state it).`,
            subjects: [ch.id],
          });
        }
      }
    }
  }
  return findings;
}

/**
 * Contract keys as an authorization surface.
 *
 * A key's MAINTAINERS are the parties authorized to look the contract up by
 * key, and under non-unique keys (`lookupAllByKey`, Daml-LF 2.3) a single key
 * can resolve to several contracts. Both facts are authorization-relevant and
 * were entirely absent from the earlier graph schema.
 */
export function analyzeKeys(graph) {
  const { owners } = indexGraph(graph);
  const findings = [];

  for (const t of owners.values()) {
    if (t.external || t.kind === 'interface') continue;

    if (t.key) {
      if (t.key.maintainers.size === 0) {
        findings.push({
          category: 'keys',
          severity: 'warning',
          code: 'key-no-maintainer',
          message: `${t.name} has a contract key (${t.key.expr || 'expression not recovered'}) with no resolvable maintainer - key lookups cannot be authorized.`,
          subjects: [t.key.id],
        });
      } else if (!subset(t.key.maintainers, t.signatories)) {
        const outsiders = [...t.key.maintainers].filter((m) => !t.signatories.has(m));
        findings.push({
          category: 'keys',
          severity: 'warning',
          code: 'maintainer-not-signatory',
          message:
            `${t.name}: key maintainer(s) [${outsiders.join(', ')}] are not signatories [${list(t.signatories)}]. ` +
            `Daml requires maintainers to be signatories, so either the parse of the key/signatory expressions is ` +
            `incomplete or the model is inconsistent - worth checking by hand.`,
          subjects: [t.key.id, t.id],
        });
      }
    }

    // Reads through a non-unique key return a SET of contracts; the caller must
    // handle collisions. Worth surfacing at every call site.
    for (const [cname, ch] of t.choices) {
      for (const op of ch.ops) {
        if (op.kind !== 'lookupAllByKey') continue;
        findings.push({
          category: 'keys',
          severity: 'info',
          code: 'non-unique-key-read',
          message:
            `${t.name}.${cname} reads ${op.target} via \`lookupAllByKey\` (non-unique key) - it may match several ` +
            `contracts. Confirm the choice handles more than one result.` +
            (op.via ? ` (Reached via ${op.via.join(' -> ')}.)` : ''),
          subjects: [ch.id],
        });
      }
    }
  }
  return findings;
}

/**
 * Interfaces: the extra exercisable surface an `interface instance` adds.
 *
 * When template T implements interface I, every choice of I becomes
 * exercisable on T's contracts with I's controller - a party that need not
 * appear anywhere in T's own declaration. This is the fact the earlier
 * prototype dropped when it flagged interfaces as "not modeled".
 */
export function analyzeInterfaces(graph) {
  const { owners } = indexGraph(graph);
  const findings = [];

  for (const iface of owners.values()) {
    if (iface.kind !== 'interface') continue;

    // An external interface whose package WAS decoded (from a bundled DAR) has
    // real choices, so it is analysed like a local one. Only an interface with
    // no choices in the graph is genuinely unknown.
    if (iface.external && iface.choices.size === 0) {
      if (iface.implementedBy.size > 0) {
        findings.push({
          category: 'interfaces',
          severity: 'warning',
          code: 'external-interface-surface',
          message:
            `Interface ${iface.name} is implemented by [${list(iface.implementedBy)}] but declared outside this ` +
            `graph, and its package was not decoded. Its choices and their controllers are unknown here, so the ` +
            `exercisable surface of those templates is UNDER-reported. Point the tool at the DAR that declares ` +
            `it (project mode decodes DARs found under the roots).`,
          subjects: [iface.id, ...[...iface.implementedBy].map((n) => owners.get(n)?.id).filter(Boolean)],
        });
      }
      continue;
    }

    for (const [cname, ch] of iface.choices) {
      if (iface.implementedBy.size === 0) {
        findings.push({
          category: 'interfaces',
          severity: 'info',
          code: 'interface-unimplemented',
          message: `Interface choice ${iface.name}.${cname} has no implementing template in this graph.`,
          subjects: [ch.id],
        });
        continue;
      }
      for (const tname of iface.implementedBy) {
        const t = owners.get(tname);
        if (!t || t.external) continue;
        const controllers = [...ch.controllers];
        // An interface controller is usually a view projection (`view.admin`).
        // The implementing template's `interface instance ... view = ...`
        // record says which of ITS expressions supplies that field, so the
        // projection resolves to a concrete party rather than staying opaque.
        const viewProjected = ch.controllerNodes.some((c) => c.fromView);
        const resolved = ch.viewControllers.get(tname) || [];

        let how;
        if (resolved.length) {
          how =
            `, controlled on ${tname} by [${resolved.map((r) => `${tname}.${r.party}`).join(', ')}] ` +
            `(resolved through the view: ${resolved.map((r) => `${r.viewField} = ${r.expr}`).join('; ')})` +
            (resolved.some((r) => r.heuristic)
              ? '. That view field is bound to an applied expression, so the party was taken as its last argument - check it.'
              : '.');
        } else if (viewProjected) {
          how =
            `, controlled by [${controllers.join(', ') || '∅'}] - a view projection that ${tname}'s ` +
            `\`interface instance\` does not bind directly (nested record, or not written in the view), ` +
            `so the supplying field is not derivable here.`;
        } else {
          how = `, controlled by [${controllers.join(', ') || '∅'}].`;
        }

        findings.push({
          category: 'interfaces',
          severity: 'info',
          code: 'interface-choice-exercisable',
          message:
            `${ch.consuming ? 'Consuming' : 'Nonconsuming'} interface choice ${iface.name}.${cname} is exercisable ` +
            `on ${tname} contracts${how}` +
            (iface.external ? ` (${iface.name} is declared in an imported package.)` : ''),
          subjects: [ch.id, t.id],
        });

        // Now that the controller is a concrete party, it can be checked
        // against the implementing template's own stakeholders. A consuming
        // interface choice controlled by a party that is neither signatory nor
        // observer of the template is a real archive path the template's own
        // declaration never mentions.
        const stakeholders = new Set([...t.signatories, ...t.observers]);
        for (const r of resolved) {
          if (stakeholders.has(r.party)) continue;
          findings.push({
            category: 'interfaces',
            severity: ch.consuming ? 'warning' : 'info',
            code: 'interface-controller-not-stakeholder',
            message:
              `${iface.name}.${cname} is ${ch.consuming ? 'a CONSUMING choice ' : ''}exercisable on ${tname} by ` +
              `[${tname}.${r.party}] (via view field \`${r.viewField}\`), but that party is neither a signatory ` +
              `[${list(t.signatories)}] nor an observer [${list(t.observers)}] of ${tname}. ` +
              `The template's own declaration does not show this access path.`,
            subjects: [ch.id, t.id],
          });
        }
      }
    }
  }

  // A template whose only stakeholder is its signatory, but which implements an
  // interface, may be reachable by parties the template itself never names.
  for (const t of owners.values()) {
    if (t.kind !== 'template' || t.external || t.implements.size === 0) continue;
    // "Unknown" means no choices in the graph, NOT merely declared elsewhere:
    // a decoded bundled DAR makes an external interface fully visible.
    const unknown = [...t.implements].filter((i) => {
      const o = owners.get(i);
      return !o || (o.external && o.choices.size === 0);
    });
    if (unknown.length && unknown.length === t.implements.size) {
      findings.push({
        category: 'interfaces',
        severity: 'info',
        code: 'template-external-interfaces-only',
        message:
          `${t.name} implements only interfaces whose declarations are not in this graph ` +
          `[${unknown.join(', ')}] - none of their choices appear here, so its exercisable surface is incomplete.`,
        subjects: [t.id],
      });
    }
  }

  return findings;
}

/** Information flow: template -> template propagation, boundaries, cycles. */
export function analyzeInformationFlow(graph) {
  const { owners } = indexGraph(graph);
  const findings = [];

  // build lifecycle adjacency (create/exercise/archive), skip reads
  const adj = new Map();
  for (const t of owners.values()) adj.set(t.name, new Set());
  for (const t of owners.values()) {
    for (const [cname, ch] of t.choices) {
      for (const op of ch.ops) {
        if (!LIFECYCLE_KINDS.has(op.kind)) continue;
        if (op.target === t.name && op.kind === 'create') continue; // self-replacement is normal
        adj.get(t.name)?.add(op.target);

        // cross-party flow: acting parties -> resulting signatories
        const target = owners.get(op.target);
        if ((op.kind === 'create' || op.kind === 'createAndExercise') && target && !target.external) {
          const acting = new Set([...t.signatories, ...ch.controllers]);
          if (setsDiffer(acting, target.signatories)) {
            findings.push({
              category: 'information-flow',
              severity: 'info',
              code: 'cross-party-flow',
              message:
                `${t.name}.${cname} (acting: [${list(acting)}]) creates ${op.target} ` +
                `(signed by: [${list(target.signatories)}]) - authority crosses a party boundary.` +
                (op.via ? ` (Reached via ${op.via.join(' -> ')}.)` : ''),
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
      subjects: cyc.map((n) => owners.get(n)?.id).filter(Boolean),
    });
  }

  // terminal (leaf) templates: internal, defined, no outgoing lifecycle ops
  for (const t of owners.values()) {
    if (t.external || t.kind === 'interface') continue;
    const out = adj.get(t.name);
    if (out && out.size === 0 && t.choices.size > 0) {
      findings.push({
        category: 'information-flow',
        severity: 'info',
        code: 'terminal-template',
        message: `${t.name} performs no create/exercise on other templates - a lifecycle leaf.`,
        subjects: [t.id],
      });
    }
  }

  return findings;
}

/**
 * Run every analysis.
 *
 * On a repository-scale graph the raw finding list is long, and a list nobody
 * reads is worth nothing - so the result carries a `summary` (counts per code
 * and per severity) and supports filtering:
 *
 *   analyzeAll(graph, { suppress: ['no-observers'], minSeverity: 'warning' })
 *
 * Suppression is explicit and reported: `summary.suppressed` records what was
 * filtered out and why, so a quiet report can never be mistaken for a clean one.
 *
 * @param {import('./graph.js').Graph} graph
 * @param {{suppress?: string[], only?: string[], minSeverity?: 'info'|'warning'|'error'}} [options]
 */
export function analyzeAll(graph, options = {}) {
  const authorization = analyzeAuthorization(graph);
  const visibility = analyzeVisibility(graph);
  const informationFlow = analyzeInformationFlow(graph);
  const keys = analyzeKeys(graph);
  const interfaces = analyzeInterfaces(graph);

  const raw = [...authorization, ...visibility, ...informationFlow, ...keys, ...interfaces];

  const suppress = new Set(options.suppress || []);
  const only = options.only && options.only.length ? new Set(options.only) : null;
  const minRank = SEVERITY_RANK[options.minSeverity || 'info'] ?? 0;

  /** @type {Record<string, number>} */
  const suppressed = {};
  const kept = [];
  for (const f of raw) {
    if (suppress.has(f.code) || (only && !only.has(f.code)) || SEVERITY_RANK[f.severity] < minRank) {
      suppressed[f.code] = (suppressed[f.code] || 0) + 1;
      continue;
    }
    kept.push(f);
  }

  const byCode = {};
  const bySeverity = { info: 0, warning: 0, error: 0 };
  const byCategory = {};
  for (const f of kept) {
    byCode[f.code] = (byCode[f.code] || 0) + 1;
    bySeverity[f.severity]++;
    byCategory[f.category] = (byCategory[f.category] || 0) + 1;
  }

  const filter = (fs) => fs.filter((f) => kept.includes(f));

  return {
    authorization: filter(authorization),
    visibility: filter(visibility),
    informationFlow: filter(informationFlow),
    keys: filter(keys),
    interfaces: filter(interfaces),
    all: kept,
    summary: {
      total: kept.length,
      totalBeforeFilter: raw.length,
      byCode,
      bySeverity,
      byCategory,
      suppressed,
    },
  };
}
