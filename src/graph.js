// src/graph.js
//
// Turns a ParseResult (from parser.js) into a NORMALIZED GRAPH JSON that the
// renderer - or the Daml-LF backend - can consume. The schema is documented in
// README.md ("Normalized graph schema").

/**
 * @typedef {Object} GraphNode
 * @property {string} id
 * @property {'template'|'party'|'choice'|'interface'|'key'} kind
 * @property {string} label
 * @property {string} [template]   owning template name (for party/choice/key)
 * @property {string} [interface]  owning interface name (for interface choices)
 * @property {string} [owner]      owning template OR interface label
 * @property {'template'|'interface'} [ownerKind]
 * @property {string} [module]     declaring module (project mode)
 * @property {Object} [meta]
 */

/**
 * @typedef {Object} GraphEdge
 * @property {string} id
 * @property {string} source
 * @property {string} target
 * @property {'declares'|'signatory'|'observer'|'controller'|'view-controller'|'implements'|'keyed-by'|'maintainer'|'create'|'createAndExercise'|'exercise'|'exerciseByKey'|'fetch'|'fetchByKey'|'lookupByKey'|'lookupAllByKey'|'archive'} kind
 * @property {string} label
 */

/**
 * @typedef {Object} Graph
 * @property {{module: string|null, source: string, warnings: string[], modules?: string[]}} meta
 * @property {GraphNode[]} nodes
 * @property {GraphEdge[]} edges
 */

import { partyRefs } from './parser.js';

const OPERATION_KINDS = new Set([
  'create', 'createAndExercise', 'exercise', 'exerciseByKey',
  'fetch', 'fetchByKey', 'lookupByKey', 'lookupAllByKey', 'archive',
]);

const STRUCTURAL_KINDS = new Set([
  'declares', 'signatory', 'observer', 'controller', 'view-controller',
  'implements', 'keyed-by', 'maintainer',
]);

const tplId = (name) => `tpl:${name}`;
const ifaceId = (name) => `iface:${name}`;
const partyId = (owner, field) => `party:${owner}.${field}`;
const choiceId = (owner, name) => `choice:${owner}.${name}`;
const keyId = (tpl) => `key:${tpl}`;

/**
 * @param {import('./parser.js').ParseResult} parsed
 * @param {{source?: string, module?: string|null}} [options]
 *        `source` is the provenance tag written to meta.source.
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
    const existing = nodes.get(node.id);
    if (!existing) {
      nodes.set(node.id, node);
      return node;
    }
    // A later, better-informed sighting upgrades an earlier placeholder.
    //
    // The rule is "more information wins", not "external becomes internal".
    // Keying only on the external flag lost real data: an operation edge that
    // mentions a template BEFORE its declaration is reached creates a stub
    // which `isInternal` already classifies correctly as `external: false`,
    // so the flag never changed and the upgrade was skipped. The declaration's
    // `module` and `meta.fields` were then dropped. On a 27 package Canton
    // repository that hit 23 of 28 templates, which emptied `partyFields` in
    // the analysis layer and left the renderer unable to group by module.
    //
    // Merge field by field instead, never letting an absent value overwrite a
    // present one. The one genuinely directional rule is the original: an
    // internal declaration must never be downgraded back to external.
    const mergedMeta = { ...existing.meta, ...node.meta };
    if (existing.meta && existing.meta.external === false) mergedMeta.external = false;
    const merged = { ...existing };
    for (const [k, v] of Object.entries(node)) {
      if (k === 'meta') continue;
      if (v !== undefined && v !== null) merged[k] = v;
    }
    merged.meta = mergedMeta;
    nodes.set(node.id, merged);
    return nodes.get(node.id);
  };
  const addEdge = (src, tgt, kind, label, meta) => {
    edges.push({
      id: `e${edgeSeq++}`,
      source: src,
      target: tgt,
      kind,
      label: label || kind,
      ...(meta ? { meta } : {}),
    });
  };

  /**
   * Emit the operation edges of one choice. Operations reached through helper
   * functions (`inheritedOperations`) are drawn with the same edge kind but
   * carry `meta.via`, the call path that justifies them, so a reader can tell
   * a direct `create` from one that happens two calls away.
   */
  const addOperationEdges = (cid, choice, isInternal) => {
    const emit = (op, via) => {
      if (!op.target) return;
      const asInterface = op.targetKind === 'interface';
      const nid = asInterface ? ifaceId(op.target) : tplId(op.target);
      addNode({
        id: nid,
        kind: asInterface ? 'interface' : 'template',
        label: op.target,
        meta: { external: !isInternal(op.target) },
      });
      addEdge(cid, nid, op.kind, op.kind, {
        ...(via ? { via } : {}),
        ...(op.resolvedVia ? { resolvedVia: op.resolvedVia } : {}),
      });
    };
    for (const op of choice.operations || []) emit(op, null);
    for (const op of choice.inheritedOperations || []) emit(op, op.via);
  };

  const interfaces = parsed.interfaces || [];
  const definedTemplates = new Set(parsed.templates.map((t) => t.name));
  const definedInterfaces = new Set(interfaces.map((i) => i.name));
  const isInternal = (name) => definedTemplates.has(name) || definedInterfaces.has(name);
  const interfaceByName = new Map(interfaces.map((i) => [i.name, i]));

  // ---------------------------------------------------------------- interfaces
  // Declared first so that `implements` edges from templates always land on a
  // node that already carries the interface's real metadata.
  for (const iface of interfaces) {
    addNode({
      id: ifaceId(iface.name),
      kind: 'interface',
      label: iface.name,
      ...(iface.module ? { module: iface.module } : {}),
      meta: {
        // An interface can be DECLARED elsewhere yet fully known, when its
        // package was decoded from a bundled DAR. That is a different state
        // from "referenced but unknown", and the analyses depend on it.
        external: !!iface.external,
        ...(iface.package ? { package: iface.package } : {}),
        viewtype: iface.viewtype || null,
        methods: iface.methods || [],
      },
    });

    for (const ch of iface.choices) {
      const cid = choiceId(iface.name, ch.name);
      addNode({
        id: cid,
        kind: 'choice',
        label: ch.name,
        interface: iface.name,
        owner: iface.name,
        ownerKind: 'interface',
        ...(iface.module ? { module: iface.module } : {}),
        meta: { consuming: ch.consuming, onInterface: true },
      });
      addEdge(ifaceId(iface.name), cid, 'declares');

      // Interface-choice controllers are typically view projections
      // (`(view this).admin`), normalized by the parser to `view.admin`.
      for (const c of ch.controllers) {
        const pid = partyId(iface.name, c);
        addNode({
          id: pid,
          kind: 'party',
          label: c,
          template: iface.name,
          owner: iface.name,
          ownerKind: 'interface',
          meta: { fromView: c.startsWith('view.') },
        });
        addEdge(cid, pid, 'controller');
      }

      addOperationEdges(cid, ch, isInternal);
    }
  }

  // ---------------------------------------------------------------- templates
  for (const t of parsed.templates) {
    addNode({
      id: tplId(t.name),
      kind: 'template',
      label: t.name,
      ...(t.module ? { module: t.module } : {}),
      meta: {
        external: false,
        fields: t.fields,
        ...(t.implements && t.implements.length ? { implements: t.implements } : {}),
        ...(t.key ? { keyed: true } : {}),
      },
    });

    for (const pf of t.partyFields) {
      addNode({ id: partyId(t.name, pf), kind: 'party', label: pf, template: t.name, owner: t.name, ownerKind: 'template' });
    }

    // signatory / observer edges. A ref is either a plain party field, or a
    // record projection like `spec.transferLeg.sender` (derived) - either way
    // we draw a node so the relationship is visible, tagging projections.
    const addPartyRef = (ref, kind) => {
      const id = partyId(t.name, ref);
      const derived = !t.partyFields.includes(ref);
      addNode({
        id,
        kind: 'party',
        label: ref,
        template: t.name,
        owner: t.name,
        ownerKind: 'template',
        ...(derived ? { meta: { derived: true } } : {}),
      });
      addEdge(tplId(t.name), id, kind);
    };
    for (const s of t.signatories) addPartyRef(s, 'signatory');
    for (const o of t.observers) addPartyRef(o, 'observer');

    // ------------------------------------------------------- interface instances
    // `implements` records that every choice of the interface is exercisable on
    // THIS template's contracts, with the interface choice's controller. That
    // is the access-structure fact the old prototype dropped entirely.
    const instanceFor = new Map(
      (t.interfaceInstances || []).map((ii) => [ii.interface, ii])
    );
    for (const iname of t.implements || []) {
      const inst = instanceFor.get(iname);
      const known = interfaceByName.get(iname);
      addNode({
        id: ifaceId(iname),
        kind: 'interface',
        label: iname,
        meta: {
          external: known ? !!known.external : !definedInterfaces.has(iname),
          ...(known && known.package ? { package: known.package } : {}),
        },
      });
      addEdge(tplId(t.name), ifaceId(iname), 'implements', 'implements', {
        ...(inst && inst.viewType ? { viewType: inst.viewType } : {}),
        ...(inst && Object.keys(inst.viewBindings || {}).length
          ? { viewBindings: inst.viewBindings }
          : {}),
      });

      // Resolve view-projected interface controllers to THIS template's fields.
      // An interface choice declares `controller (view this).admin`; the
      // `interface instance`'s view record says which of the template's own
      // expressions supplies `admin`. Joining the two turns "controlled by a
      // view projection we cannot place" into a concrete party.
      const iface = interfaceByName.get(iname);
      if (!iface || !inst) continue;
      for (const ch of iface.choices || []) {
        const cid = choiceId(iname, ch.name);
        for (const c of ch.controllers || []) {
          if (!c.startsWith('view.')) continue;
          const field = c.slice('view.'.length);
          // Only the leading component of a projection is a view field.
          const head = field.split('.')[0];
          const expr = (inst.viewBindings || {})[head];
          if (expr === undefined) {
            // Bound through a nested record, or not written in the view at all.
            continue;
          }
          let applied = false;
          const resolved = partyRefs(expr, { onApplied: () => { applied = true; } });
          if (resolved.length === 0) continue;
          for (const party of resolved) {
            const pid = partyId(t.name, party);
            addNode({
              id: pid,
              kind: 'party',
              label: party,
              template: t.name,
              owner: t.name,
              ownerKind: 'template',
              ...(t.partyFields.includes(party) ? {} : { meta: { derived: true } }),
            });
            addEdge(cid, pid, 'view-controller', `controller via ${iname}`, {
              template: t.name,
              viewField: head,
              expr,
              ...(applied ? { heuristic: 'view field bound to an applied expression' } : {}),
            });
          }
        }
      }
    }

    // ----------------------------------------------------------- contract key
    if (t.key) {
      const kid = keyId(t.name);
      addNode({
        id: kid,
        kind: 'key',
        label: `key ${t.name}`,
        template: t.name,
        owner: t.name,
        ownerKind: 'template',
        meta: {
          expr: t.key.expr,
          type: t.key.type,
          maintainers: t.key.maintainers,
        },
      });
      addEdge(tplId(t.name), kid, 'keyed-by');
      for (const m of t.key.maintainers) {
        const pid = partyId(t.name, m);
        addNode({
          id: pid,
          kind: 'party',
          label: m,
          template: t.name,
          owner: t.name,
          ownerKind: 'template',
          ...(t.partyFields.includes(m) ? {} : { meta: { derived: true } }),
        });
        addEdge(kid, pid, 'maintainer');
      }
    }

    // --------------------------------------------------------------- choices
    for (const ch of t.choices) {
      const cid = choiceId(t.name, ch.name);
      addNode({
        id: cid,
        kind: 'choice',
        label: ch.name,
        template: t.name,
        owner: t.name,
        ownerKind: 'template',
        ...(t.module ? { module: t.module } : {}),
        meta: { consuming: ch.consuming },
      });
      addEdge(tplId(t.name), cid, 'declares');

      // controller edges - link to party field when it resolves, else make a
      // param-party node so the controller is still visible.
      for (const c of ch.controllers) {
        let target;
        if (t.partyFields.includes(c)) {
          target = partyId(t.name, c);
          addNode({ id: target, kind: 'party', label: c, template: t.name, owner: t.name, ownerKind: 'template' });
        } else {
          // Not a template field: either a choice argument, or a projection
          // into a non-Party-typed record field. Tagged `fromArg` so analyses
          // do not mistake it for a missing stakeholder.
          target = `party:${t.name}.${c}#arg`;
          addNode({
            id: target,
            kind: 'party',
            label: c,
            template: t.name,
            owner: t.name,
            ownerKind: 'template',
            meta: { fromArg: true, projected: c.includes('.') },
          });
        }
        addEdge(cid, target, 'controller');
      }

      // operation edges: choice -> target template (direct and via helpers)
      addOperationEdges(cid, ch, isInternal);
    }
  }

  const warnings = parsed.diagnostics
    .filter((d) => d.severity !== 'info')
    .map((d) => d.message);

  return {
    meta: {
      module: options.module !== undefined ? options.module : parsed.module,
      source,
      warnings,
      ...(parsed.modules ? { modules: parsed.modules } : {}),
    },
    nodes: [...nodes.values()],
    edges,
  };
}

export { OPERATION_KINDS, STRUCTURAL_KINDS, tplId, ifaceId, partyId, choiceId, keyId };
