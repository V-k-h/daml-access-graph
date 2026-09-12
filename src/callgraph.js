// src/callgraph.js
//
// Attribute ledger operations performed by HELPER FUNCTIONS back to the choices
// that call them.
//
// Why this exists. Idiomatic Canton codebases keep choice bodies thin and put
// the actual `create`/`exercise` calls in shared top-level helpers:
//
//   -- Factory.daml
//   choice CreateTenantMirror : ContractId TenantMirror.TenantMirror
//     with contractData : TenantMirror.TenantData
//     controller admin
//     do Upsert.tenantMirror admin approver reader contractData
//
//   -- Internal/Upsert.daml
//   tenantMirror admin approver reader contractData = do
//     create TenantMirror.TenantMirror with …
//
// A parser that only reads choice bodies sees NO operation here. On the
// dlt-canton repo that accounted for almost every missing operational edge:
// 28 templates produced 2 `create` edges, because 26 of them are created
// inside `Internal/Upsert`.
//
// This pass walks the call graph from each choice body through the helper
// functions it references, transitively, and records the operations it reaches
// as `inheritedOperations`, each carrying the `via` call path that justifies
// it. Direct operations are left untouched, so the distinction between "this
// choice creates X" and "this choice calls a helper that creates X" survives
// into the graph and the findings.
//
// Honest limits:
//   * Reference collection is name-based (see parser.extractRefs), so a local
//     binding sharing a helper's name can produce a spurious edge. Every such
//     edge is tagged with `via`, so it is auditable rather than invisible.
//   * Higher-order calls (a helper passed as an argument) are not followed.
//   * Recursion is cut at the first repeat; depth is bounded.

const DEFAULT_MAX_DEPTH = 6;

/**
 * @typedef {Object} FunctionEntry
 * @property {string} name
 * @property {string} [module]
 * @property {import('./parser.js').Operation[]} operations
 * @property {string[]} refs
 */

/**
 * Build the lookup table used to resolve a reference to a function.
 *
 * Two spellings are indexed:
 *   `Internal.Upsert.tenantMirror` and `Upsert.tenantMirror`  (qualified)
 *   `tenantMirror`                                            (bare)
 *
 * A bare name that several modules define is recorded as ambiguous and is NOT
 * followed, so cross-module coincidences do not invent edges.
 *
 * @param {FunctionEntry[]} functions
 */
export function buildFunctionIndex(functions) {
  /** @type {Map<string, FunctionEntry[]>} */
  const index = new Map();
  const add = (key, fn) => {
    if (!index.has(key)) index.set(key, []);
    const list = index.get(key);
    if (!list.includes(fn)) list.push(fn);
  };

  for (const fn of functions) {
    add(fn.name, fn);
    if (fn.module) {
      add(`${fn.module}.${fn.name}`, fn);
      // Daml `import qualified Internal.Upsert as Upsert` and the common
      // `import qualified Internal.Upsert` both let a call site write
      // `Upsert.tenantMirror`, so index every module-name suffix.
      const segs = fn.module.split('.');
      for (let i = 0; i < segs.length; i++) {
        add(`${segs.slice(i).join('.')}.${fn.name}`, fn);
      }
    }
  }
  return index;
}

/**
 * Resolve one reference to a single function, preferring a same-module match.
 * Returns null when the name is unknown or ambiguous.
 */
function resolveRef(index, ref, fromModule) {
  const cands = index.get(ref);
  if (!cands || cands.length === 0) return null;
  if (cands.length === 1) return cands[0];
  const same = cands.filter((c) => c.module === fromModule);
  if (same.length === 1) return same[0];
  // Ambiguous across modules: refuse rather than guess.
  return null;
}

/**
 * Collect every operation reachable from a set of references.
 *
 * @param {Map<string, FunctionEntry[]>} index
 * @param {string[]} refs
 * @param {string|undefined} fromModule
 * @param {number} maxDepth
 * @returns {Array<import('./parser.js').Operation & {via: string[]}>}
 */
function reachableOperations(index, refs, fromModule, maxDepth) {
  const out = [];
  const visited = new Set();

  /** @type {Array<{refs: string[], module: string|undefined, path: string[]}>} */
  let frontier = [{ refs, module: fromModule, path: [] }];

  for (let depth = 0; depth < maxDepth && frontier.length; depth++) {
    const next = [];
    for (const item of frontier) {
      for (const ref of item.refs) {
        const fn = resolveRef(index, ref, item.module);
        if (!fn) continue;
        const fnKey = `${fn.module || ''}.${fn.name}`;
        if (visited.has(fnKey)) continue;
        visited.add(fnKey);

        const path = [...item.path, fn.module ? `${fn.module}.${fn.name}` : fn.name];
        for (const op of fn.operations) {
          out.push({ ...op, via: path });
        }
        next.push({ refs: fn.refs, module: fn.module, path });
      }
    }
    frontier = next;
  }

  return out;
}

/**
 * Attach `inheritedOperations` to every choice of every template/interface in
 * `model`, resolved through `model.functions`.
 *
 * Mutates and returns the model (it is an intermediate representation, and
 * callers pass it straight on to buildGraph).
 *
 * @param {{templates: any[], interfaces?: any[], functions?: any[], diagnostics: any[]}} model
 * @param {{maxDepth?: number}} [options]
 */
export function expandCalls(model, options = {}) {
  const maxDepth = options.maxDepth || DEFAULT_MAX_DEPTH;
  const functions = model.functions || [];
  if (functions.length === 0) {
    for (const owner of [...(model.templates || []), ...(model.interfaces || [])]) {
      for (const ch of owner.choices || []) ch.inheritedOperations = [];
    }
    model.callgraph = { functions: 0, edgesAdded: 0 };
    return model;
  }

  const index = buildFunctionIndex(functions);
  let edgesAdded = 0;
  let choicesTouched = 0;

  for (const owner of [...(model.templates || []), ...(model.interfaces || [])]) {
    for (const ch of owner.choices || []) {
      const inherited = reachableOperations(index, ch.refs || [], owner.module, maxDepth);
      // Do not duplicate an operation the choice already performs directly on
      // the same target.
      const direct = new Set((ch.operations || []).map((o) => `${o.kind}:${o.target}`));
      ch.inheritedOperations = inherited.filter((o) => {
        if (!o.target) return false;
        return !direct.has(`${o.kind}:${o.target}`);
      });
      if (ch.inheritedOperations.length) {
        choicesTouched++;
        edgesAdded += ch.inheritedOperations.length;
      }
    }
  }

  model.callgraph = { functions: functions.length, choicesTouched, edgesAdded, maxDepth };
  if (edgesAdded > 0) {
    model.diagnostics.push({
      severity: 'info',
      code: 'callgraph-attributed',
      message:
        `${edgesAdded} ledger operation(s) across ${choicesTouched} choice(s) were attributed via ` +
        `helper functions rather than appearing directly in the choice body. These edges carry a ` +
        `\`via\` call path; they are name-resolved, so verify any that look surprising.`,
    });
  }
  return model;
}
