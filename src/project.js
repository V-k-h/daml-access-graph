// src/project.js
//
// PROJECT MODE: parse a whole multi-package Daml codebase at once and resolve
// the references a single-file parse cannot.
//
// Why this exists. The per-file parser sees `exercise cid SomeChoice` and can
// only report "target unknown", because the target template's name is simply
// not present at the call site. Across a real repository that is most of the
// interesting edges: on a 27-package Canton codebase the single-file parser
// left the majority of `exercise`/`fetch` sites unresolved, so the access graph
// had templates but almost no inter-template structure.
//
// Project mode fixes that with information that IS available once every module
// is in hand:
//
//   1. A choice-name -> declaring template/interface index. `exercise cid Foo`
//      resolves to the unique declarer of `Foo`, or is reported as ambiguous
//      when several templates declare a choice of that name. It is never
//      guessed.
//   2. An interface index, so `interface instance Holding for X` links to the
//      real `Holding` declaration when it lives in a sibling module, and is
//      marked external only when it genuinely comes from an imported DAR.
//   3. Name-collision handling. Template names are unique per package, not per
//      repository, so a bare `tpl:Foo` node id can conflate two different
//      templates. Names that appear in more than one module are qualified as
//      `Module:Name`; unique names stay bare so ids remain readable.
//
// The output is the same ParseResult shape `buildGraph` already consumes, plus
// `modules`, so nothing downstream needs to know whether it is looking at one
// file or a whole repo.

import { parseDaml } from './parser.js';
import { expandCalls } from './callgraph.js';

/**
 * @typedef {Object} SourceFile
 * @property {string} path
 * @property {string} source
 */

/**
 * @typedef {Object} ProjectResult
 * @property {null} module                   always null: a project spans modules
 * @property {string[]} modules              module names, sorted
 * @property {import('./parser.js').Template[]} templates
 * @property {import('./parser.js').Interface[]} interfaces
 * @property {string[]} referencedTemplates
 * @property {string[]} referencedInterfaces
 * @property {import('./parser.js').Diagnostic[]} diagnostics
 * @property {Object} stats
 */

/**
 * Parse and cross-link a set of Daml source files.
 *
 * @param {SourceFile[]} files
 * @returns {ProjectResult}
 */
export function parseProject(files, options = {}) {
  /**
   * Interfaces and templates declared in packages OUTSIDE this source tree,
   * decoded from bundled DARs (see backend/dalf.js). Without these, a
   * `interface instance Holding for X` can only be reported as "declared
   * somewhere we cannot see", and the exercisable surface of X is unknown.
   */
  const externalPackages = options.externalPackages || [];

  /** @type {Array<{path: string, module: string, parsed: import('./parser.js').ParseResult}>} */
  const units = [];

  for (const f of files) {
    const parsed = parseDaml(f.source);
    const module = parsed.module || f.path;
    units.push({ path: f.path, module, parsed });
  }

  // ---------------------------------------------------------------- naming
  // A template/interface name is qualified as `Module:Name` only when the bare
  // name is declared in more than one module. Unique names stay bare, which
  // keeps node ids stable between single-file and project mode.
  const tplModules = new Map(); // bare name -> Set<module>
  const ifaceModules = new Map();
  for (const u of units) {
    for (const t of u.parsed.templates) {
      if (!tplModules.has(t.name)) tplModules.set(t.name, new Set());
      tplModules.get(t.name).add(u.module);
    }
    for (const i of u.parsed.interfaces) {
      if (!ifaceModules.has(i.name)) ifaceModules.set(i.name, new Set());
      ifaceModules.get(i.name).add(u.module);
    }
  }

  /**
   * Does a module name match an import qualifier used at a call site?
   * `exercise cid ArBorrowingBase.Archive…` may refer to module
   * `ArBorrowingBase` or, under `import qualified X.Y.ArBorrowingBase`, to any
   * module whose trailing segments match.
   */
  const moduleMatchesHint = (module, hint) =>
    module === hint || module.endsWith(`.${hint}`) || hint.endsWith(`.${module}`);

  const qualified = (index) => (module, name) =>
    index.get(name) && index.get(name).size > 1 ? `${module}:${name}` : name;
  const tplName = qualified(tplModules);
  const ifaceName = qualified(ifaceModules);

  /** bare name -> [{module, display}] */
  const tplIndex = new Map();
  const ifaceIndex = new Map();

  // External declarations are indexed FIRST so a local declaration of the same
  // name wins the same-module preference below.
  const externalInterfaces = [];
  for (const pkg of externalPackages) {
    const label = pkg.name ? `${pkg.name}${pkg.version ? `-${pkg.version}` : ''}` : 'imported package';
    for (const iface of pkg.interfaces || []) {
      if (!ifaceIndex.has(iface.name)) ifaceIndex.set(iface.name, []);
      ifaceIndex.get(iface.name).push({ module: iface.module || label, display: iface.name });
      externalInterfaces.push({ ...iface, external: true, package: label });
    }
  }

  for (const u of units) {
    for (const t of u.parsed.templates) {
      if (!tplIndex.has(t.name)) tplIndex.set(t.name, []);
      tplIndex.get(t.name).push({ module: u.module, display: tplName(u.module, t.name) });
    }
    for (const i of u.parsed.interfaces) {
      if (!ifaceIndex.has(i.name)) ifaceIndex.set(i.name, []);
      ifaceIndex.get(i.name).push({ module: u.module, display: ifaceName(u.module, i.name) });
    }
  }

  // -------------------------------------------------- choice -> declarer index
  // Built over DISPLAY names so a resolved target is directly usable as a node
  // label. Interface choices are included: `exercise cid Split_Utxo` targets an
  // interface, and that is a real edge, not a failure.
  /** choice name -> [{owner: display, ownerKind, modules: string[]}] */
  const choiceIndex = new Map();
  const addChoice = (choiceName, owner, ownerKind, module) => {
    if (!choiceIndex.has(choiceName)) choiceIndex.set(choiceName, []);
    const list = choiceIndex.get(choiceName);
    const existing = list.find((x) => x.owner === owner && x.ownerKind === ownerKind);
    if (existing) {
      if (!existing.modules.includes(module)) existing.modules.push(module);
    } else {
      list.push({ owner, ownerKind, modules: [module] });
    }
  };
  for (const iface of externalInterfaces) {
    for (const ch of iface.choices || []) {
      addChoice(ch.name, iface.name, 'interface', iface.module || iface.package);
    }
  }
  for (const u of units) {
    for (const t of u.parsed.templates) {
      const display = tplName(u.module, t.name);
      for (const ch of t.choices) addChoice(ch.name, display, 'template', u.module);
    }
    for (const i of u.parsed.interfaces) {
      const display = ifaceName(u.module, i.name);
      for (const ch of i.choices) addChoice(ch.name, display, 'interface', u.module);
    }
  }

  // ------------------------------------------------------------- rewrite pass
  const templates = [];
  const interfaces = [...externalInterfaces];
  const diagnostics = [];
  const referencedTemplates = new Set();
  const referencedInterfaces = new Set();
  const resolvedSites = new Set();  // sites project mode resolved
  const adjudicated = new Set();    // sites project mode reached a verdict on
  const stats = {
    files: files.length,
    modules: 0,
    templates: 0,
    interfaces: 0,
    choices: 0,
    opsTotal: 0,
    opsResolvedInFile: 0,
    opsResolvedByProject: 0,
    opsAmbiguous: 0,
    opsExternal: 0,
    collisions: 0,
  };

  /** Resolve a bare target template name seen in one module to a display name. */
  const resolveTargetName = (bare, module) => {
    const cands = tplIndex.get(bare);
    if (!cands || cands.length === 0) return { display: bare, external: true };
    // Prefer a declaration in the same module, else a unique one elsewhere.
    const sameModule = cands.find((c) => c.module === module);
    if (sameModule) return { display: sameModule.display, external: false };
    if (cands.length === 1) return { display: cands[0].display, external: false };
    return { display: bare, external: false, ambiguous: cands.map((c) => c.display) };
  };

  const rewriteOps = (ownerLabel, module, ops) => {
    for (const op of ops) {
      stats.opsTotal++;

      if (op.target) {
        // Target named at the call site: map it onto a display name.
        const r = resolveTargetName(op.target, module);
        if (r.ambiguous) {
          diagnostics.push({
            severity: 'warning',
            code: 'ambiguous-template-name',
            line: op.line,
            module,
            message:
              `${ownerLabel}: \`${op.kind}\` targets template \`${op.target}\`, which is declared in ` +
              `${r.ambiguous.length} modules [${r.ambiguous.join(', ')}]. Left unresolved rather than guessed.`,
          });
          stats.opsAmbiguous++;
          op.target = null;
          continue;
        }
        op.target = r.display;
        if (r.external) {
          referencedTemplates.add(r.display);
          stats.opsExternal++;
        }
        stats.opsResolvedInFile++;
        continue;
      }

      // No target at the call site. If the parser recovered a choice name, look
      // up which template or interface declares it.
      if (!op.choice) continue;
      adjudicated.add(`${module}:${op.line}:${op.choice}`);
      let owners = choiceIndex.get(op.choice) || [];

      // A module-qualified call site (`exercise cid ArBorrowingBase.Archive…`)
      // names the declaring module, which resolves the common case where
      // several mirror templates declare an identically named choice.
      if (owners.length > 1 && op.moduleHint) {
        const narrowed = owners.filter((o) => o.modules.some((m) => moduleMatchesHint(m, op.moduleHint)));
        if (narrowed.length >= 1) owners = narrowed;
      }

      if (owners.length === 1) {
        op.target = owners[0].owner;
        op.inferred = true;
        op.resolvedVia = owners[0].ownerKind === 'interface'
          ? 'project-choice-lookup(interface)'
          : 'project-choice-lookup';
        if (owners[0].ownerKind === 'interface') op.targetKind = 'interface';
        stats.opsResolvedByProject++;
        resolvedSites.add(`${module}:${op.line}:${op.choice}`);
      } else if (owners.length > 1) {
        diagnostics.push({
          severity: 'info',
          code: 'ambiguous-choice-owner',
          line: op.line,
          module,
          message:
            `${ownerLabel}: \`${op.kind}\` of choice \`${op.choice}\` - that choice name is declared by ` +
            `${owners.length} owners [${owners.map((o) => `${o.owner}${o.ownerKind === 'interface' ? ' (interface)' : ''}`).join(', ')}]. ` +
            `Not guessed.`,
        });
        stats.opsAmbiguous++;
      } else {
        diagnostics.push({
          severity: 'info',
          code: 'unknown-choice',
          line: op.line,
          module,
          message:
            `${ownerLabel}: \`${op.kind}\` of choice \`${op.choice}\` - no template or interface in this project ` +
            `declares it (likely an imported DAR).`,
        });
        stats.opsExternal++;
      }
    }
  };

  const functions = [];

  for (const u of units) {
    const { module, path, parsed } = u;

    // Helper functions first: their operation targets must carry display names
    // before the call-graph pass attributes them to calling choices.
    for (const fn of parsed.functions || []) {
      rewriteOps(`${module}.${fn.name}`, module, fn.operations);
      functions.push({ ...fn, module, path });
    }

    for (const iface of parsed.interfaces) {
      const display = ifaceName(module, iface.name);
      const label = `${display}`;
      for (const ch of iface.choices) {
        stats.choices++;
        rewriteOps(`${label}.${ch.name}`, module, ch.operations);
      }
      interfaces.push({ ...iface, name: display, module, path });
      stats.interfaces++;
    }

    for (const t of parsed.templates) {
      const display = tplName(module, t.name);
      if (display !== t.name) stats.collisions++;

      // Map implemented interface names onto display names; mark unresolvable
      // ones as genuinely external (imported DAR) rather than silently local.
      const impls = [];
      for (const iname of t.implements || []) {
        const cands = ifaceIndex.get(iname) || [];
        if (cands.length === 1) {
          impls.push(cands[0].display);
        } else if (cands.length > 1) {
          const same = cands.find((c) => c.module === module);
          impls.push(same ? same.display : iname);
        } else {
          impls.push(iname);
          referencedInterfaces.add(iname);
        }
      }

      for (const ch of t.choices) {
        stats.choices++;
        rewriteOps(`${display}.${ch.name}`, module, ch.operations);
      }

      templates.push({ ...t, name: display, implements: impls, module, path });
      stats.templates++;
    }
  }

  // ------------------------------------------------- diagnostics consolidation
  // A per-file diagnostic that project mode has since adjudicated is stale:
  // either it was resolved, or project mode has replaced it with a more
  // specific verdict (`ambiguous-choice-owner` / `unknown-choice`). Keeping
  // both would double-report the same call site.
  const projectHasTemplates = templates.length > 0 || interfaces.length > 0;
  for (const u of units) {
    for (const d of u.parsed.diagnostics) {
      if (d.code === 'ambiguous-target' && d.line != null) {
        const m = d.message.match(/choice `([^`]+)`/);
        if (m && adjudicated.has(`${u.module}:${d.line}:${m[1]}`)) continue;
      }
      // A module with no templates is unremarkable in a project (test scripts,
      // pure calculation modules); it is only notable for a single-file parse.
      if (d.code === 'no-templates' && projectHasTemplates) continue;
      // `external-interface` is answered by the project-wide interface index.
      if (d.code === 'external-interface') {
        const m = d.message.match(/Interface `([^`]+)`/);
        if (m && ifaceIndex.has(m[1])) continue;
      }
      // `external-template` likewise.
      if (d.code === 'external-template') {
        const m = d.message.match(/template `([^`]+)`/);
        if (m && tplIndex.has(m[1])) continue;
      }
      diagnostics.push({ ...d, module: u.module, path: u.path });
    }
  }

  const modules = [...new Set(units.map((u) => u.module))].sort();
  stats.modules = modules.length;
  stats.externalPackages = externalPackages.length;
  stats.externalInterfaces = externalInterfaces.length;

  if (externalInterfaces.length) {
    diagnostics.push({
      severity: 'info',
      code: 'external-packages-decoded',
      message:
        `Resolved ${externalInterfaces.length} interface(s) from ${externalPackages.length} bundled ` +
        `package(s): ${[...new Set(externalInterfaces.map((i) => i.package))].join(', ')}. ` +
        `Their choices and controllers are now part of the graph.`,
    });
  }

  if (stats.collisions > 0) {
    diagnostics.push({
      severity: 'info',
      code: 'qualified-names',
      message:
        `${stats.collisions} template(s) share a name across modules and were qualified as ` +
        `\`Module:Name\` so their graph nodes stay distinct.`,
    });
  }

  const result = {
    module: null,
    modules,
    templates,
    interfaces,
    functions,
    referencedTemplates: [...referencedTemplates].sort(),
    referencedInterfaces: [...referencedInterfaces].sort(),
    diagnostics,
    stats,
  };

  // Attribute helper-function operations back to the choices that call them.
  expandCalls(result);
  stats.functions = functions.length;
  stats.opsViaHelpers = result.callgraph ? result.callgraph.edgesAdded : 0;

  return result;
}
