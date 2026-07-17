// backend/lf-parser.js
//
// Parse the textual Daml-LF produced by `daml damlc inspect <dar|dalf>` into
// the SAME structural model shape that the browser parser (src/parser.js)
// produces, so both feed the shared graph builder unchanged.
//
// Why this is better than the browser regex parser:
//   * It reads COMPILED, typechecked Daml-LF, so signatory/observer/controller
//     party references and operation target templates are recovered soundly
//     (target templates come from explicit `@Module:Template` type applications).
//
// Caveat we do NOT hide: the *textual* pretty-print format of `damlc inspect`
// is not a stable public API and varies across Daml-LF versions. This parser
// targets the Daml-LF 2.x style output. If it recovers nothing from non-empty
// input, it says so via a diagnostic rather than silently returning an empty
// model. For a fully version-proof backend, decode the DALF protobuf directly
// (see README "Roadmap").

/**
 * Structural model, identical shape to src/parser.js ParseResult so buildGraph
 * can consume it. Adds `modules` (LF archives can hold several).
 *
 * @typedef {import('../src/parser.js').ParseResult & {modules: string[]}} LfModel
 */

const OP_PATTERNS = [
  // order matters: longer/more-specific keywords first
  { kind: 'createAndExercise', re: /\bcreate_and_exercise\b/g },
  { kind: 'exerciseByKey', re: /\bexercise_by_key\b/g },
  { kind: 'fetchByKey', re: /\bfetch_by_key\b/g },
  { kind: 'lookupByKey', re: /\blookup_by_key\b/g },
  { kind: 'exercise', re: /\bexercise\b/g },
  { kind: 'create', re: /\bcreate\b/g },
  { kind: 'fetch', re: /\bfetch\b/g },
];

/**
 * @param {string} lfText  output of `daml damlc inspect`
 * @returns {LfModel}
 */
export function parseLfPretty(lfText) {
  const diagnostics = [];
  const text = lfText || '';

  const moduleNames = [];
  const templates = [];
  const referenced = new Set();

  // Split into modules: `module <Name> where`
  const moduleRe = /\bmodule\s+([\w.]+)\s+where\b/g;
  const modStarts = [];
  let mm;
  while ((mm = moduleRe.exec(text))) {
    modStarts.push({ name: mm[1], index: mm.index + mm[0].length });
  }

  for (let i = 0; i < modStarts.length; i++) {
    const start = modStarts[i];
    const end = i + 1 < modStarts.length ? modStarts[i + 1].index : text.length;
    const body = text.slice(start.index, end);
    moduleNames.push(start.name);
    parseModule(start.name, body, templates, referenced, diagnostics);
  }

  if (modStarts.length === 0 && text.trim()) {
    diagnostics.push({
      severity: 'error',
      code: 'lf-no-modules',
      message: 'No `module … where` blocks found in the Daml-LF text. The `damlc inspect` output format may differ from the expected Daml-LF 2.x style.',
    });
  }
  if (modStarts.length > 0 && templates.length === 0) {
    diagnostics.push({
      severity: 'warning',
      code: 'lf-no-templates',
      message: 'Modules were found but no `template (this: …) = { … }` blocks were recovered. The pretty-print format may have changed.',
    });
  }

  const defined = new Set(templates.map((t) => t.name));
  for (const r of referenced) {
    if (!defined.has(r)) {
      diagnostics.push({
        severity: 'info',
        code: 'external-template',
        message: `Referenced template \`${r}\` is defined in another package/module.`,
      });
    }
  }

  return {
    module: moduleNames[0] || null,
    modules: moduleNames,
    templates,
    referencedTemplates: [...referenced].sort(),
    diagnostics,
  };
}

function parseModule(moduleName, body, templates, referenced, diagnostics) {
  // record types: `record @serializable Name = { f1: T1, f2: T2 };`
  // used to know which fields are Party-typed.
  const recordParty = new Map(); // recordName -> Set(partyFieldNames)
  const recRe = /record\s+(?:@serializable\s+)?(\w+)\s*=\s*\{([^}]*)\}/g;
  let rm;
  while ((rm = recRe.exec(body))) {
    const fields = rm[2];
    const parties = new Set();
    const fieldRe = /(\w+)\s*:\s*([^,]+)/g;
    let fm;
    while ((fm = fieldRe.exec(fields))) {
      if (/\bParty\b/.test(fm[2])) parties.add(fm[1]);
    }
    recordParty.set(rm[1], parties);
  }

  // templates: `template (this: Name) = { ... };` — brace-matched body.
  const tplHeadRe = /template\s*\(\s*this\s*:\s*(\w+)\s*\)\s*=\s*\{/g;
  let th;
  while ((th = tplHeadRe.exec(body))) {
    const name = th[1];
    const openBrace = th.index + th[0].length - 1;
    const tbody = braceSlice(body, openBrace);
    if (tbody == null) {
      diagnostics.push({
        severity: 'warning',
        code: 'lf-unbalanced-template',
        message: `Template \`${name}\`: could not find a balanced \`{ … }\` body.`,
      });
      continue;
    }
    const tpl = parseTemplateBody(name, tbody, recordParty.get(name) || new Set(), referenced);
    templates.push(tpl);
  }
}

function parseTemplateBody(name, tbody, recordPartyFields, referenced) {
  const partyFields = new Set(recordPartyFields);

  // signatories <expr>;  observers <expr>;  (stop at the first ';')
  const sigExpr = fieldExpr(tbody, 'signatories');
  const obsExpr = fieldExpr(tbody, 'observers');
  const signatories = projectionFields(sigExpr);
  const observers = projectionFields(obsExpr);
  // signatory/observer projections are, by construction, template fields.
  signatories.forEach((f) => partyFields.add(f));
  observers.forEach((f) => partyFields.add(f));

  const choices = parseChoices(tbody, partyFields, referenced);

  return {
    name,
    fields: [...partyFields].map((f) => ({ name: f, type: 'Party', isParty: true })),
    partyFields: [...partyFields],
    signatories,
    observers,
    choices,
    line: 0,
  };
}

/** Slice `choice … choice … };` region into individual choice blocks. */
function parseChoices(tbody, partyFields, referenced) {
  const heads = [];
  const headRe = /\bchoice\s+(Consuming|NonConsuming|PreConsuming|PostConsuming)\s+(\w+)\b/g;
  let ch;
  while ((ch = headRe.exec(tbody))) {
    heads.push({ consuming: !/^Non/.test(ch[1]), name: ch[2], index: ch.index });
  }

  const choices = [];
  for (let i = 0; i < heads.length; i++) {
    const start = heads[i].index;
    const end = i + 1 < heads.length ? heads[i + 1].index : tbody.length;
    const cbody = tbody.slice(start, end);

    // controllers <expr> up to the next `, ` field or `to`
    const ctrlExpr = fieldExprBounded(cbody, 'controllers');
    const controllers = projectionFields(ctrlExpr);
    controllers.forEach((f) => partyFields.has(f) || null); // no-op; membership decided in graph

    const operations = parseOperations(cbody, referenced);

    choices.push({
      name: heads[i].name,
      consuming: heads[i].consuming,
      controllers,
      operations,
      line: 0,
    });
  }
  return choices;
}

function parseOperations(cbody, referenced) {
  const ops = [];
  for (const { kind, re } of OP_PATTERNS) {
    re.lastIndex = 0;
    let m;
    while ((m = re.exec(cbody))) {
      const after = cbody.slice(m.index + m[0].length, m.index + m[0].length + 80);
      const target = inferLfTarget(after);
      if (target) referenced.add(target);
      // `exercise @T Archive` -> treat as an archive operation
      let opKind = kind;
      if (kind === 'exercise' && /@[^\s(]*:\w+\s+Archive\b/.test(after)) opKind = 'archive';
      ops.push({ kind: opKind, target: target || null, inferred: !!target, line: 0 });
    }
  }
  return ops;
}

/** From `@Pkg:Mod.Sub:Template ...` (or `@Mod:Template`) grab `Template`. */
function inferLfTarget(after) {
  const m = after.match(/@\s*(?:'[^']+':)?[\w.]*:(\w+)/);
  return m ? m[1] : null;
}

/** Capture a top-level template field expression `name <expr>;`. */
function fieldExpr(tbody, keyword) {
  const re = new RegExp(`\\b${keyword}\\b`);
  const m = tbody.match(re);
  if (!m) return '';
  const from = m.index + m[0].length;
  const semi = tbody.indexOf(';', from);
  return tbody.slice(from, semi === -1 ? tbody.length : semi);
}

/**
 * Capture a choice field `name <expr>` bounded by the next choice-field
 * separator (`, observers` / `, authorizers`) or the update body keyword `to`.
 *
 * Bracket-depth-aware: a boundary token only counts at depth 0, so a party
 * field named `to` appearing as a `{to}` projection inside the expression is
 * NOT mistaken for the update-body `to` keyword.
 */
function fieldExprBounded(cbody, keyword) {
  const re = new RegExp(`\\b${keyword}\\b`);
  const m = cbody.match(re);
  if (!m) return '';
  const from = m.index + m[0].length;
  const rest = cbody.slice(from);

  let depth = 0;
  for (let i = 0; i < rest.length; i++) {
    const c = rest[i];
    if (c === '(' || c === '[' || c === '{') depth++;
    else if (c === ')' || c === ']' || c === '}') depth = Math.max(0, depth - 1);
    else if (depth === 0) {
      const ahead = rest.slice(i);
      if (/^,\s*(observers|authorizers|controllers)\b/.test(ahead)) return rest.slice(0, i);
      if (/^\bto\b/.test(ahead) && /^to\s/.test(ahead)) return rest.slice(0, i);
    }
  }
  return rest;
}

/** All record-projection field names in an expr: `Mod:Type {field} expr` -> field. */
function projectionFields(expr) {
  const out = [];
  const seen = new Set();
  const re = /\{\s*(\w+)\s*\}/g;
  let m;
  while ((m = re.exec(expr || ''))) {
    if (!seen.has(m[1])) {
      seen.add(m[1]);
      out.push(m[1]);
    }
  }
  return out;
}

/** Return the substring inside the braces starting at `open` (index of `{`). */
function braceSlice(text, open) {
  let depth = 0;
  for (let i = open; i < text.length; i++) {
    const c = text[i];
    if (c === '{') depth++;
    else if (c === '}') {
      depth--;
      if (depth === 0) return text.slice(open + 1, i);
    }
  }
  return null;
}
