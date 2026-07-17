// src/parser.js
//
// Best-effort, regex/line-based parser for Daml source.
//
// IMPORTANT: This parser is a PROTOTYPE. It is NOT a sound Daml frontend.
// It uses heuristics (regexes + indentation tracking), so it will miss or
// misread some valid Daml. Every place where it gives up or guesses is
// reported in `diagnostics` with a severity, so the UI can surface it
// honestly instead of pretending the model is complete.

/**
 * @typedef {Object} Diagnostic
 * @property {'info'|'warning'|'error'} severity
 * @property {string} message
 * @property {number} [line]   1-based line number in the (stripped) source
 * @property {string} [code]   short machine code, e.g. "old-controller-can"
 */

/**
 * @typedef {Object} Operation
 * @property {'create'|'createAndExercise'|'exercise'|'exerciseByKey'|'fetch'|'fetchByKey'|'lookupByKey'|'archive'} kind
 * @property {string|null} target   inferred target template name, or null if ambiguous
 * @property {boolean} inferred     true if target was guessed heuristically
 * @property {number} line
 */

/**
 * @typedef {Object} Choice
 * @property {string} name
 * @property {boolean} consuming    false => nonconsuming
 * @property {string[]} controllers party-ish identifiers found after `controller`
 * @property {Operation[]} operations
 * @property {number} line
 */

/**
 * @typedef {Object} Field
 * @property {string} name
 * @property {string} type
 * @property {boolean} isParty   true if the field's type mentions Party
 */

/**
 * @typedef {Object} Template
 * @property {string} name
 * @property {Field[]} fields
 * @property {string[]} partyFields   names of fields whose type is Party
 * @property {string[]} signatories
 * @property {string[]} observers
 * @property {Choice[]} choices
 * @property {number} line
 */

/**
 * @typedef {Object} ParseResult
 * @property {string|null} module
 * @property {Template[]} templates
 * @property {string[]} referencedTemplates  target templates referenced by operations
 * @property {Diagnostic[]} diagnostics
 */

const OP_KINDS = [
  'createAndExercise',
  'exerciseByKey',
  'lookupByKey',
  'fetchByKey',
  'exercise',
  'create',
  'fetch',
  'archive',
];

/** Strip `-- line` and `{- block -}` comments, preserving line count. */
function stripComments(source) {
  // Remove block comments but keep newlines so line numbers stay stable.
  let out = source.replace(/\{-[\s\S]*?-\}/g, (m) => m.replace(/[^\n]/g, ' '));
  // Remove line comments.
  out = out
    .split('\n')
    .map((line) => line.replace(/--.*$/, ''))
    .join('\n');
  return out;
}

/** Count leading spaces (tabs counted as 1) for a line. */
function indentOf(line) {
  const m = line.match(/^(\s*)/);
  return m ? m[1].replace(/\t/g, ' ').length : 0;
}

/**
 * Split a field region on newlines and on commas that sit at paren/bracket
 * depth 0, so `owner : Party, sig : (Party, Party)` -> two decls while the
 * inner tuple comma is preserved.
 */
function splitTopLevel(region) {
  const parts = [];
  let buf = '';
  let depth = 0;
  for (const ch of region) {
    if (ch === '(' || ch === '[' || ch === '{') depth++;
    else if (ch === ')' || ch === ']' || ch === '}') depth = Math.max(0, depth - 1);
    if ((ch === '\n' || ch === ',') && depth === 0) {
      parts.push(buf);
      buf = '';
    } else {
      buf += ch;
    }
  }
  if (buf) parts.push(buf);
  return parts;
}

/** Pull identifier-ish tokens (party candidates) out of an expression. */
function extractIdentifiers(expr) {
  if (!expr) return [];
  // Drop list/tuple/paren syntax noise, keep dotted paths as their head.
  const tokens = expr.match(/[A-Za-z_][A-Za-z0-9_']*/g) || [];
  const keywords = new Set([
    'do', 'let', 'in', 'if', 'then', 'else', 'with', 'this',
    'return', 'pure', 'map', 'fmap', 'fromList', 'toList',
  ]);
  const seen = new Set();
  const out = [];
  for (const t of tokens) {
    if (keywords.has(t)) continue;
    // Skip obviously type-level / constructor-only leading caps like `Set`, `Some`.
    if (seen.has(t)) continue;
    seen.add(t);
    out.push(t);
  }
  return out;
}

/**
 * Parse Daml source into a structural model.
 * @param {string} rawSource
 * @returns {ParseResult}
 */
export function parseDaml(rawSource) {
  /** @type {Diagnostic[]} */
  const diagnostics = [];
  const source = stripComments(rawSource || '');
  const lines = source.split('\n');

  const moduleMatch = source.match(/\bmodule\s+([\w.]+)\s+where/);
  const moduleName = moduleMatch ? moduleMatch[1] : null;
  if (!moduleName) {
    diagnostics.push({
      severity: 'info',
      code: 'no-module',
      message: 'No `module <Name> where` header found; treating input as a loose fragment.',
    });
  }

  // Flag legacy `controller ... can` blocks — only partially supported.
  lines.forEach((line, i) => {
    if (/\bcontroller\b.*\bcan\b/.test(line)) {
      diagnostics.push({
        severity: 'warning',
        code: 'old-controller-can',
        line: i + 1,
        message: 'Legacy `controller … can` choice syntax detected — choices inside it may be parsed incompletely. Prefer the `choice … controller …` form.',
      });
    }
  });

  // Flag interfaces — not modeled.
  const ifaceRe = /\binterface\s+(\w+)\b/g;
  let ifaceM;
  while ((ifaceM = ifaceRe.exec(source))) {
    diagnostics.push({
      severity: 'warning',
      code: 'interface-unsupported',
      message: `Interface \`${ifaceM[1]}\` found — interfaces are not modeled by this prototype.`,
    });
  }

  // Locate top-level template starts. `template Name` where `template` is the
  // first token on the line (ignoring leading whitespace).
  const templateStarts = [];
  lines.forEach((line, i) => {
    const m = line.match(/^\s*template\s+(\w+)\b/);
    if (m) templateStarts.push({ name: m[1], line: i });
  });

  const templates = [];
  const referenced = new Set();

  for (let t = 0; t < templateStarts.length; t++) {
    const start = templateStarts[t];
    const end = t + 1 < templateStarts.length ? templateStarts[t + 1].line : lines.length;
    const body = lines.slice(start.line, end);
    const tpl = parseTemplate(start.name, body, start.line, diagnostics, referenced);
    templates.push(tpl);
  }

  if (templates.length === 0) {
    diagnostics.push({
      severity: 'info',
      code: 'no-templates',
      message: 'No `template` definitions found.',
    });
  }

  // Referenced templates that are not defined locally are external.
  const defined = new Set(templates.map((x) => x.name));
  for (const r of referenced) {
    if (!defined.has(r)) {
      diagnostics.push({
        severity: 'info',
        code: 'external-template',
        message: `Referenced template \`${r}\` is not defined in this source (external or imported).`,
      });
    }
  }

  return {
    module: moduleName,
    templates,
    referencedTemplates: [...referenced].sort(),
    diagnostics,
  };
}

/**
 * @param {string} name
 * @param {string[]} body       lines of the template block
 * @param {number} baseLine     0-based offset of body[0] in the whole file
 * @param {Diagnostic[]} diagnostics
 * @param {Set<string>} referenced
 * @returns {Template}
 */
function parseTemplate(name, body, baseLine, diagnostics, referenced) {
  const fields = [];
  const partyFields = [];
  let signatories = [];
  let observers = [];

  // --- field block: the region between the `with` and the template's `where`.
  // Handles both idiomatic multi-line layout and single-line
  // `template T with x : Ty where`. Fields may be newline- or comma-separated;
  // splitting is paren/bracket-aware so tuple types like `(Party, Party)` and
  // `[Party]` stay intact.
  const joined = body.join('\n');
  const wIdx = joined.search(/\bwith\b/);
  let region = null;
  if (wIdx !== -1) {
    const afterWith = joined.slice(wIdx + 'with'.length);
    const whereRel = afterWith.search(/\bwhere\b/);
    region = whereRel === -1 ? afterWith : afterWith.slice(0, whereRel);
  }
  if (region && region.trim()) {
    for (const piece of splitTopLevel(region)) {
      const decl = piece.trim();
      if (!decl) continue;
      const fm = decl.match(/^([\w']+)\s*:\s*([\s\S]+?)\s*$/);
      if (fm) {
        const fname = fm[1];
        const ftype = fm[2].replace(/\s+/g, ' ').trim();
        const isParty = /\bParty\b/.test(ftype);
        fields.push({ name: fname, type: ftype, isParty });
        if (isParty) partyFields.push(fname);
      } else {
        diagnostics.push({
          severity: 'info',
          code: 'unparsed-field',
          line: baseLine + 1,
          message: `Template \`${name}\`: could not parse field declaration: \`${decl}\``,
        });
      }
    }
  } else {
    diagnostics.push({
      severity: 'warning',
      code: 'no-field-block',
      line: baseLine + 1,
      message: `Template \`${name}\`: could not locate a \`with … where\` field block.`,
    });
  }

  // --- signatory / observer (may span the rest of a line after the keyword) ---
  for (const line of body) {
    const sig = line.match(/^\s*signatory\s+(.+?)\s*$/);
    if (sig) signatories.push(...extractIdentifiers(sig[1]));
    const obs = line.match(/^\s*observer\s+(.+?)\s*$/);
    if (obs) observers.push(...extractIdentifiers(obs[1]));
  }
  signatories = [...new Set(signatories)];
  observers = [...new Set(observers)];

  if (signatories.length === 0) {
    diagnostics.push({
      severity: 'warning',
      code: 'no-signatory',
      line: baseLine + 1,
      message: `Template \`${name}\` has no detectable \`signatory\`.`,
    });
  }

  // --- choices ---
  const choices = parseChoices(name, body, baseLine, diagnostics, referenced);

  return {
    name,
    fields,
    partyFields,
    signatories,
    observers,
    choices,
    line: baseLine + 1,
  };
}

/**
 * Find `choice`/`nonconsuming choice` blocks within a template body, then
 * parse controller + ledger operations out of each.
 */
function parseChoices(templateName, body, baseLine, diagnostics, referenced) {
  const starts = [];
  body.forEach((line, i) => {
    const m = line.match(/^\s*(nonconsuming\s+)?choice\s+(\w+)\b/);
    if (m) starts.push({ nonconsuming: !!m[1], name: m[2], idx: i, indent: indentOf(line) });
  });

  const choices = [];
  for (let c = 0; c < starts.length; c++) {
    const s = starts[c];
    const end = c + 1 < starts.length ? starts[c + 1].idx : body.length;
    const cbody = body.slice(s.idx, end);

    // controller: `controller <expr>` (modern form) before the `do`.
    let controllers = [];
    for (const line of cbody) {
      const cm = line.match(/^\s*controller\s+(.+?)\s*$/);
      if (cm) controllers.push(...extractIdentifiers(cm[1]));
    }
    controllers = [...new Set(controllers)];
    if (controllers.length === 0) {
      diagnostics.push({
        severity: 'warning',
        code: 'no-controller',
        line: baseLine + s.idx + 1,
        message: `Choice \`${templateName}.${s.name}\` has no detectable \`controller\`.`,
      });
    }

    const operations = parseOperations(cbody, baseLine + s.idx, diagnostics, referenced);

    choices.push({
      name: s.name,
      consuming: !s.nonconsuming,
      controllers,
      operations,
      line: baseLine + s.idx + 1,
    });
  }

  return choices;
}

/** Scan a block for ledger operations and infer target templates. */
function parseOperations(cbody, baseLine, diagnostics, referenced) {
  const operations = [];
  cbody.forEach((line, i) => {
    for (const kind of OP_KINDS) {
      // word-boundary match for the op keyword
      const re = new RegExp(`\\b${kind}\\b`, 'g');
      let m;
      while ((m = re.exec(line))) {
        const rest = line.slice(m.index + kind.length);
        const target = inferTarget(kind, rest);
        if (target) referenced.add(target);
        else if (kind !== 'archive') {
          diagnostics.push({
            severity: 'info',
            code: 'ambiguous-target',
            line: baseLine + i + 1,
            message: `Could not infer target template for \`${kind}\` at this call site.`,
          });
        }
        operations.push({
          kind,
          target: target || null,
          inferred: !!target,
          line: baseLine + i + 1,
        });
      }
    }
  });
  return operations;
}

/**
 * Heuristically infer the target template of an operation from the text that
 * follows the keyword. Handles:
 *   create Foo with ...      -> Foo
 *   create (Foo ...)         -> Foo
 *   fetch @Foo cid           -> Foo
 *   exerciseByKey @Foo key C -> Foo
 *   createAndExercise (Foo ) -> Foo
 * Falls back to null when it can only see a value-level cid.
 */
function inferTarget(kind, rest) {
  // Type application: @Foo
  const at = rest.match(/^\s*@([A-Z][\w.]*)/);
  if (at) return lastSegment(at[1]);

  // Constructor application: `(Foo ...)` or `Foo with` / `Foo {`
  const ctor = rest.match(/^\s*\(?\s*([A-Z][\w.]*)\b/);
  if (ctor && (kind === 'create' || kind === 'createAndExercise')) {
    return lastSegment(ctor[1]);
  }
  // For fetch/lookup without @, sometimes `fetch (Foo ...)` appears.
  if (ctor && (kind === 'fetch' || kind === 'fetchByKey' || kind === 'lookupByKey')) {
    return lastSegment(ctor[1]);
  }
  return null;
}

function lastSegment(dotted) {
  const parts = dotted.split('.');
  return parts[parts.length - 1];
}
