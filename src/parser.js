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
 * @property {'create'|'createAndExercise'|'exercise'|'exerciseByKey'|'fetch'|'fetchByKey'|'lookupByKey'|'lookupAllByKey'|'archive'} kind
 * @property {string|null} target   inferred target template name, or null if ambiguous
 * @property {boolean} inferred     true if target was guessed heuristically
 * @property {string|null} [choice] choice name seen at an `exercise` call site,
 *                                  used by project mode to resolve the target
 * @property {number} line
 */

/**
 * @typedef {Object} Choice
 * @property {string} name
 * @property {boolean} consuming    false => nonconsuming
 * @property {string[]} controllers party-ish identifiers found after `controller`
 * @property {Operation[]} operations
 * @property {string[]} refs        identifiers called in the body, for the
 *                                  helper-function call graph (see callgraph.js)
 * @property {number} line
 */

/**
 * A top-level (non-template) binding. Canton-style codebases factor the actual
 * `create`/`exercise` calls out of choice bodies into shared helpers, so the
 * operations a choice really performs are often one call away.
 *
 * @typedef {Object} TopLevelFunction
 * @property {string} name
 * @property {Operation[]} operations
 * @property {string[]} refs
 * @property {number} line
 */

/**
 * @typedef {Object} Field
 * @property {string} name
 * @property {string} type
 * @property {boolean} isParty   true if the field's type mentions Party
 */

/**
 * @typedef {Object} ContractKey
 * @property {string} expr          the key expression, whitespace-normalized
 * @property {string|null} type     the key's type annotation, if present
 * @property {string[]} parties     party fields appearing in the key expression
 * @property {string[]} maintainers maintainer refs (`key._1` resolved to a key
 *                                  component where possible)
 * @property {number} line
 */

/**
 * @typedef {Object} Template
 * @property {string} name
 * @property {Field[]} fields
 * @property {string[]} partyFields   names of fields whose type is Party
 * @property {string[]} signatories
 * @property {string[]} observers
 * @property {Choice[]} choices
 * @property {string[]} implements    interface names this template implements
 * @property {InterfaceInstance[]} interfaceInstances
 * @property {ContractKey|null} key
 * @property {number} line
 */

/**
 * One `interface instance I for T where` block, including the parsed `view`
 * record. `viewBindings` maps a view field to the template expression that
 * supplies it, which is what lets a `(view this).admin` controller be resolved
 * to a real field of the implementing template.
 *
 * @typedef {Object} InterfaceInstance
 * @property {string} interface
 * @property {string} forTemplate
 * @property {string|null} viewType
 * @property {Record<string,string>} viewBindings
 * @property {string[]} nestedViewFields  view fields bound to a nested record
 * @property {number} line
 */

/**
 * @typedef {Object} Interface
 * @property {string} name
 * @property {string|null} viewtype
 * @property {Choice[]} choices
 * @property {string[]} methods      declared method names
 * @property {number} line
 */

/**
 * @typedef {Object} ParseResult
 * @property {string|null} module
 * @property {Template[]} templates
 * @property {Interface[]} interfaces
 * @property {TopLevelFunction[]} functions
 * @property {string[]} referencedTemplates   target templates referenced by operations
 * @property {string[]} referencedInterfaces  interfaces implemented but not declared here
 * @property {Diagnostic[]} diagnostics
 */

const OP_KINDS = [
  'createAndExercise',
  'exerciseByKey',
  'lookupAllByKey',
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

/**
 * Normalize a party reference to the name the enclosing template declares.
 *
 *   `this.admin`        -> `admin`       (self-projection: the same field)
 *   `(view this).admin` -> `view.admin`  (interface-view projection, kept
 *                                         distinguishable by the `view.` prefix)
 *   `contractData.x`    -> unchanged     (projection into a nested record)
 *
 * `this.field` is the dominant controller form in Canton codebases and denotes
 * exactly the same party as `field`. Treating the two as distinct was the
 * single largest source of bogus "controller is not a stakeholder" findings.
 */
function normalizePartyRef(ref) {
  const viewProj = ref.match(/^\(\s*view\s+this\s*\)\.(.+)$/);
  if (viewProj) return `view.${viewProj[1]}`;
  if (ref.startsWith('this.')) return ref.slice('this.'.length);
  return ref;
}

/** Keywords that can never name a party. */
const PARTY_KEYWORDS = new Set([
  'do', 'let', 'in', 'if', 'then', 'else', 'with', 'this',
  'return', 'pure', 'map', 'fmap', 'fromList', 'toList',
]);

/**
 * Split a party expression on the operators Daml uses to BUILD a party list,
 * at paren/bracket depth 0:
 *
 *   `,`   record/list separator
 *   `::`  cons          (`signatory admin :: optionalParty governance.approver`)
 *   `<>`  semigroup append (`observer a <> b`)
 *   `++`  list append
 *
 * Without this, `signatory admin :: optionalParty governance.approvalParty`
 * yielded only `admin`, silently UNDER-reporting the stakeholders of every
 * template in the tokens repo that uses the cons form.
 */
function splitPartyExpr(region) {
  const parts = [];
  let buf = '';
  let depth = 0;
  for (let i = 0; i < region.length; i++) {
    const ch = region[i];
    if (ch === '(' || ch === '[' || ch === '{') depth++;
    else if (ch === ')' || ch === ']' || ch === '}') depth = Math.max(0, depth - 1);

    if (depth === 0) {
      const two = region.slice(i, i + 2);
      if (two === '::' || two === '<>' || two === '++') {
        parts.push(buf);
        buf = '';
        i++; // consume the second operator character
        continue;
      }
      if (ch === '\n' || ch === ',') {
        parts.push(buf);
        buf = '';
        continue;
      }
    }
    buf += ch;
  }
  if (buf) parts.push(buf);
  return parts;
}

/**
 * Pick the party reference out of one segment of a party expression.
 *
 * A segment is usually a bare reference (`admin`, `spec.transferLeg.sender`),
 * but it is often a helper application whose LAST argument is the party:
 * `optionalParty governance.approvalParty`. So: tokenize the dotted
 * identifiers, drop keywords and capitalized constructors (`Some`, `None`,
 * type names), and if more than one remains take the last, which is the
 * argument rather than the function.
 *
 * @returns {{ref: string, applied: boolean}|null}
 */
function pickPartyRef(seg) {
  // `(view this).admin` must be matched first, or the leading `view` wins.
  const viewM = seg.match(/^\s*\(\s*view\s+this\s*\)((?:\.[A-Za-z_][A-Za-z0-9_']*)+)/);
  if (viewM) return { ref: normalizePartyRef(`(view this)${viewM[1]}`), applied: false };

  const tokens = seg.match(/[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*/g) || [];
  const candidates = tokens.filter((t) => {
    if (PARTY_KEYWORDS.has(t)) return false;
    // a capitalized head is a constructor or module qualifier, not a party
    return !/^[A-Z]/.test(t);
  });
  if (candidates.length === 0) return null;
  const applied = candidates.length > 1;
  return { ref: normalizePartyRef(candidates[candidates.length - 1]), applied };
}

/**
 * Extract party references from a signatory / observer / controller expression.
 *
 * Splits on top-level `,` / `::` / `<>` / `++` (paren/bracket-aware) so
 * `registry, owner` and `admin :: optionalParty governance.approver` both
 * yield every party, and keeps dotted record projections intact:
 * `spec.transferLeg.sender` is ONE party, not three. A leading `[ … ]` list
 * wrapper is unwrapped so `observer [alice, bob]` reads as two parties.
 * `this.x` and `(view this).x` are normalized (see normalizePartyRef).
 *
 * @param {string} expr
 * @param {{onApplied?: (ref: string, seg: string) => void}} [hooks]
 */
function partyRefs(expr, hooks = {}) {
  if (!expr) return [];
  // unwrap a single surrounding list literal: `[a, b]` -> `a, b`
  const e = expr.trim().replace(/^\[([\s\S]*)\]$/, '$1');
  const seen = new Set();
  const out = [];
  for (const part of splitPartyExpr(e)) {
    const seg = part.trim();
    if (!seg) continue;
    const picked = pickPartyRef(seg);
    if (!picked || seen.has(picked.ref)) continue;
    seen.add(picked.ref);
    out.push(picked.ref);
    if (picked.applied && hooks.onApplied) hooks.onApplied(picked.ref, seg);
  }
  return out;
}

/**
 * Parse the `view = SomeView with …` record of an `interface instance` block.
 *
 * This is the map that makes view-projected interface controllers resolvable.
 * An interface choice says `controller (view this).admin`; which of the
 * IMPLEMENTING template's fields supplies that admin is written down right
 * here, and was previously left unparsed:
 *
 *   interface instance Utxo for TransferableRecToken where
 *     view = UtxoView with
 *       holding = HoldingView with
 *         owner
 *         amount
 *       admin
 *
 * Two shapes have to be handled, both of which appear in real code:
 *   * record PUNNING - a bare `owner` means `owner = owner`
 *   * NESTING - `holding = HoldingView with …` continues over deeper lines
 *
 * Only the outermost bindings are returned as resolvable; a nested record is
 * kept as an unparsed expression string, because a party reached through one
 * is not a direct field of the template.
 *
 * @returns {{viewType: string|null, bindings: Record<string,string>, nested: string[]}}
 */
function parseViewBindings(body, from, to) {
  let viewType = null;
  /** @type {Record<string,string>} */
  const bindings = {};
  const nested = [];

  let headerIdx = -1;
  let headerIndent = 0;
  let inlineRest = '';
  for (let i = from; i < to && i < body.length; i++) {
    const m = body[i].match(/^(\s*)view\s*=\s*([A-Z][\w']*)?\s*(?:\bwith\b(.*))?$/);
    if (m) {
      headerIdx = i;
      headerIndent = m[1].replace(/\t/g, ' ').length;
      viewType = m[2] || null;
      inlineRest = m[3] || '';
      break;
    }
  }
  if (headerIdx === -1) return { viewType, bindings, nested };

  // Continuation lines: everything indented deeper than the `view =` line.
  const contLines = [];
  for (let i = headerIdx + 1; i < to && i < body.length; i++) {
    const line = body[i];
    if (!line.trim()) continue;
    if (indentOf(line) <= headerIndent) break;
    contLines.push(line);
  }

  /** Group continuation lines: a line at the shallowest indent starts a binding. */
  const groups = [];
  if (contLines.length) {
    const minIndent = Math.min(...contLines.map(indentOf));
    for (const line of contLines) {
      if (indentOf(line) === minIndent) groups.push([line]);
      else if (groups.length) groups[groups.length - 1].push(line);
    }
  }
  // Inline bindings on the header line, e.g. `view = V with a = x, b`
  for (const piece of splitTopLevel(inlineRest)) {
    if (piece.trim()) groups.unshift([piece]);
  }

  for (const group of groups) {
    const head = group[0].trim();
    const isNested = group.length > 1;
    const assigned = head.match(/^([a-z][\w']*)\s*=\s*([\s\S]*)$/);
    if (assigned) {
      const field = assigned[1];
      const expr = [assigned[2], ...group.slice(1).map((l) => l.trim())].join(' ').trim();
      if (isNested || /\bwith\b/.test(expr)) {
        nested.push(field);
      } else if (expr) {
        bindings[field] = expr;
      }
      continue;
    }
    // record punning: a bare field name means `field = field`
    const pun = head.match(/^([a-z][\w']*)$/);
    if (pun) bindings[pun[1]] = pun[1];
  }

  return { viewType, bindings, nested };
}

/** Top-level declaration keywords that terminate a template/interface body. */
const DECL_RE = /^(template|interface|data|type|newtype|class|instance|module|deriving)\b/;

/**
 * Extent of an indentation-delimited block starting at `startIdx`: runs until
 * the first later non-blank line indented no deeper than the header.
 */
function blockEnd(lines, startIdx) {
  const baseIndent = indentOf(lines[startIdx]);
  for (let i = startIdx + 1; i < lines.length; i++) {
    const line = lines[i];
    if (!line.trim()) continue;
    const ind = indentOf(line);
    if (ind <= baseIndent) return i;
    if (ind === 0 && DECL_RE.test(line.trim())) return i;
  }
  return lines.length;
}

/**
 * Identifiers that are never a user-defined helper worth following in the call
 * graph: Daml keywords, the ledger primitives we already model directly, and
 * the handful of Prelude names that appear in almost every body.
 */
const REF_STOPLIST = new Set([
  'do', 'let', 'in', 'if', 'then', 'else', 'with', 'this', 'where', 'case', 'of',
  'module', 'import', 'qualified', 'as', 'hiding', 'deriving', 'instance', 'data',
  'type', 'class', 'template', 'interface', 'signatory', 'observer', 'controller',
  'ensure', 'key', 'maintainer', 'choice', 'nonconsuming', 'viewtype', 'view',
  'return', 'pure', 'abort', 'error', 'assert', 'assertMsg', 'getTime', 'show',
  'map', 'fmap', 'foldl', 'foldr', 'filter', 'length', 'sum', 'product', 'concat',
  'concatMap', 'elem', 'notElem', 'null', 'head', 'tail', 'fst', 'snd', 'not',
  'when', 'unless', 'forA', 'forA_', 'mapA', 'mapA_', 'sequence', 'zip', 'unzip',
  'fromSome', 'fromOptional', 'optional', 'either', 'maybe', 'truncate', 'floor',
  'ceiling', 'round', 'abs', 'min', 'max', 'divide', 'self', 'arg',
  ...OP_KINDS,
]);

/**
 * Collect the identifiers a block calls, for the helper-function call graph.
 * Both the qualified (`Upsert.tenantMirror`) and bare (`tenantMirror`) spellings
 * are recorded so the resolver can match either an import-qualified call or a
 * same-module one.
 *
 * This over-collects: a local variable whose name happens to match a top-level
 * function will be picked up. The resolver only follows refs that actually
 * name a parsed function, and every operation it attributes this way is tagged
 * with the call path (`via`), so an over-attribution is visible rather than
 * silent.
 */
function extractRefs(blockLines) {
  const refs = new Set();
  const re = /\b((?:[A-Z][\w']*\.)+)?([a-z][\w']*)\b/g;
  for (const line of blockLines) {
    let m;
    while ((m = re.exec(line))) {
      const bare = m[2];
      if (REF_STOPLIST.has(bare)) continue;
      if (m[1]) refs.add(m[1] + bare);
      refs.add(bare);
    }
  }
  return [...refs];
}

/**
 * Parse the top-level (non-template) bindings of a module and the ledger
 * operations inside them.
 *
 * A definition starts at any column-0 line beginning with a lowercase
 * identifier that is not a keyword, and extends until the next such line or the
 * next top-level declaration. Consecutive blocks with the same leading name are
 * merged, so the common Daml layout
 *
 *   tenantMirror
 *     : Party -> TenantData -> Update (ContractId TenantMirror)
 *   tenantMirror admin contractData = do
 *     create TenantMirror.TenantMirror with …
 *
 * is read as ONE function with one `create`.
 *
 * @returns {TopLevelFunction[]}
 */
function parseFunctions(lines, uncovered, diagnostics, referenced) {
  const starts = [];
  for (let i = 0; i < lines.length; i++) {
    if (!uncovered[i]) continue;
    const line = lines[i];
    if (indentOf(line) !== 0 || !line.trim()) continue;
    if (DECL_RE.test(line.trim())) continue;
    const m = line.match(/^([a-z][\w']*)\b/);
    if (!m || REF_STOPLIST.has(m[1])) continue;
    starts.push({ name: m[1], idx: i });
  }

  // merge consecutive blocks that share a name (signature + equation)
  const merged = [];
  for (const s of starts) {
    const prev = merged[merged.length - 1];
    if (prev && prev.name === s.name) continue;
    merged.push(s);
  }

  const functions = [];
  for (let i = 0; i < merged.length; i++) {
    const s = merged[i];
    // A function body ends at the next top-level function OR the next covered
    // line (a template/interface declaration).
    let end = i + 1 < merged.length ? merged[i + 1].idx : lines.length;
    for (let k = s.idx + 1; k < end; k++) {
      if (!uncovered[k]) {
        end = k;
        break;
      }
    }
    const body = lines.slice(s.idx, end);
    const operations = parseOperations(body, s.idx, diagnostics, referenced, {
      quiet: true,
    });
    functions.push({
      name: s.name,
      operations,
      refs: extractRefs(body),
      line: s.idx + 1,
    });
  }
  return functions;
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

  // Flag legacy `controller ... can` blocks - only partially supported.
  lines.forEach((line, i) => {
    if (/\bcontroller\b.*\bcan\b/.test(line)) {
      diagnostics.push({
        severity: 'warning',
        code: 'old-controller-can',
        line: i + 1,
        message: 'Legacy `controller … can` choice syntax detected - choices inside it may be parsed incompletely. Prefer the `choice … controller …` form.',
      });
    }
  });

  // --- locate top-level template and interface declarations ---
  // `interface instance I for T where` is a TEMPLATE-BODY construct, not an
  // interface declaration, so it must not be picked up here.
  const templateStarts = [];
  const interfaceStarts = [];
  lines.forEach((line, i) => {
    const tm = line.match(/^\s*template\s+(\w+)\b/);
    if (tm) {
      templateStarts.push({ name: tm[1], line: i });
      return;
    }
    const im = line.match(/^\s*interface\s+(\w+)\b/);
    if (im && im[1] !== 'instance') interfaceStarts.push({ name: im[1], line: i });
  });

  // A body ends where the next top-level template/interface declaration starts.
  const allStarts = [
    ...templateStarts.map((s) => ({ ...s, kind: 'template' })),
    ...interfaceStarts.map((s) => ({ ...s, kind: 'interface' })),
  ].sort((a, b) => a.line - b.line);

  const templates = [];
  const interfaces = [];
  const referenced = new Set();
  const referencedInterfaces = new Set();

  // Lines NOT inside a template/interface body are candidates for top-level
  // helper functions. A body is bounded by whichever comes first: the next
  // declaration, or the end of its indentation block - the latter matters
  // because helpers are commonly defined *after* a template in the same file.
  const uncovered = new Array(lines.length).fill(true);

  for (let i = 0; i < allStarts.length; i++) {
    const start = allStarts[i];
    const nextStart = i + 1 < allStarts.length ? allStarts[i + 1].line : lines.length;
    const end = Math.min(nextStart, blockEnd(lines, start.line));
    for (let k = start.line; k < end; k++) uncovered[k] = false;
    const body = lines.slice(start.line, end);
    if (start.kind === 'template') {
      templates.push(
        parseTemplate(start.name, body, start.line, diagnostics, referenced, referencedInterfaces)
      );
    } else {
      interfaces.push(parseInterface(start.name, body, start.line, diagnostics, referenced));
    }
  }

  const functions = parseFunctions(lines, uncovered, diagnostics, referenced);

  if (templates.length === 0 && interfaces.length === 0) {
    diagnostics.push({
      severity: 'info',
      code: 'no-templates',
      message: 'No `template` or `interface` definitions found.',
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

  const definedIfaces = new Set(interfaces.map((x) => x.name));
  for (const r of referencedInterfaces) {
    if (!definedIfaces.has(r)) {
      diagnostics.push({
        severity: 'warning',
        code: 'external-interface',
        message:
          `Interface \`${r}\` is implemented here but declared elsewhere (another module, or an imported DAR). ` +
          `Its choices and their controllers are not in this graph - run project mode over the whole package set, ` +
          `or the interface's exercisable surface stays invisible.`,
      });
    }
  }

  return {
    module: moduleName,
    templates,
    interfaces,
    functions,
    referencedTemplates: [...referenced].sort(),
    referencedInterfaces: [...referencedInterfaces].sort(),
    diagnostics,
  };
}

/**
 * Parse an `interface Name where` block: viewtype, declared methods, choices.
 *
 * Interface choices are where the authorization for interface-exercised
 * actions on every implementing template actually lives, so they are modeled
 * as first-class choices rather than flagged and dropped.
 *
 * @returns {Interface}
 */
function parseInterface(name, body, baseLine, diagnostics, referenced) {
  let viewtype = null;
  const methods = [];

  // Method signatures live above the first choice header.
  const firstChoice = body.findIndex((l) => /^\s*(nonconsuming\s+)?choice\s+\w+/.test(l));
  const declRegion = firstChoice === -1 ? body : body.slice(0, firstChoice);

  for (const line of declRegion) {
    const vt = line.match(/^\s*viewtype\s+(\w+)/);
    if (vt) {
      viewtype = vt[1];
      continue;
    }
    if (/^\s*(viewtype|choice|signatory|observer|ensure|key|maintainer|nonconsuming)\b/.test(line)) continue;
    const md = line.match(/^\s{2,}([a-z][\w']*)\s*:\s*\S/);
    if (md) methods.push(md[1]);
  }

  if (!viewtype) {
    diagnostics.push({
      severity: 'warning',
      code: 'interface-no-viewtype',
      line: baseLine + 1,
      message: `Interface \`${name}\` has no detectable \`viewtype\` - view-projected parties (\`(view this).x\`) cannot be related to a record.`,
    });
  }

  const choices = parseChoices(name, body, baseLine, diagnostics, referenced);

  return { name, viewtype, choices, methods, line: baseLine + 1 };
}

/**
 * @param {string} name
 * @param {string[]} body       lines of the template block
 * @param {number} baseLine     0-based offset of body[0] in the whole file
 * @param {Diagnostic[]} diagnostics
 * @param {Set<string>} referenced
 * @param {Set<string>} referencedInterfaces
 * @returns {Template}
 */
function parseTemplate(name, body, baseLine, diagnostics, referenced, referencedInterfaces) {
  const fields = [];
  const partyFields = [];
  let signatories = [];
  let observers = [];

  // --- `interface instance I for T where` blocks ---
  // Nested inside the template body, carrying method implementations that may
  // contain ledger operations. Record which interfaces are implemented, and
  // remember the line ranges so the stakeholder scanner can skip an instance's
  // `view` body (which mentions parties that are not the template's own
  // signatories).
  const implementsList = [];
  const instanceRanges = [];
  const interfaceInstances = [];
  body.forEach((line, i) => {
    const m = line.match(/^\s*interface\s+instance\s+([\w.]+)\s+for\s+(\w+)\s+where/);
    const legacy = m ? null : line.match(/^\s*implements\s+([\w.]+)\b/); // Daml 2.x form
    if (!m && !legacy) return;

    const iface = lastSegment(m ? m[1] : legacy[1]);
    const end = blockEnd(body, i);
    implementsList.push(iface);
    referencedInterfaces.add(iface);
    instanceRanges.push([i, end]);

    const view = parseViewBindings(body, i + 1, end);
    interfaceInstances.push({
      interface: iface,
      forTemplate: m ? m[2] : name,
      viewType: view.viewType,
      viewBindings: view.bindings,
      nestedViewFields: view.nested,
      line: baseLine + i + 1,
    });
  });

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
  const inInstance = (i) => instanceRanges.some(([a, b]) => i > a && i < b);
  body.forEach((line, i) => {
    if (inInstance(i)) return;
    const sig = line.match(/^\s*signatory\s+(.+?)\s*$/);
    if (sig) signatories.push(...partyRefs(sig[1]));
    const obs = line.match(/^\s*observer\s+(.+?)\s*$/);
    if (obs) observers.push(...partyRefs(obs[1]));
  });
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

  const key = parseKey(name, body, baseLine, diagnostics, partyFields);

  // --- choices ---
  const choices = parseChoices(name, body, baseLine, diagnostics, referenced);

  return {
    name,
    fields,
    partyFields,
    signatories,
    observers,
    choices,
    implements: [...new Set(implementsList)],
    interfaceInstances,
    key,
    line: baseLine + 1,
  };
}

/**
 * Parse a template's contract key and maintainers.
 *
 * Handles the multi-line layout Canton codebases use:
 *
 *   key (admin, contractData.relationshipId,
 *        if backdated then Some d else None)
 *     : (Party, Text, Optional Time)
 *   maintainer key._1
 *
 * `maintainer key._N` is resolved POSITIONALLY against the key tuple, so
 * `key._1` over `key (admin, …)` reports `admin` as the maintaining party.
 * Without that resolution, maintainer-vs-signatory comparison is impossible.
 *
 * @returns {ContractKey|null}
 */
function parseKey(name, body, baseLine, diagnostics, partyFields) {
  // `key <expr>`, but not a local binding (`let key = …`) or a signature
  // (`key : …` at the start of a line belongs to a record field, not a key).
  const keyIdx = body.findIndex((l) => /^\s*key\s+(?![=:])\S/.test(l));
  if (keyIdx === -1) return null;

  // Accumulate continuation lines until parens balance.
  let exprRaw = body[keyIdx].replace(/^\s*key\s+/, '');
  let depth = balance(exprRaw);
  let i = keyIdx + 1;
  while (depth > 0 && i < body.length) {
    exprRaw += ' ' + body[i].trim();
    depth += balance(body[i]);
    i++;
  }
  // A `: <type>` annotation may sit on the same line or the next one.
  const inline = splitKeyType(exprRaw);
  exprRaw = inline.expr;
  let type = inline.type;
  if (!type && i < body.length) {
    const cont = body[i].match(/^\s*:\s*(.+?)\s*$/);
    if (cont) type = cont[1].trim();
  }

  const expr = exprRaw.replace(/\s+/g, ' ').trim();

  // Key components, for positional maintainer resolution.
  const tupleBody = expr.match(/^\(([\s\S]*)\)$/);
  const components = (tupleBody ? splitTopLevel(tupleBody[1]) : [expr]).map((s) => s.trim());
  const parties = components
    .flatMap((c) => partyRefs(c))
    .filter((p) => partyFields.includes(p));

  const maintainers = [];
  let sawMaintainer = false;
  for (const line of body) {
    const m = line.match(/^\s*maintainer\s+(.+?)\s*$/);
    if (!m) continue;
    sawMaintainer = true;
    for (const ref of partyRefs(m[1])) {
      const positional = ref.match(/^key\._(\d+)$/);
      if (positional) {
        const comp = components[Number(positional[1]) - 1];
        const resolved = comp ? partyRefs(comp)[0] : null;
        if (resolved) {
          maintainers.push(resolved);
        } else {
          maintainers.push(ref);
          diagnostics.push({
            severity: 'info',
            code: 'maintainer-unresolved',
            line: baseLine + keyIdx + 1,
            message: `Template \`${name}\`: maintainer \`${ref}\` could not be resolved to a key component.`,
          });
        }
      } else if (ref === 'key') {
        // `maintainer key` - every party component of the key maintains it
        maintainers.push(...parties);
      } else {
        maintainers.push(ref.replace(/^key\./, ''));
      }
    }
  }

  if (!sawMaintainer) {
    diagnostics.push({
      severity: 'warning',
      code: 'key-no-maintainer',
      line: baseLine + keyIdx + 1,
      message: `Template \`${name}\` declares a \`key\` but no \`maintainer\` was detected.`,
    });
  }

  return {
    expr,
    type,
    parties: [...new Set(parties)],
    maintainers: [...new Set(maintainers)],
    line: baseLine + keyIdx + 1,
  };
}

/** Net paren/bracket depth change across a string. */
function balance(s) {
  let d = 0;
  for (const ch of s) {
    if (ch === '(' || ch === '[') d++;
    else if (ch === ')' || ch === ']') d--;
  }
  return d;
}

/** Split a trailing `: <type>` off a key expression, paren-aware. */
function splitKeyType(raw) {
  let depth = 0;
  for (let i = 0; i < raw.length; i++) {
    const ch = raw[i];
    if (ch === '(' || ch === '[') depth++;
    else if (ch === ')' || ch === ']') depth--;
    else if (ch === ':' && depth === 0 && raw[i + 1] !== ':') {
      return { expr: raw.slice(0, i).trim(), type: raw.slice(i + 1).trim() };
    }
  }
  return { expr: raw.trim(), type: null };
}

/**
 * Find `choice`/`nonconsuming choice` blocks within a template or interface
 * body, then parse controller + ledger operations out of each.
 */
function parseChoices(ownerName, body, baseLine, diagnostics, referenced) {
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
      if (cm) controllers.push(...partyRefs(cm[1]));
    }
    controllers = [...new Set(controllers)];
    if (controllers.length === 0) {
      diagnostics.push({
        severity: 'warning',
        code: 'no-controller',
        line: baseLine + s.idx + 1,
        message: `Choice \`${ownerName}.${s.name}\` has no detectable \`controller\`.`,
      });
    }

    const operations = parseOperations(cbody, baseLine + s.idx, diagnostics, referenced, {
      selfTemplate: ownerName,
    });

    choices.push({
      name: s.name,
      consuming: !s.nonconsuming,
      controllers,
      operations,
      refs: extractRefs(cbody),
      line: baseLine + s.idx + 1,
    });
  }

  return choices;
}

/**
 * Scan a block for ledger operations and infer target templates.
 * `options.quiet` suppresses `ambiguous-target` diagnostics, used when
 * scanning top-level helpers (they are reported at the calling choice instead).
 */
function parseOperations(cbody, baseLine, diagnostics, referenced, options = {}) {
  const operations = [];
  const selfName = options.selfTemplate || null;
  cbody.forEach((line, i) => {
    for (const kind of OP_KINDS) {
      // word-boundary match for the op keyword
      const re = new RegExp(`\\b${kind}\\b`, 'g');
      let m;
      while ((m = re.exec(line))) {
        const rest = line.slice(m.index + kind.length);
        let target = inferTarget(kind, rest);
        let selfCreate = false;

        // `create this with …` inside template T definitionally creates T.
        // This is resolution, not a guess, and it is the single most common
        // create shape in mirror/upsert codebases.
        if (!target && selfName && (kind === 'create' || kind === 'createAndExercise')) {
          if (/^\s*this\b/.test(rest)) {
            target = selfName;
            selfCreate = true;
          }
        }

        // At an `exercise cid SomeChoice` site the target TEMPLATE is not
        // syntactically present, but the CHOICE NAME is - often module
        // qualified (`exercise cid ArBorrowingBase.ArchiveSubtypeToken`).
        // Project mode resolves the target by looking that name up across all
        // parsed modules, using the qualifier to disambiguate.
        const hint = target ? null : exerciseChoiceHint(kind, rest);
        if (target) referenced.add(target);
        else if (kind !== 'archive' && !options.quiet) {
          diagnostics.push({
            severity: 'info',
            code: 'ambiguous-target',
            line: baseLine + i + 1,
            message:
              `Could not infer target template for \`${kind}\` at this call site` +
              (hint ? ` (choice \`${hint.choice}\` - resolvable in project mode).` : '.'),
          });
        }
        operations.push({
          kind,
          target: target || null,
          inferred: !!target,
          ...(selfCreate ? { selfCreate: true } : {}),
          ...(hint ? { choice: hint.choice } : {}),
          ...(hint && hint.moduleHint ? { moduleHint: hint.moduleHint } : {}),
          line: baseLine + i + 1,
        });
      }
    }
  });
  return operations;
}

/**
 * At an `exercise cid Choice with …` site, recover the choice name so project
 * mode can resolve which template declares it.
 *
 * The choice is frequently module-qualified - `exercise cid
 * ArBorrowingBase.ArchiveSubtypeToken` - in which case the LAST segment is the
 * choice and the qualifier is a module hint that makes the lookup unambiguous
 * even when several templates declare a choice of the same name.
 *
 * @returns {{choice: string, moduleHint: string|null}|null}
 */
function exerciseChoiceHint(kind, rest) {
  if (kind !== 'exercise' && kind !== 'exerciseByKey' && kind !== 'createAndExercise') return null;
  // Skip the contract-id / key argument(s), then take the first capitalized
  // (possibly qualified) identifier: the choice name in every `exercise` shape.
  const m = rest.match(/^\s*(?:\(?[\w.'#]+\)?\s+)*?((?:[A-Z][\w']*\.)*)([A-Z][\w']*)\b/);
  if (!m) return null;
  const qualifier = m[1] ? m[1].replace(/\.$/, '') : null;
  return { choice: m[2], moduleHint: qualifier || null };
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
  if (
    ctor &&
    (kind === 'fetch' || kind === 'fetchByKey' || kind === 'lookupByKey' || kind === 'lookupAllByKey')
  ) {
    return lastSegment(ctor[1]);
  }
  return null;
}

function lastSegment(dotted) {
  const parts = dotted.split('.');
  return parts[parts.length - 1];
}

export { partyRefs, normalizePartyRef, splitTopLevel, OP_KINDS };
