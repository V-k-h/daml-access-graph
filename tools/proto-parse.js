// tools/proto-parse.js
//
// A small proto3 parser, covering exactly the constructs `daml_lf2.proto`
// uses: `syntax`, `package`, `option`, `message`, `enum`, `oneof`, `repeated`,
// and `reserved`. No imports, maps, services, groups or extensions appear in
// that file, so they are rejected loudly rather than half-handled.
//
// The point is not to be a general protobuf toolchain. It is to make the
// decoder's field numbers DERIVED from the official schema instead of copied
// by hand, because the failure mode of a wrong number is silence: reading
// `Expr.RecProj` with `Expr.RecUpd`'s number throws nothing and just yields no
// party names.

/**
 * @typedef {Object} ProtoField
 * @property {string} name        as written, e.g. `field_interned_str`
 * @property {string} jsName      camelCase, e.g. `fieldInternedStr`
 * @property {number} number
 * @property {string} type        as written, e.g. `int32`, `Expr`, `Type.Con`
 * @property {boolean} repeated
 * @property {string|null} oneof  the oneof this field belongs to, if any
 */

/**
 * @typedef {Object} ProtoMessage
 * @property {string} name        simple name
 * @property {string} qualifiedName  e.g. `Expr.RecProj`
 * @property {ProtoField[]} fields
 * @property {string[]} nested    qualified names of nested messages
 * @property {string[]} enums     qualified names of nested enums
 */

/**
 * @typedef {Object} ProtoSchema
 * @property {string|null} syntax
 * @property {string|null} package
 * @property {Map<string, ProtoMessage>} messages  keyed by qualified name
 * @property {Map<string, Record<string, number>>} enums  keyed by qualified name
 */

const SCALARS = new Set([
  'double', 'float', 'int32', 'int64', 'uint32', 'uint64', 'sint32', 'sint64',
  'fixed32', 'fixed64', 'sfixed32', 'sfixed64', 'bool', 'string', 'bytes',
]);

/** Strip `//` and `/* *​/` comments without changing line count. */
function stripComments(text) {
  let out = text.replace(/\/\*[\s\S]*?\*\//g, (m) => m.replace(/[^\n]/g, ' '));
  out = out
    .split('\n')
    .map((line) => {
      // A `//` inside a string literal would be mangled, but the schema has
      // none, and asserting that is cheaper than writing a string-aware lexer.
      const i = line.indexOf('//');
      return i === -1 ? line : line.slice(0, i);
    })
    .join('\n');
  return out;
}

const snakeToCamel = (s) => s.replace(/_([a-z0-9])/g, (_, c) => c.toUpperCase());

/**
 * Parse a .proto source into a schema descriptor.
 * @param {string} source
 * @returns {ProtoSchema}
 */
export function parseProto(source) {
  const text = stripComments(source);
  // `import` is accepted and ignored: the envelope proto imports the LF2 one,
  // but only to reference it by name, never as a field type here. The other
  // constructs would need real handling, so they are refused rather than
  // silently half-parsed.
  if (/\bservice\b|\bextend\b|\bmap\s*</.test(text)) {
    throw new Error(
      'proto-parse: this parser covers only the subset the Daml-LF schemas use ' +
        '(no service/extend/map). Refusing to parse rather than guess.'
    );
  }

  /** @type {ProtoSchema} */
  const schema = {
    syntax: null,
    package: null,
    messages: new Map(),
    enums: new Map(),
  };

  const syntaxMatch = text.match(/\bsyntax\s*=\s*"([^"]+)"/);
  if (syntaxMatch) schema.syntax = syntaxMatch[1];
  if (schema.syntax && schema.syntax !== 'proto3') {
    throw new Error(`proto-parse: expected proto3, got ${schema.syntax}`);
  }
  const packageMatch = text.match(/^\s*package\s+([\w.]+)\s*;/m);
  if (packageMatch) schema.package = packageMatch[1];

  let i = 0;

  // Stray semicolons are legal between top-level declarations.
  const skipWs = () => {
    while (i < text.length && /[\s;]/.test(text[i])) i++;
  };

  /** Read to the matching close brace, assuming `text[i]` is just past `{`. */
  const readBlock = () => {
    let depth = 1;
    const start = i;
    while (i < text.length && depth > 0) {
      const ch = text[i++];
      if (ch === '{') depth++;
      else if (ch === '}') depth--;
    }
    if (depth !== 0) throw new Error('proto-parse: unbalanced braces');
    return text.slice(start, i - 1);
  };

  /** Parse the body of a message, recursing into nested declarations. */
  const parseMessageBody = (body, qualifiedPrefix) => {
    /** @type {ProtoField[]} */
    const fields = [];
    const nested = [];
    const enums = [];

    let j = 0;
    const at = () => body.slice(j);

    while (j < body.length) {
      // eat whitespace and stray semicolons
      const ws = at().match(/^[\s;]+/);
      if (ws) {
        j += ws[0].length;
        continue;
      }
      if (j >= body.length) break;

      const rest = at();

      // nested message
      let m = rest.match(/^message\s+([A-Za-z_]\w*)\s*\{/);
      if (m) {
        j += m[0].length;
        const inner = extractBlock(body, j);
        const qn = `${qualifiedPrefix}${m[1]}`;
        parseMessageBody(inner.text, `${qn}.`) // register children first
          .register(qn, m[1]);
        nested.push(qn);
        j = inner.end;
        continue;
      }

      // nested enum
      m = rest.match(/^enum\s+([A-Za-z_]\w*)\s*\{/);
      if (m) {
        j += m[0].length;
        const inner = extractBlock(body, j);
        const qn = `${qualifiedPrefix}${m[1]}`;
        schema.enums.set(qn, parseEnumBody(inner.text));
        enums.push(qn);
        j = inner.end;
        continue;
      }

      // oneof
      m = rest.match(/^oneof\s+([A-Za-z_]\w*)\s*\{/);
      if (m) {
        j += m[0].length;
        const inner = extractBlock(body, j);
        for (const f of parseFieldLines(inner.text, m[1])) fields.push(f);
        j = inner.end;
        continue;
      }

      // reserved / option: skip to the terminating semicolon
      m = rest.match(/^(reserved|option)\b[^;]*;/);
      if (m) {
        j += m[0].length;
        continue;
      }

      // a plain field declaration
      m = rest.match(/^(repeated\s+|optional\s+)?([\w.]+)\s+([A-Za-z_]\w*)\s*=\s*(\d+)\s*[^;]*;/);
      if (m) {
        fields.push(makeField(m[2], m[3], Number(m[4]), !!(m[1] && m[1].trim() === 'repeated'), null));
        j += m[0].length;
        continue;
      }

      throw new Error(`proto-parse: could not parse near: ${rest.slice(0, 80).replace(/\s+/g, ' ')}`);
    }

    return {
      register(qualifiedName, simpleName) {
        schema.messages.set(qualifiedName, {
          name: simpleName,
          qualifiedName,
          fields,
          nested,
          enums,
        });
      },
    };
  };

  // -------------------------------------------------------------- top level
  while (i < text.length) {
    skipWs();
    if (i >= text.length) break;
    const rest = text.slice(i);

    let m = rest.match(/^(syntax|package|option|import)\b[^;]*;/);
    if (m) {
      i += m[0].length;
      continue;
    }

    m = rest.match(/^message\s+([A-Za-z_]\w*)\s*\{/);
    if (m) {
      i += m[0].length;
      const block = readBlock();
      parseMessageBody(block, `${m[1]}.`).register(m[1], m[1]);
      continue;
    }

    m = rest.match(/^enum\s+([A-Za-z_]\w*)\s*\{/);
    if (m) {
      i += m[0].length;
      const block = readBlock();
      schema.enums.set(m[1], parseEnumBody(block));
      continue;
    }

    throw new Error(
      `proto-parse: unexpected top-level construct near: ${rest.slice(0, 80).replace(/\s+/g, ' ')}`
    );
  }

  return schema;
}

function makeField(type, name, number, repeated, oneof) {
  if (!SCALARS.has(type) && !/^[A-Z]/.test(type.split('.')[0])) {
    // A lowercase non-scalar type would mean the parser mis-split a line.
    throw new Error(`proto-parse: unrecognized field type \`${type}\` for \`${name}\``);
  }
  return { name, jsName: snakeToCamel(name), number, type, repeated, oneof };
}

/** Fields inside a oneof block. */
function parseFieldLines(body, oneofName) {
  const fields = [];
  const re = /(repeated\s+|optional\s+)?([\w.]+)\s+([A-Za-z_]\w*)\s*=\s*(\d+)\s*[^;]*;/g;
  let m;
  while ((m = re.exec(body))) {
    fields.push(makeField(m[2], m[3], Number(m[4]), !!(m[1] && m[1].trim() === 'repeated'), oneofName));
  }
  return fields;
}

function parseEnumBody(body) {
  /** @type {Record<string, number>} */
  const out = {};
  const re = /([A-Za-z_]\w*)\s*=\s*(-?\d+)\s*[^;]*;/g;
  let m;
  while ((m = re.exec(body))) {
    if (m[1] === 'option' || m[1] === 'reserved') continue;
    out[m[1]] = Number(m[2]);
  }
  return out;
}

/** Find the matching close brace for a block that starts at `start`. */
function extractBlock(text, start) {
  let depth = 1;
  let i = start;
  while (i < text.length && depth > 0) {
    const ch = text[i++];
    if (ch === '{') depth++;
    else if (ch === '}') depth--;
  }
  if (depth !== 0) throw new Error('proto-parse: unbalanced braces in nested block');
  return { text: text.slice(start, i - 1), end: i };
}

/**
 * Field-number lookup for one message: `{ jsName: number }`.
 * @param {ProtoMessage} message
 */
export function fieldNumbers(message) {
  /** @type {Record<string, number>} */
  const out = {};
  for (const f of message.fields) out[f.jsName] = f.number;
  return out;
}
