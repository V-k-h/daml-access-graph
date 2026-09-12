# Vendored Daml-LF 2 schema

`daml_lf2.proto` is copied verbatim from:

    repo:   github.com/digital-asset/daml
    tag:    v3.4.11
    path:   sdk/daml-lf/archive/src/protobuf/com/digitalasset/daml/lf/archive/daml_lf2.proto
    license: Apache-2.0 (header retained in the file)

Fetched with:

    gh api "repos/digital-asset/daml/contents/sdk/daml-lf/archive/src/protobuf/com/digitalasset/daml/lf/archive/daml_lf2.proto?ref=v3.4.11" \
      --jq '.content' | base64 -d > backend/proto/daml_lf2.proto

## Why it is vendored rather than hand-transcribed

`backend/lf2-schema.generated.js` is produced FROM this file by
`npm run codegen`. Nothing in the decoder carries a hand-copied field number.

That matters because the failure mode of a wrong field number is silence, not
an error. `Expr.RecProj` and `Expr.RecUpd` are near-identical messages that put
`field_interned_str` in slots 4 and 2 respectively, and `FieldWithExpr` puts it
in 3. Reading RecProj with RecUpd's number does not throw; every stakeholder
expression simply comes back empty, and the tool reports a package as having no
signatories. That bug was real, and generation removes the whole class of it.

## Updating

Replace the file, note the new tag above, and run:

    npm run codegen
    npm test

`tests/codegen.test.js` fails if the committed generated schema does not match
what this proto produces, so drift cannot land silently.
