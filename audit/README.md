# Audit records and schemas

This repository uses the common AML source-map, statement-comparison,
proof-coverage, fidelity, proof-relationship and report contracts.
[`aml_audit_source.json`](aml_audit_source.json) binds the complete public Lean
inventory to its code revision. The schema/policy files are exact copies of the
central owners, pinned by [`schemas/SHA256SUMS`](schemas/SHA256SUMS).

The descriptor covers 28 paper modules, the public import root and
`ProofChecks.lean`. Native manuscript, source quotes, reviews and audit records
remain private. Their repository location and revision bindings are withheld
from this public metadata. The descriptor therefore preserves the common
unavailable-transport state; schema checks issue no mathematical acceptance.
The final validation report retains its stated theorem scope.

## Public checks

```sh
python3 -m pip install -r audit/requirements.txt
python3 audit/verify_audit_source.py
```

These checks validate the descriptor, complete code inventory and exact schema
copies without private credentials. CI runs them alongside the existing Lean
build and proof/axiom checks. The complete schema bundle includes its local
references and adds no paper-specific classification vocabulary.

## Authorized native replay

When an authorized native descriptor and snapshot are available, the same
verifier delegates to the central AML owners:

```sh
python3 audit/verify_audit_source.py \
  --aml-root /path/to/authorized/AML-checkout \
  --native-snapshot /path/to/authorized/native-snapshot
```

The central `audit_repository_sources` and `audit_snapshot_transport` owners
validate exact native code bindings and replay the snapshot after relocation.
A full replay requires the matching authorized descriptor. Preserve native
pending/accepted states, source editions and statement/proof scopes. A report
or digest alone supplies no proof credit. Count each full versioned source item
once across repositories.

After a code, source-edition, target or material dependency change, update the
affected native owners, retain all required evidence in authorized Git storage,
regenerate the snapshot and refresh the descriptor. Preserve issued reviews
and their exact identities. A schema-only update reuses unchanged mathematics.
