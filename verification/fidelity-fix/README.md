# Fidelity fix verification

The verified source commit is recorded in summary.json. Later package commits
add these records without changing Lean sources. All 65 transitive certificate
dependencies remain byte-for-byte unchanged from d1320320.

summary.json records stage timings, outcomes, scope, and the new sanity proofs.
semantic-checks.json checks the unchanged statement/proof code, source hashes,
line caps, and retained citation labels. protected-closure.json contains the
complete frozen import closure with hashes and shortest import paths.
sanity-exports.log lists the exact signatures and axiom dependencies of all
17 new public theorems; axioms-and-interface.log is the strict whole-available-tree
Audit. source-checks.json and headers.json cover all 1,117 Lean files.

The physical statement comparison compiles independent and library-side
reflexive main_iff adapters in separate environments. The independent adapter is
the generated root Challenge with its one placeholder theorem replaced by
main_iff : Main ↔ AKLT.Challenge.MainStatementV2 := Iff.rfl. The library adapter
imports MainV2 and defines the same alias and reflexive theorem. The Comparator
recursively compares the complete reachable physical statement with no definition
exemptions and checks the adapter export with Lean and NanoDa. Changing only
the independent spinZ diagonal constant from 2 to 3 is rejected at bondCasimir.
This is a statement-identity test, not a proof of the unconditional main theorem.

regression-receipt.json records the official protected two-input pipeline:
Lean and NanoDa accept its full Solution export, and con-ron accepts the same
export. It is bound to the final source hashes and is explicitly conditional.
The full unconditional Solution and Audit still require generated certificates.

The exact generation check runs as part of source verification and the complete
runner. Use python3 scripts/make_challenge.py --check. Existing metadata and
license TODOs remain author-owned findings. Measurement RSS is a sampled process
tree sum and can double-count shared pages; it is not a production cgroup peak.
