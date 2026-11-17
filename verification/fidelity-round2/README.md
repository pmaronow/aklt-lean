# Second fidelity-round verification

summary.json binds these records to the verified source commit. Later commits add
records only. The full conditional Solution export is identical to the previously
accepted 61f1093 export, and is accepted again by Lean, NanoDa, and verified con-ron.

interface-before.json.gz and interface-after.json.gz contain full elaborated
ConstantInfo types, exact Name structure, universe-parameter lists, full pretty
output, raw Expr representations, and body availability. All 2,408 retained
captured declarations match in every field. The one missing sentinel is the
explicitly deleted, unused MainStatement. It was present only in conservative
complete/exposed inventories, not either actual generated reference list.
interface-hashes.tsv indexes these exact records; interface-identity.json gives
the comparison and family counts. The diagnostic interface-probe.lean.in includes
the old name intentionally to confirm its removal; it is not a library caller.

source-diff.json records exact line counts and permitted code deletions. All
remaining definitions, statements, and proofs preserve their code. All 24 selected
declaration doc comments are copied verbatim. The generation check detects even
a one-byte change. old-closure-changes.tsv gives the exact two files changed since
d132032 within the old 65-module closure, with old/new hashes for the source merge.

Strict Audit covers 21,896 available constant entries and all 18 required exports.
Headers cover all 1,117 Lean files. The physical statement comparison uses separate
reflexive main_iff adapters in independent and library environments, with no
definition exemptions. Lean and NanoDa accept; an altered spinZ is rejected at
bondCasimir. This establishes statement identity, not the unconditional proof.
The full unconditional Solution/Audit checks await merged generated sources.

The build used LEAN_NUM_THREADS=12, a 12-compiler process guard, and CPUs 0–15.
Native GC/runtime helper threads are separate telemetry; the worker setting is
not a count of all operating-system helper threads. Stage RSS is a sampled
process-tree sum, not an authenticated cgroup peak. Source checks retain only the
preexisting author metadata/provenance and root LICENSE findings.

The regeneration clones, their build objects, and REGEN reports were not modified.
The final release must build from the merged sources with fresh project objects.
