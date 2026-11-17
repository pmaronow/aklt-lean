# Verification record

This record separates the complete Lean source build from independent checks of
the two-input reduction and physical statement. Fields named `TBD-…` are filled
from the final combined build and published release receipts. They are not pass
claims. The project follows Palomar's file and comparison conventions and is not
a Palomar submission; Palomar's execution allowance does not apply.

## Toolchain and pins

| Component | Pin |
|---|---|
| Lean | `leanprover/lean4:v4.35.0-rc2` |
| Mathlib | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Other Lean dependencies | Exact revisions in `lake-manifest.json` |
| Official verifier used for the recorded comparisons | `14aa8d6b3c2f14a8540605e37144560b9a00e7e7` |
| Manuscript | `241c2d870e89e8ff857991fbadf28ba6df833783`; exact file hashes in `verification/manuscript.json` |
| Final combined source commit | `TBD-FINAL-SOURCE-COMMIT` |
| Final certificate receipt bundle / release tag | `TBD-FINAL-RECEIPTS`, `TBD-RELEASE-TAG` |

The earlier protected con-ron replay used the official selected checker override
for Lean v4.36.0-rc1; its exact binary pin is in the recorded regression receipt.
The source compiler remained v4.35.0-rc2.

## Lean source digest

The digest is SHA-256 of the UTF-8 concatenation of lines `path sha256\n`, sorted
lexicographically by repository-relative path, for every tracked `.lean` file
plus `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`. Each inner hash
is SHA-256 of that file's exact working-tree bytes. Paths use `/`; one ASCII
space separates the path and lowercase digest, and every line ends in LF.
Documentation and later documentation-only commits do not change this value.
Generated sources are intentionally untracked and are instead pinned individually
by the certificate manifests and source archives; include those receipts with
this record. The tracked source digest alone does not identify an untracked
certificate installation.

```sh
python3 scripts/source_digest.py --manifest ../aklt-verification/lean-sources.sha256
python3 scripts/source_digest.py --check ../aklt-verification/lean-source-digest.txt
```

Final combined digest: **TBD-FINAL-LEAN-SOURCE-DIGEST**.
The tracked source baseline at `42b16c3` has digest
`c875dff024d396b0b78f1fa955ea5d38e8f577e1d8bd69e970fd02bea906bee9`.
It is recorded in `verification/source-digest.txt`; documentation and tooling
updates preserve it.

## Hand-written build

Run `lake build Handwritten Challenge Regression.Solution Regression.Audit
AuditHandwritten RegenSamples.H1Consumer RegenSamples.H3Consumer` after fetching
the pinned Mathlib cache. The final fresh build record is **TBD-HANDWRITTEN-BUILD**:
wall seconds **TBD-HANDWRITTEN-WALL**, CPU-hours **TBD-HANDWRITTEN-CPU-HOURS**,
peak process/aggregate RSS **TBD-HANDWRITTEN-MEMORY**.

Already measured at verified source commit `dad70bac7b345ea4ca89426c32848b4567acb6a8`:
a fresh affected closure of 1,025 modules built in 1,102.623 s wall and
10,674.760 s CPU (2.965 CPU-hours), with 57.776 GiB sampled aggregate RSS.
`LEAN_NUM_THREADS=12`, a 12-compiler process guard, and CPUs 0–15 were used.
Native runtime/GC helper threads are separate telemetry. Both regeneration
consumers passed. The strict hand-written Audit checked 21,896 constant entries
and all 18 explicit export prints. Full records are in
`verification/fidelity-round2/`; these numbers are not a fresh combined release
measurement.

## Certificate builds

Numeric input and source-archive pins are in [the artifact guide](docs/ARTIFACTS.md).
Both families are generated as ordinary module-system Lean sources and are checked
by the Lean kernel when compiled. A successful Python computation or receipt hash
is never substituted for a theorem proof. A fresh combined build starts without
project objects and uses no objects from the separate regeneration clones.

| Family | Generated modules | Final CPU-hours | Final wall seconds | Peak process RSS | Peak aggregate RSS | Receipt |
|---|---:|---|---|---|---|---|
| H1 | 7,964 | TBD-H1-CPU-HOURS | TBD-H1-WALL | TBD-H1-PROCESS-MEMORY | TBD-H1-AGGREGATE-MEMORY | TBD-H1-RECEIPT |
| H3 | 5,032 | TBD-H3-CPU-HOURS | TBD-H3-WALL | TBD-H3-PROCESS-MEMORY | TBD-H3-AGGREGATE-MEMORY | TBD-H3-RECEIPT |

The separate H3 regeneration completed 5,032 modules and 2,735 generated theorem
axiom audits using 23.081631 CPU-hours for unique successful compilations
(23.187933 CPU-hours across all attempts). Peak process RSS including closing
was 13.636 GB; peak sampled aggregate RSS was 94.716 GB, at up to 16 Lean processes.
These reference measurements, in `docs/regeneration/H3.md`, are not the final
combined-build measurements. The H1 reference build checked 7,964 owners and
414,638 theorem audits using 155.174 numeric CPU-hours, with 5.987 GiB peak module
RSS and a conservative 160.028 GB sampled aggregate bound. Its per-kind table
and 26–28% coverage-frontier CPU increase are recorded in `docs/regeneration/H1.md`.
Record the actual combined-tree values above rather than substituting reference
measurements.

The cold driver orders hand-written targets, H3 generate/build/close/verify,
H1 input receipts/re-export/build/verify/close, and the common closing modules.
It runs directly from numeric inputs without an external adapter. Both families
receive explicit job and aggregate-memory limits. The source-only dry-run and
compatibility checks are recorded under `verification/layout/`.

## Closing theorems and axioms

The final closing modules prove:

```lean
CertData.Close.h1 : AKLT.Blueprint.Top.H1Statement
CertData.Close.h2 : AKLT.Blueprint.Top.H2Statement
CertData.Close.h3 : AKLT.Blueprint.Top.H3Statement
CertData.Close.main : AKLT.Challenge.MainStatementV2
AKLTPalomar.aklt_gap : AKLTPalomar.Main
```

`Audit.lean` checks the closed types and prints their axiom sets, together with
`AKLTPalomar.main_iff`. `scripts/check_axioms.py --mode full` requires all six
prints and rejects any axiom outside `propext`, `Classical.choice`, and `Quot.sound`.
`AuditHandwritten.lean` also scans every available first-party constant; the
certificate runners scan every generated theorem. Strict elaboration turns
warnings into errors and disables implicit variables.

Final full Audit log: **TBD-FULL-AUDIT-LOG**. Paste its exact
`#print axioms AKLTPalomar.aklt_gap` output here: **TBD-FULL-THEOREM-AXIOMS**.
The already accepted reduction transcript contains:

```text
'AKLT.Final.main_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLTPalomar.aklt_gap_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
FIRST_PARTY_AXIOM_AUDIT_PASS: 21896 constants
```

## Challenge requirements and statement comparison

`Challenge.lean` has 161 physical lines and 7,359 bytes, imports only Mathlib,
uses the module system, and has one conventional placeholder. Every other Lean
file must have a module header, no proof placeholder or forbidden construct, and
at most 10,000 physical lines. The official parser accepted all 1,117 hand-written
Lean sources in the recorded tree. Final all-source checks, including the
generated families: **TBD-ALL-SOURCE-CHECKS**, **TBD-ALL-HEADER-CHECKS**.
Author metadata and root LICENSE were the only recorded source/configuration
findings; author identities, ORCIDs, license, and public provenance remain author TODOs.

`make_challenge.py --check` verifies the Challenge and its source-hash record
byte-for-byte. Its selected 24 declaration comments are copied verbatim from the
library. `main_iff` is Iff.rfl on a library definition and does not itself compare
separate environments. The physical comparison compiles the independent Challenge
and a library-side reflexive adapter separately, then compares all reachable
statement definitions without definition exemptions.

Lean and NanoDa accepted this statement comparison at `dad70ba`: the Comparator
stage used 69.527 s wall, 83.190 s CPU, and 0.579 GiB sampled RSS. Its negative
control changes independent `spinZ` from `2-k` to `3-k`; the Comparator rejects
`AKLT.Challenge.bondCasimir` (18.467 s). An added-byte generation control is also
rejected. See `verification/fidelity-round2/statement-comparison.log` and
`generation-negative.json`. The current sources are unchanged in this layout
commit. Reproduce both cases with `scripts/compare_statement.py`.
Final combined-tree physical comparison / negative control: **TBD-FINAL-STATEMENT-COMPARISON**.

## Independent kernels: exact scope

Lean's fresh replay, NanoDa, and con-ron accepted the **full two-input reduction**
`Regression.Solution`, including its exported proof closure, at `dad70ba`.
This theorem assumes H1 and H3 and uses the proved H2. It is not the unconditional
certificate proof. The export contained 63,516 declarations and 671,986,654 bytes,
SHA-256 `ea82aaec07c458ff23d38403de8cc22fc93b488cebc3a99ebe4ed6701d7fab6d`.
The protected Comparator (Lean plus NanoDa) used 1,117.574 s wall,
1,218.760 s CPU, and 23.226 GiB sampled RSS; verified con-ron used 713.212 s wall,
878.220 s CPU, and 47.184 GiB sampled RSS. The acceptance markers and exact commands
are in `verification/fidelity-round2/regression-receipt.json`.
These sampled RSS sums can double-count shared pages and are not cgroup peaks.

**A full replay of the unconditional proof in an independent kernel was not run.**
The generated certificate modules are checked by the Lean kernel at build time.
REL_FEAS's measured-sample estimate gives about 90–140 hours of serial numerical
work for the Comparator's Lean replay; NanoDa about 100–220 numerical CPU-hours
and con-ron about 220–400 numerical CPU-hours, plus data parsing. Five H3 spatial
catalogs alone encode roughly 35.8 GB of decimal digits before endpoints, H1,
expressions, or proofs. Three original row closures produced about 7 GiB and both
independent readers exceeded 5,400 s without acceptance. These are planning
estimates from samples, not a full-export size or runtime measurement. The
size and repeated numerical work explain this verification boundary; they are
not an unproved theorem premise. See [the feasibility excerpt](docs/INDEPENDENT-KERNELS.md).

## Fidelity reviews and resolutions

Three independent statement reviews are preserved under
[verification/reviews/](verification/reviews/README.md):

| Review | Verdict and scope |
|---|---|
| FID_FABLE | FAITHFUL WITH REMARKS; current-paper Challenge, input layer, and reduction; no Fatal or Major finding |
| FID_ASTRA | FAITHFUL WITH REMARKS; current-paper Challenge and selected inputs; no Fatal or Major finding |
| FID_CH2 | PASS, zero blocking findings; earlier all-parity target MainStatementV2 against the supplied target and earlier paper, not a whole-tree audit |

The two current-paper reviews' minor findings were addressed by correcting
references, deleting the unused even-period statement and arithmetic, documenting
Iff.rfl precisely, making exact generation mandatory, removing root Challenge
cache-reset commands, explaining the spin convention, proving the sanity
propositions, and documenting the input-layer conventions. Those conventions
remain explicit in `docs/STATEMENT-NOTES.md`: first-hit trails, center-zero
restrictions on legacy/V2 stationary operators, and redundant raw exchange signs.
The source/interface identity checks and proof changes are recorded in
`verification/fidelity-fix/`, `verification/fidelity-round2/`, and
`docs/port/CHANGES.md`. No review is represented as a kernel audit of omitted
certificate modules. Author metadata, public artifact URLs, and license are
completed by the author; final build fields above are completed from receipts.
