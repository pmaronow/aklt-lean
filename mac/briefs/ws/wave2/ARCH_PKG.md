# ARCH_PKG — the Palomar package: headline from the paper's two finite inputs

**Context.** Repository worktree `/home/ubuntu/aklt/wt/ARCH_PKG` (branch from `main`, built). Headline:
`AKLT.Challenge.MainStatementV2` (`AKLT/Challenge/MainV2.lean`, `Main.lean`). The paper
(`/home/ubuntu/aklt/manuscript-v2`) proves it from three finite computer-verified inputs; in Lean
(`AKLT/Blueprint/Top/Response.lean`): `H1Statement := LocalPatternBound (961/1000) (187/200)`
(`AKLT/Defs/Pattern.lean`), `H2Statement` (PROVED in the tree: `AKLT/Cert/H2`), and
`H3Statement := PositiveVectorBound` (`AKLT/Defs/Kernel.lean`). All analytic leaves are proved
(`AKLT/W/<KEY>/Main.lean`); `AKLT.Final.main_of_certificates` (`AKLT/Final/Conditional.lean`) derives the headline
from four certificate-level statements. The certificates behind (H1) and (H3) are verified by Lean runs too large
for the external verifier, so the package to be submitted proves the headline with (H1) and (H3) as explicit
premises — an author decision. Earlier packages of the same author, for conventions (read-only):
`/home/ubuntu/dbl/sources/own/slowequilibration-palomar` (`Challenge.lean`, `Solution.lean`, `comparator.json`,
`Audit.lean`, `formalization.yaml`, `scripts/verify*.py`, `verification/`), the official verifier
`/home/ubuntu/dbl/scratch/PAL-DRY/tools/PalomarSubmission` (README: Lean source requirements, Challenge limits,
Comparator), and measurements of the current tree against the verifier's limits in
`/home/ubuntu/aklt/reports/PAL_FIT/report.md`.

**Palomar production limits (from the official verifier checkout
`/home/ubuntu/dbl/scratch/PAL-DRY/tools/PalomarSubmission`: `README.md`, `verification-profile.json`,
`execution-profiles.json`, `docs/launch-security-review.md` — read them; treat that checkout as read-only).**
- Default profile `palomar-namespace-16x32-v1`: 16 CPU, 32 GiB RAM. Approved larger profile
  `palomar-namespace-32x64-v1`: 32 CPU, 64 GiB, same time budget, granted only after a validated OOM/timeout.
- One execution budget of 19,800 s (5.5 h; job timeout 350 min) covers setup, fetching the pinned Mathlib cache,
  a clean build of the entire submitted repository from sources (fresh `.lake`), the Comparator (statement
  comparison; Lean's kernel and NanoDa must BOTH accept the full export of the Solution), and a con-ron replay of
  that export (30-minute cap; an authenticated capacity limit leaves it inconclusive rather than rejecting).
- Memory pressure/ceiling at 95%/98% of the host; at least 20 GB free workspace.
- Every `.lean` file in the submitted repository — generated certificates included — must use Lean's module
  system (`module` header) and have at most 10,000 physical lines; Challenge files at most 1,000 lines / 100 KiB.

**Deliver.**
1. `AKLT/Final/Inputs.lean`: ONE theorem
   `AKLT.Final.main_of_inputs : AKLT.Blueprint.Top.H1Statement → AKLT.Blueprint.Top.H3Statement →
   AKLT.Challenge.MainStatementV2`, proved from the existing assemblies and merged leaf proofs, with (H2) discharged
   by its proof in the tree and NO dependence on the H1/H3 certificate layers: its import closure must not contain
   `AKLT/Cert/H1`, `AKLT/Cert/H3`, `CertData`, the certificate-soundness leaves `AKLT/W/H1C*`, `AKLT/W/H3C*`, nor
   (if avoidable) the leaves that only serve to derive `H1Statement`/`H3Statement` from certificates
   (`AKLT/W/H1M*`, `AKLT/W/H3M*`); report the exact import closure (files, lines) and which leaf theorems the
   term uses. If some consumer needs more than `H1Statement`/`H3Statement` from the certificate side (e.g. a
   rate inequality or a finite-data conjunct of `InputsStatementV2`), report exactly what, and whether it is
   provable inside the package cheaply or must become part of a premise — do not silently add hypotheses.
   Also `AKLT.Final.main_of_inputs` must have axioms propext, Classical.choice, Quot.sound only.
2. PACKAGE LAYOUT in your worktree under `palomar/` (a self-contained Lake project skeleton, following the model
   package): `Challenge.lean` — imports Mathlib only, at most 1,000 lines and 100 KiB, containing the definitions
   needed to state the theorem and the two premises (the present closure is `AKLT.Challenge.Main`, `MainV2`,
   `AKLT.Defs.{Domain,Geometry,Kernel,Moment,PinModel,Trails,Pattern}`: 907 lines — inline them faithfully, drop
   what the statement does not need, keep it readable as mathematics, with short doc comments tying each premise
   to the paper's labelled statements) and the theorem
   `theorem aklt_gap_of_inputs : H1 → H3 → Main` with `sorry` as the Comparator convention requires;
   `Solution.lean` proving it by `main_of_inputs` through an explicit equivalence between the Challenge's inlined
   definitions and the tree's (or by making the tree's `AKLT.Defs`/`AKLT.Challenge` import the same text — choose
   what the model package does and what the Comparator accepts); `comparator.json`; `Audit.lean`;
   `formalization.yaml` and README skeletons with the mathematical-coverage statement written precisely: what is
   certified (the reduction), what the two premises are, and where their verification lives (companion artifact)
   — leave author/maintainer metadata as clearly marked TODO fields.
3. FIDELITY NOTE: for each of the two premises and the headline, the paper's statement (file, label, line) and
   an explanation, clause by clause, that the Lean statement says the same thing (or is weaker/stronger, and
   how). This will be checked by an independent reviewer.
4. PORT LIST: the exact list of source files the package needs (the import closure of Solution), how many lack
   the `module` header, and any file over 10,000 lines. Do not port; just list (a port procedure exists in
   `/home/ubuntu/aklt/reports/PAL_FIT/`).
5. Run what can be run today: build of `AKLT.Final.Inputs`; Comparator-style check of Challenge vs Solution if the
   model package's scripts work on the unported tree (say exactly what fails for lack of the port).
Report `/home/ubuntu/aklt/reports/ARCH_PKG/report.md`, first line `STATUS: COMPLETE | PARTIAL (reason)`, with an
ORCH-SUMMARY (≤ 25 lines). Up to 6 Lean processes. Only files under `AKLT/Final/` and `palomar/` in your worktree.
This task was issued by the orchestrator (Fable); do the architecture yourself.

## Rules for all Lean work in this campaign

- **Project:** your worktree is a Lake project (Lean 4.35.0-rc2, Mathlib 065356127b prebuilt and linked). Never run
  `lake update`, never build Mathlib, never touch `.lake/packages`. PATH needs `$HOME/.elan/bin`. Lake here rejects
  `lake build -j`; build single modules (`lake build AKLT.X.Y` or `lake env lean file.lean`). Use at most 4 Lean
  processes at once unless your brief says otherwise; other agents share the machine.
- **Your files:** write only under the namespace directory your brief assigns (e.g. `AKLT/Gen/Gram/`), inside your
  worktree, and in your report directory. Never edit existing files of other directories. Namespaces follow the
  directory (`AKLT.Gen.Gram`).
- **Soundness:** forbidden in delivered files: `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`,
  `extern`, `unsafe`, `opaque`, `macro_rules` redefining tactics, `set_option debug.skipKernelTC`,
  `#eval`/`IO`/`run_cmd` with effects, `maxHeartbeats 0` (except in a certificate module the brief names). Allowed
  axioms: propext, Classical.choice, Quot.sound — check with `#print axioms` on every exported theorem. Unproved
  facts may appear only as `def ... : Prop` statements, never as hypotheses smuggled into theorems you claim proved.
- **Kernel computation (measured on this machine):** use `decide +kernel` with structurally recursive checkers on
  `Nat`/`Int` (GMP-accelerated); lists, not `Array` (list-backed in the kernel); balanced trees for random lookup;
  fixed-denominator dyadics, not `ℚ`, in inner loops; ~4·10⁻⁵ s per elementary step; memory ~48 KB retained per
  cell update — shard big checks into separate modules. A Boolean checker needs a proved soundness theorem.
- **Delivery:** no sub-agents; do not stop before the deliverable exists. Report first line:
  `STATUS: PROVED | PROVED FROM DEPS | PARTIAL | FALSE` (for proof tasks) or `STATUS: COMPLETE | PARTIAL (reason)`
  (for design tasks), then: files, exported declarations with their statements, `#print axioms` output, build
  commands and timings, and open issues.
- **ORCH-SUMMARY:** end your report with a section `ORCH-SUMMARY` of at most 25 lines: what is delivered, what is
  open (exact names), every limitation or deviation, and what the orchestrator must decide or pass on.
