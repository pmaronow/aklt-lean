# ARCH_H1T — Lean architecture for the new H1 input ("H1-tree") (author-directed, top priority)

**Context.** Repository worktree `/home/ubuntu/aklt/wt/ARCH_H1T` (branch from `main`, built). The formalization's
headline is `AKLT.Challenge.MainStatementV2`; `AKLT.Final.main_of_certificates` proves it from four finite
certificate statements, two of them for the input (H1): `AKLT.Blueprint.Top.H1FiniteDataStatementV2` and
`AKLT.Blueprint.Top.CertificateStatement` (a catalogue of 7,962 local patterns with Gram certificates; hand-written
checker and soundness layer in `AKLT/Cert/H1/**`, analytic part in `AKLT/Blueprint/H1/**` with proved leaves
`AKLT/W/H1M*/`, certificate-soundness leaves `AKLT/W/H1C*/`). That certificate costs ~115 CPU-hours of kernel time
and cannot pass the external verifier (limits below). A mathematical replacement now exists as a complete written
proof: `/home/ubuntu/aklt/reports/H1TREE_PROOF/h1tree.tex` (+ `wrapper.pdf`, `report.md`, exact replay programs
`checks/`, data `data/`): 38 path-shaped models; finite inputs = 23 mean bounds by Bernstein-coefficient checks,
22 scalar quadratic tests, 16 Pauli-sector matrices (dimension ≤ 66, entries ≤ 37 bits) with Gram/residual
witnesses, and a finite Boolean coverage enumeration of local kept sets; Theorem 1.17 derives the local inequality
`Z_E^τ ≥ c_type Z_{E+}^τ` for every actual non-exceptional U departure, with the same constants. NOTE its first
repair: it proves the inequality for actual departures (a D corner with k internal bonds has at most 2−k external
factors), not the literally larger covered-pattern statement of the paper's Definition 6.8.

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

Target for the whole new H1 certificate: at most ~15 minutes of single-thread Lean kernel time in total, at most
4 GiB per process, literal data of a few MB, every file with a `module` header and ≤ 10,000 lines, checks written
so that independent kernels (con-ron, NanoDa) handle them (no `decide`/`rfl` forcing huge unfoldings; put the large
operand first in big multiplications; no giant single literals — see "Replay hazards" in
`/home/ubuntu/aklt/reports/CERT_H3/report.md` and the measured Gram probe
`/home/ubuntu/aklt/reports/MATH_FIT/probes/GramPacked66.lean`: 48 s / 2.9 GiB for the largest matrix).

**Deliver** (statements, designs and assemblies only — no leaf proofs; proofs go to other writers):
1. SPLICE ANALYSIS. Find every place where the proof tree consumes H1: which Lean statements take
   `AKLT.Blueprint.Top.H1Statement` (or the certificate statements) as a hypothesis, in which form, and what
   they actually use of it. Decide the cleanest splice so that the new theorem replaces the two old H1
   certificate statements in `main_of_certificates` with the least re-proving: either (a) the existing
   `H1Statement` (or the exact statement the consumers need) is derivable from the new development as it stands,
   or (b) a new consumer-facing statement `H1ActualStatement` (the actual-departure form) is needed, in which
   case list every consumer leaf that must be re-proved against it, with the change each needs (state the new
   leaf statements; keep the old ones untouched and add V3 variants + a V3 assembly, as was done for V2).
   Justify the choice with the exact Lean statements.
2. BLUEPRINT `AKLT/Blueprint/H1T/`: Lean definitions of the models and of `Z`, `Cij`, `Zcur`, `Znext` on top of
   the existing definitions (`AKLT/Defs`, moment layer); the finite statement `H1TreeFiniteStatement` (closed
   Prop: the checks pass on the supplied data — design the data as small `Array`/`List` literals of integers in
   ordinary modules); closed-Prop leaf statements following `h1tree.tex` statement by statement (mean bounds from
   Bernstein checks; scalar tests ⇒ scalar inequality; matrix reconstruction = moment tensors; Gram/residual ⇒
   positivity, reusing `AKLT/Cert/H1` and `AKLT/Gen/Gram` soundness where it applies; coverage enumeration ⇒
   every actual local configuration reduces to a listed model; the reduction steps of Lemma 1.14 one case per
   leaf; Theorem 1.17), each with paper locator (h1tree.tex numbering), suggested proof route, trap notes, and
   difficulty; `Assembly.lean` proving the consumer-facing statement chosen in item 1 from the leaves and
   `H1TreeFiniteStatement`; and `leaves.json` in the usual format
   ({"lean_name","module","paper_label","paper_locator","difficulty","suggested_proof_route","trap_note"}).
   Prefer many small leaves to few large ones (each provable in one sitting by a mid-level prover); reuse
   already proved leaves (index `/home/ubuntu/aklt/state/lw/proved-index.tsv`) and name them in the routes.
3. CHECKER DESIGN + PILOT for `H1TreeFiniteStatement`: the executable checkers (Bernstein coefficients, scalar
   tests, tensor/matrix reconstruction, Gram/residual, coverage enumeration with its 2,048,000 raw choices) as
   kernel-friendly definitions in `module` files importing as little as possible; generate the data from
   `H1TREE_PROOF/data` with a script; run the full set of finite checks in Lean (`decide +kernel` or the
   project's packed style — your choice, measured) and report kernel time and memory per check and in total, and
   con-ron/NanoDa acceptance and times (`/home/ubuntu/aklt/bin/conron-check.sh` shows how). If the total misses
   the target, say which check dominates and how to cut it.
4. A new final-assembly statement: `AKLT.Final.main_of_certificates_T` taking `H1TreeFiniteStatement` in place of
   the two old H1 certificate statements (plus the two H3 ones unchanged), proved from the new assembly and the
   existing leaves, with any new consumer leaves as explicit hypotheses until they are proved.
Report `/home/ubuntu/aklt/reports/ARCH_H1T/report.md`, first line `STATUS: COMPLETE | PARTIAL (reason)`; write the
splice analysis first (within the first hour), keep the report current; `#print axioms` for every assembly; an
ORCH-SUMMARY (≤ 25 lines). Up to 6 Lean processes. This task was issued by the orchestrator (Fable); do the
architecture yourself, no leaf proofs.

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
