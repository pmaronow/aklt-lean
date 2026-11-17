# REL_FEAS — release feasibility: independent checkers on the certificate modules, and the release procedure

**Context.** `/home/ubuntu/aklt` holds a Lean 4 formalization (repo `/home/ubuntu/aklt/repo`, branch `main`;
headline `AKLT.Challenge.MainStatementV2`; guide `/home/ubuntu/aklt/briefs/GUIDE.md` — read its release sections).
The final theorem will depend on two families of generated finite-certificate modules, kernel-checked by Lean in
separate opt-in Lake libraries:
- H3′: worktree `/home/ubuntu/aklt/wt/CERT_H3` (report `/home/ubuntu/aklt/reports/CERT_H3/report.md`): about
  5,035 generated check modules, ~20 CPU-hours of Lean kernel time; one complete case ("B1", 1,160 modules) is
  already built there, the rest is being produced now.
- H1: worktree `/home/ubuntu/aklt/wt/CERT_H1` (report `/home/ubuntu/aklt/reports/CERT_H1/report.md`): 7,962
  patterns / 12,173 blocks, forecast ~115 CPU-hours of Lean kernel time; a 100-pattern pilot is built, production
  is running now.
The release standard requires, on a clean clone: a clean build, the axiom audit, and acceptance of the exported
environment (the dependency closure of the headline theorem) by the independent checkers `con-ron --verified` and
NanoDa (binaries in `~/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/`: `con-ron`, `nanoda_bin`,
`leanexport`), and the Palomar Comparator. On ordinary proof modules con-ron checks ~82,000 declarations in about
two minutes, but it has no special support for some reductions that Lean's kernel shortcuts; on two proof modules
its memory grew without bound. Nobody has yet measured the independent checkers on the generated certificate
modules. `/home/ubuntu/aklt/bin/conron-check.sh WT OUT MODULE…` shows how an export + con-ron (with a memory cap)
+ NanoDa run is done for chosen modules of a worktree (read it; adapt a copy for other Lake libraries).

**Both production lanes are running: treat their worktrees as READ-ONLY and do not build inside them.** Work in
`/home/ubuntu/aklt/wt/REL_FEAS` (your worktree, a checkout of `main`, built); to test generated modules, copy a small
sample (sources and, where usable, built `.olean`s) into your own worktree or scratch under your report directory.
Use at most 6 CPU-heavy processes and 60 GB RAM in total (cap every checker run), and keep disk use under 30 GB.

**Deliver.**
1. MEASURE: for a representative sample of generated modules of each family (H3′: a few B1 row/prefix/automaton
   check modules of different sizes; H1: a few pilot Gram/packed check modules), the Lean kernel time and memory
   versus con-ron and NanoDa time and peak memory on the export of exactly those declarations (with closure).
   State clearly whether each checker ACCEPTS, and the slow-down factors. If a checker blows up, find the
   declaration shape responsible (e.g. `Nat`/`Int` literal arithmetic by `decide`/`rfl`, `Nat.rec` unfolding,
   bitwise ops, large `List`/`Array` literals) with a minimal example.
2. EXTRAPOLATE to the full release (all modules of both families + the proof tree): wall time and memory per
   checker on this 64-thread, 495 GB machine, for (a) one monolithic export, (b) a sharded scheme (independent
   exports per group of certificate modules, each with its closure, run in parallel) — and say precisely what the
   sharded scheme does and does not establish compared with one monolithic check, and whether the Comparator can
   consume it.
3. RECOMMEND: if the independent checkers cannot do the release in a reasonable time (say more than ~12 hours) or
   memory, propose concrete changes ranked by cost — e.g. reformulating the check declarations into a form the
   checkers handle well (what form, measured on a converted sample), fewer/larger or smaller modules, different
   literal encodings — with measured evidence for the top proposal. Do not edit the generators themselves; give
   exact instructions the lanes can apply.
4. RELEASE SCRIPT: `release/run-release.sh` (in your worktree) that, from a clean clone of the repository at a given
   commit plus the certificate attachment, performs the whole release check end to end with logs and receipts
   (clean build incl. the certificate libraries, token scan, axiom audit of the headline, export, con-ron with
   `--progress=1` and a memory cap, NanoDa, Comparator per the guide), parameterised by job counts; test whatever
   part can be tested today on the current tree (the headline is not yet proved: test on
   `AKLT.Final.mainV2_of_open` or another proved top-level theorem as stand-in).
Report `/home/ubuntu/aklt/reports/REL_FEAS/report.md`, first line `STATUS: COMPLETE | PARTIAL (reason)`, with tables
of measurements, the extrapolation, the recommendation, and an ORCH-SUMMARY (≤ 25 lines). Write the measurement
part (items 1–2) to the report as soon as you have it, before doing items 3–4.

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
