# VENDOR-1 — vendor the donor code the streamlined proof needs

**Goal.** Bring into the campaign repo, at our pin, the donor Lean closures that the streamlined proof will use, so
that writers import instead of re-proving. The plan of the proof is `/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md`
(statement inventory: finite conditional expectations, couplings, density/block comparison, finite contraction,
spectral gap of finite reversible chains, planar boundary connectivity/Timár, polynomial/sl₂ edge lemma, finite
frames, dyadic arithmetic). The donor audit with exact commits, closures, licences and trial ports is
`/home/ubuntu/aklt/reports/VENDOR-PLAN/report.md` (clones in `/home/ubuntu/aklt/donors/`, trial ports in
`/home/ubuntu/aklt/scratch/VENDOR-PLAN/`). The streamlined proof no longer uses a Knabe criterion, a continuous
sphere measure, cell blocking or MO/MOS; do not vendor code only those would need.

**Deliver:** for each donor closure the plan actually needs (decide from the plan; justify each inclusion and each
exclusion in the report), copy it into `AKLT/Vendor/<Donor>/` with namespaces relocated to `AKLT.Vendor.<Donor>`,
licence headers and attribution retained, a `THIRD_PARTY_NOTICES.md` at the worktree root, and the trial-port fixes
applied; build every vendored module; scan for forbidden tokens and run `#print axioms` on the key theorems. Also
list, per plan statement, which vendored declaration covers it (a reuse map). Worktree
`/home/ubuntu/aklt/wt/VENDOR_1`; report `/home/ubuntu/aklt/reports/VENDOR_1/report.md`. Up to 8 Lean processes.

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
