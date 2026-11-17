Orchestrator message — next phase for you: build the release package and port it to Lean's module system.
Direction settled by the author: the submission is the reduction with the paper's two finite inputs as premises.
On `main` (commit d77c3ca) there is now `AKLT.Final.main_of_inputs : H1Statement → H3Statement → MainStatementV2`
(`AKLT/Final/Inputs.lean`) and a package skeleton `palomar/` (standalone `Challenge.lean` of 572 lines with the
theorem `aklt_gap_of_inputs`, `Solution.lean`, `Audit.lean`, `comparator.json`, `formalization.yaml`, `scripts/`,
`FIDELITY.md`, and `port-list.tsv`: the exact 616-file Solution closure, 615 of them needing the `module`
header). The architect's report is `/home/ubuntu/aklt/reports/ARCH_PKG/report.md` (read "Package layout",
"Exact port list", "Build, axiom and Comparator diagnostics": it names two known issues to fix during the port —
the modern/legacy `Compass.step` matcher identity difference found by the Comparator, and exposing
`AKLT.Challenge.size_neZero`). Your own port procedure is `reports/PAL_FIT/tools/port_modules.py`.

The legacy tree on `main` must NOT be ported in place (large generated certificate libraries were compiled
against it). Do:
1. MATERIALIZE the release root as a separate standalone Lake project at
   `/home/ubuntu/aklt/wt/PAL_FIT/_pkg` (inside your writable area; `git init` it; first commit = the unported
   copy): exactly the files of `port-list.tsv` taken from `/home/ubuntu/aklt/repo` at d77c3ca at their
   release-relative paths, plus the skeleton files; pinned `lean-toolchain`, `lakefile`, `lake-manifest.json`
   as in the model package; `.lake/packages` may be a symlink to `/home/ubuntu/aklt/packages-store` for your
   iterations. No other Lean file may be present anywhere in the release root.
2. PORT every Lean file to the module system with your script, then make the whole package build
   (`lake build` of the default target, plus `Challenge`, `Solution`, `Audit`) from a fresh `.lake/build`,
   fixing what breaks. Rules: do not change the meaning of any statement or definition (the three statements in
   Challenge and their in-tree counterparts must stay as they are; `h1_iff`, `h3_iff`, `main_iff` must keep
   holding); do not rewrite proofs beyond what visibility/exposure requires — record every proof-body change
   (file, declaration, reason) in `PORT-CHANGES.md`; keep all theorem names; only the axioms propext,
   Classical.choice, Quot.sound; no `sorry` except the one Challenge placeholder; no `native_decide`, `unsafe`,
   `implemented_by`, `extern`, new `opaque`; every file with `module` header and at most 10,000 lines. You may
   use up to 48 Lean processes and 300 GB RAM — the machine is otherwise idle.
3. VERIFY with the official verifier's own stages on the ported package (source/configuration/header checks,
   default build, strict Audit, Comparator with Lean and NanoDa on the protected Challenge, con-ron replay),
   as far as they run in your environment, and fix every finding that is ours to fix (leave author/maintainer/
   license metadata as clearly marked TODO fields and list them). Measure each stage (wall, CPU, peak RSS) with
   16 CPUs' affinity; give the total against the 19,800 s allowance, counting a cold Mathlib cache fetch
   separately as an estimate.
4. Write `scripts/cold-verify.sh` in the package: from a fresh clone of the package repository at a given commit
   it fetches the pinned Mathlib cache and runs the whole verification end to end non-interactively with logs
   and a JSON receipt — written so that the orchestrator can run it inside a real 16 CPU / 32 GiB cgroup
   (`systemd-run --user --scope -p CPUQuota=1600% -p MemoryMax=32G -p MemorySwapMax=0 …`); it must not need
   anything outside the clone except the official verifier checkout path and the toolchain.
Report: rewrite `/home/ubuntu/aklt/reports/PAL_FIT/report.md` first line to
`STATUS: PORT COMPLETE | PORT PARTIAL (reason)` and append a section "release package" with the stage table, the
list of proof-body changes, verifier findings fixed/remaining, the package commit hash, and an ORCH-SUMMARY
(≤ 20 lines). Write the stage results as soon as each is available.
