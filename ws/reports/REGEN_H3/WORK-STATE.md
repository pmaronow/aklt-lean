# Active handoff state

Task continues until all H3 artifacts, reports, and commit bundle are delivered. No sub-agents.
Root /home/ubuntu/aklt/rel/H3; report /home/ubuntu/aklt/reports/REGEN_H3.

Active workflow session 57598 runs finish-production.sh: full production, closing, then verify.
Poll workflow.log and receipts; failures must be fixed and resumed. All pilots passed (32 roots).
Full production currently about 1698/5032, max sampled RSS 94.72 GB, 16 Lean cap, 160 GB reserved.
Source reproduction session 87455 runs final generator under /usr/bin/time; source bytes should match archive-sources.json.
Archive session 78863 completed: see archive.json, H3-modules.tar.gz and .sha256. All original sources remain.

Critical repair: generated prefix reducers and PrefixAssembly need private `import all Init.Data.List.Sort.Basic`.
The standard library private splitter was hidden despite exposed mergeSortFuel. No hand-written Lean checker edits.
production.py emits correct headers and private sort imports. regen.py implements safe fresh processes, source/dependency/object hashing,
all theorem axiom prints, resource guards, normal Lake environment, automatic verified resumption.
All 5032 legacy template source hashes matched. Eleven mechanical retained-source samples match final generator output.
2735 generated exported theorems; max source lines 1058; source bytes about 30.71 GB.
Paired control timings in paired-controls.json: B1 P0085 new97.55 vs old82.28 (report this regression honestly),
C1 P0106 new86.55 vs old94.70, C3 Plane G0170 new37.43 vs old41.44; fresh single-process controls.
Native literal plugin experiment had identical public olean but no speedup without import phase changes; NOT adopted.
No production uses the plugin. native-literal/experiment.json records hashes and status.

Remaining work after workflow completes:
- Fix any Lean failures; production can resume via python3 AKLT/Cert/H3/regen.py build --jobs16 --ram-gb160.
- Closing source already contains exact-type examples, prints, axiom checks for requested automaton10 and stationaryCheck.
- Verify outputs summary.json, manifest.json, axioms.json, declarations.json; every generated module has successful exit and all three olean artifacts.
- Verify final regeneration source hashes equal archive source hashes and all legacy template hashes equal; archive SHA recorded.
- Run final official source/header checks (already 6147 files passed both, but rerun after all final headers now stable).
  Verifier /home/ubuntu/dbl/scratch/PAL-DRY/tools/PalomarSubmission.
- Produce plaintext SHA256SUMS for all generated sources and compiled artifacts (manifest JSON already records hashes).
- Finalize REGEN-H3.md, REGEN-CHANGES.md, report.md with timings, exact names/types, axiom output, limits, all source retention, handoff.
- IMPORTANT .git is mounted read-only. `git add` failed with read-only .git/index.lock; git-stage.log records error.
  User was told. Must create final commit in writable temporary git metadata with parent original d1320320e7cbf2d216d0afc87be92aabb206d690,
  using only 12 handwritten changed paths (git status); create self-contained commit bundle/format-patch under report for Fable.
  Do NOT try to bypass protected .git. Explicitly say original clone ref could not be updated. Report STATUS PARTIAL for this limitation,
  even if all Lean work complete; commit bundle supplies a concrete recoverable commit.
- No global Solution/Audit/Comparator run required by this H3-only handoff; Fable needs H1 closing artifacts for combined final assembly.
- Final report first line STATUS COMPLETE or PARTIAL(reason), end ORCH-SUMMARY <=20 lines. No user permission questions needed.
- Keep user updated at least each minute while long jobs run; use clock.sleep <=45 seconds, poll concise logs.

Changes in clone: AKLT/Cert/H3 README, export.py, generate_prefix.py, production.py, production_audit.py,
production_receipts.py, run_checks.py; new inputs.json, prefix-reference.json, regen.py; new REGEN-CHANGES.md, REGEN-H3.md.
No generated sources are tracked in Git; .lake/packages untouched; no lake update or Mathlib rebuild.
