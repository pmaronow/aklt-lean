# FINAL_FILL — portable certificate tooling, H1 cold-verify stage, refreshed manifests

The orchestrator (Fable) issues this task directly to you. Do the work yourself in this session; do not
launch sub-agents and do not hand any part to another model.

## Where you work

- Work ONLY in the clone `/home/ubuntu/aklt/wt/PAL_FIT/_fill` (already created from the final release tree at
  commit `42b16c3`; `.lake/packages` is the shared read-only symlink; there is no `.lake/build`).
- Write your report to `/home/ubuntu/aklt/reports/PAL_FIT/final-fill/report.md` (create the directory).
- `/home/ubuntu/aklt/final` is the release tree. Two certificate builds are running in it right now.
  You may READ it and `/home/ubuntu/aklt/reports/FINAL`, `/home/ubuntu/aklt/reports/REGEN_H1`,
  `/home/ubuntu/aklt/reports/REGEN_H3`. Never write there, never run a command with it as working directory
  that creates files, and never start a Lean, Lake, or certificate-runner process anywhere: the machine's CPU
  and memory are committed to those builds. Python syntax checks, dry-runs, hashing, and small pure-Python
  self-tests are fine.

## Hard constraints

1. No change to any `.lean` file, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, or `comparator.json`.
   `git diff --stat 42b16c3 HEAD -- '*.lean' lakefile.toml lake-manifest.json lean-toolchain comparator.json`
   must print nothing at the end. The Lean source digest (`python3 scripts/source_digest.py`) must stay
   `c875dff024d396b0b78f1fa955ea5d38e8f577e1d8bd69e970fd02bea906bee9`.
2. The running builds were started with the tools at `42b16c3`. Your tool edits must not change: any generated
   source byte, any owner/dependency map, any build key or receipt format, any hash that a receipt records, or
   the meaning of any existing command-line option or environment variable (`H1_REGEN_REPORT`, `H1_REGEN_ROOT`,
   `H3_INPUT_DIR`, `H3_REPORT_DIR`). After the builds finish, the orchestrator will run
   `AKLT/Cert/H1/tools/production_receipts.py verify` and `AKLT/Cert/H3/regen.py verify` with YOUR tools against
   the receipts those builds wrote. They must pass unchanged. State in the report, for each edited tool, why
   this holds.
3. American English throughout. No process wording in release files ("orchestrator", "hand-back", "writer",
   "campaign", "Sol", "Fable", wave/leaf labels). No machine-specific paths in any file a reader runs or reads
   as instructions.
4. Do not guess author names, ORCIDs, a license, or public URLs. Leave those author TODOs as they are.

## Tasks

### A. H1 tools: remove machine-specific paths
`grep -n "/home/ubuntu" AKLT/Cert/H1/tools/*.py` lists them. Replace each with a repository-relative default
and/or an environment variable or option:
- numeric inputs: a single `H1_INPUT_DIR` (default `<repo>/data/h1`; `/data/` is git-ignored) used by
  `packed.py`, `production_bridge_export.py`, `production_coverage.py`, `production_export.py`,
  `production_receipts.py`;
- report directory: `H1_REGEN_REPORT` keeps working; default becomes `<repo>/verification/runs/H1`
  (`/verification/runs/` is git-ignored).
- `production_bootstrap.py` is broken: it requires `AKLT.Cert.H1.Production.All` and
  `AKLT.Cert.H1.Production.Audit`, which do not exist in this tree (the final build skipped it for that
  reason). Either repair it so it checks exactly the hand-written modules the generated family imports and
  that exist, or delete it; make the documentation match.
- Scripts that can only run on the development machine and that no release command uses
  (`production_merge_check.py`, `production_leaves.py`, the retained-legacy-source route of
  `production_regen.py`, and anything similar you find): delete them if nothing in the release imports or
  documents them as a step; otherwise make them portable. List each decision.
The release route is the numeric-inputs route:
`production_receipts.py inputs` → `production_reexport.py --scratch DIR --install --report-dir R` →
`production_build.py R/data-only-production.json --jobs N --cap-gib 7 --report-dir R` →
`production_receipts.py verify R/data-only-production.json --report-dir R` →
`production_close.py --report-dir R`. That exact sequence is what is running now in the final tree
(driver: `/home/ubuntu/aklt/bin/final-h1b.sh`, report directory `/home/ubuntu/aklt/reports/FINAL/H1`).

### B. H3 tools: same treatment
Defaults in `AKLT/Cert/H3/export.py`, `generate_prefix.py`, `production.py` become repository-relative
(`<repo>/data/h3`, `<repo>/verification/runs/H3`) with `H3_INPUT_DIR` / `H3_REPORT_DIR` still honored.
`production_plan.py` and `validate_merge.py` are historical; delete them if unused by release commands and
the inventories, otherwise make them portable. The final H3 build used
`/home/ubuntu/aklt/bin/final-h3b.sh` (read it for the exact commands).

### C. Complete the cold-verification driver
`scripts/cold_verify.py` has the placeholder `TBD-H1-PORTABLE-ENTRYPOINT` and refuses to run without
`--h1-stage`. Replace the placeholder with the real H1 stage (the sequence in A), with jobs/memory options
consistent with the H3 stage, so that `scripts/cold-verify.sh` runs end to end from numeric inputs with no
extra adapter. Keep the dry-run mode and extend its self-checks. Remove the placeholder from
`VERIFICATION.md` and fold `docs/regeneration/H1-INTEGRATION.md` into `docs/regeneration/H1.md`.

### D. Rewrite the H1 regeneration notes as release documents
`docs/regeneration/H1.md` and `docs/regeneration/H1-CHANGES.md` were written as an internal report (machine
paths, "orchestrator", read-only `.git`, patch delivery, pilot bookkeeping). Rewrite both in the style of
`docs/regeneration/H3.md` / `H3-CHANGES.md`: what the family is, inputs and their pins, the exact commands
(repository-relative), resource needs, what the receipts record, the measured facts from
`/home/ubuntu/aklt/reports/REGEN_H1/report.md` that a reader needs (7,964 modules, 414,638 theorem audits,
25 kinds, per-kind table, 26–28% higher CPU on the coverage-frontier modules relative to the pre-module-system
build, byte-for-byte agreement between the two generation routes), and the closing contracts. Mark every
number that will be replaced by the final-tree build with a `TBD-H1-*` field already used in
`VERIFICATION.md` rather than inventing new field names where one exists. Check `AKLT/Cert/H1/` and
`CertData/H1/README.md` for stale statements and fix them.

### E. Refresh manifests invalidated by comment-only Lean edits
Commit `ef79c6c` changed comments in 12 Lean files after the manifests were written. Regenerate or update
every pinned hash that covers those files: `verification/port/source-manifest.tsv`, the expectations of
`scripts/verify_sources.py`, `verification/layout/protected-baseline.json.gz`, `verification/statement-sources.json`
if affected, `verification/source-inventory.json` if affected, and anything else `grep` finds. Then run every
pure-Python checker in `scripts/` that does not start Lean (`verify_sources.py`, `make_challenge.py --check`,
`source_digest.py`, `inventory.py` in check mode if it has one) and record the results. `Challenge.lean`
must be reproduced byte for byte.

### F. Sweep
- `grep -rn "/home/ubuntu" --include='*.py' --include='*.sh' --include='*.md' --include='*.yaml' --include='*.toml' .`
  outside `verification/` historical receipts: nothing operational may remain. Update
  `docs/PORTABILITY.md` and `verification/layout/absolute-paths.tsv.gz` accordingly.
- British spellings and process wording in every file you touched or created, and in `README.md`,
  `VERIFICATION.md`, `docs/*.md`.
- List (do not fill) every remaining `TBD-*` field and where it is.

## Delivery
Commit in `_fill` on top of `42b16c3` (one or a few commits, clear messages, no co-author lines needed).
Report: STATUS line first; what changed per task; the constraint proof for item 2; checks run and results;
remaining `TBD-*` fields; anything you could not do. End with an `## ORCH-SUMMARY` of at most 15 bullets.
