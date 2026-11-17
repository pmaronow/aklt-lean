Orchestrator message (the orchestrator, Fable, issues this task; do it yourself, no subagents, no hand-off) —
release layout and documentation for the clean `main`.

**Context.** The author's target: `main` of the private repository is a clean tree containing the manuscript and
the complete Lean formalization, with Challenge / Solution / Audit / comparator.json at Palomar standards
(module system, line caps, Mathlib-only Challenge), but it is NOT a Palomar submission and Palomar's CPU/memory
limits do not apply. American English throughout.

The final tree is `/home/ubuntu/aklt/final` (= your `_pkg` at `f7d40ef` + the H3 regeneration commit, HEAD
`2707fd8`). A from-scratch build is running there right now (hand-written targets, then
`AKLT/Cert/H3/regen.py generate/build/close/verify` with report directory `/home/ubuntu/aklt/reports/FINAL/H3`).
The H1 regeneration is still running in `/home/ubuntu/aklt/rel/H1`; its hand-back will add
`AKLT/Cert/H1/tools/*.py` (modified and new), `CertData/H1/Close/Main.lean`, `REGEN-H1.md`, and its own
`REGEN-CHANGES.md`; the orchestrator merges it and then runs the H1 build in `final`.
**Do not touch `/home/ubuntu/aklt/final`, `/home/ubuntu/aklt/rel/*`, or `/home/ubuntu/aklt/reports/{FINAL,REGEN_*}`.**

**Your workspace:** `/home/ubuntu/aklt/wt/PAL_FIT/_tidy`, a clone of `final` at `2707fd8` (already created; its
`.lake/packages` is the shared store; it has no build directory — do not run Lean builds there beyond what a
script dry-run needs; use `_pkg` if you must elaborate something). Commit there. The orchestrator will apply your
commit(s) on top of `final` after the certificate builds, so:

**Hard constraints (the running builds must stay valid).**
- Change NO `.lean` file, and not `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `comparator.json`.
- Do not change anything that enters the certificate runners' receipts, contexts, or dependency hashes (read
  `context()`, `source_info()`, `dep_hashes()` in `AKLT/Cert/H3/regen.py` and the files they hash; the H1 runner
  in `/home/ubuntu/aklt/rel/H1/AKLT/Cert/H1/tools/production_regen.py` is read-only reference). If a file is
  hashed, leave it byte-identical and document instead. `verification/generated-modules.json` and
  `verification/regen-interface/*` are read by the runners: keep their paths and bytes.
- Do not move or rename `AKLT/Cert/H1/tools/*`, `AKLT/Cert/H3/*`, `CertData/**`, or anything a runner opens by path.

**Deliverables.**
1. **Root layout.** The root should contain only what a reader or the build needs: `README.md`,
   `VERIFICATION.md`, `Challenge.lean`, `Solution.lean`, `Audit.lean`, `comparator.json`, `formalization.yaml`,
   the Lake files, `Handwritten.lean`, `AuditHandwritten.lean`, the library directories, `Regression/`,
   `RegenSamples/`, `scripts/`, `docs/`, `verification/`, `manuscript/`. Move the port/regeneration records
   (`PORT-CHANGES.md`, `PORT-MANIFEST.tsv`, `port-list.tsv`, `direct-leaves.txt`, `reachable-leaves.txt`,
   `AMERICAN-ENGLISH-IDENTIFIERS.tsv`, `REGEN-INTERFACE.md`, `REGEN-CHANGES.md`, `REGEN-H3.md`, `FIDELITY.md`,
   `statement-sources.json` if no script needs it at the root) under `docs/` or `verification/` — only after
   checking every script, runner and document that refers to them, and updating those references (subject to
   the hard constraints: if a hashed runner file refers to a root path, leave that file where it is). Say where
   the H1 hand-back's `REGEN-H1.md` and `REGEN-CHANGES.md` should go so the two families' notes do not collide
   (for example `docs/regeneration/H1.md`, `docs/regeneration/H3.md`, one merged change note).
2. **`manuscript/`**: copy the paper from `/home/ubuntu/aklt/manuscript-v2` (commit `241c2d8`; all `.tex`,
   bibliography, figures, and `main.pdf`; no `.git`, no LaTeX auxiliary files). Do not edit the paper.
3. **Portability.** No script or document in the release should require `/home/ubuntu/...`. Scripts take the
   input-data directory and report directory from environment variables or arguments with repository-relative
   defaults (subject to the hard constraints — where a hashed file has an absolute default, keep the file,
   and make the documented commands set the environment variables explicitly). List every remaining absolute
   path with the reason. The numeric inputs are not in Git (multi-GB): the README must say what they are
   (file names, sizes, SHA-256 from `AKLT/Cert/H3/inputs.json` and the H1 equivalent) and that they and the
   generated-source archives are attached to a release of the repository (leave a clearly marked placeholder
   for the release tag; the orchestrator fills it in).
4. **`README.md`** rewritten for the finished state (do not describe history, phases, or "pending" work): the
   theorem and its exact Lean statement; the map paper ↔ Lean (Theorem 1.2, Definitions 1.1 and 3.1, inputs
   (H1), (H2), (H3_h) and their Lean names; where each section's results live); repository layout; the two
   parts (hand-written derivation, checked in minutes by `lake build`; generated certificate libraries, checked
   by the runners in tens of CPU-hours) ; exact commands for a full from-scratch verification; what the Audit
   checks; pointers to `VERIFICATION.md` and `docs/STATEMENT-NOTES.md`. Short, factual, no marketing.
5. **`VERIFICATION.md`** as a template the orchestrator completes after the final build: sections for toolchain
   and pins; a "Lean source digest" (define it: SHA-256 over the sorted list of `path sha256` for all tracked
   `.lean` files plus `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`; add `scripts/source_digest.py`
   that prints it and a `--check` mode against a recorded value) so that the record identifies the exact Lean
   sources independently of later documentation commits; hand-written build; H1 and H3 certificate builds
   (modules, CPU-hours, peak memory — placeholders `TBD-…`); closing theorems and axiom output; Challenge
   requirements; statement comparison (Lean, NanoDa) and its negative control; independent kernels (what con-ron
   and NanoDa accepted: the full two-input reduction; the certificate modules are checked by the Lean kernel at
   build time; say plainly that a full replay of the unconditional proof in an independent kernel was not run
   and why — size: REL_FEAS estimate); the fidelity reviews (three independent reviews, verdicts, where the
   remarks were resolved). Fill in everything that is already known from your reports; mark the rest `TBD-…`.
6. **`scripts/cold-verify.sh`** (new or revised): one driver for the complete from-scratch verification in a
   fresh checkout: hand-written targets → H3 runner (generate, build, close, verify) → H1 runner → the closing
   modules `CertData.H1.Close.*`, `CertData.H3.Close.Main`, `CertData.Close.All`, `Solution`, `Audit` → strict
   audit and `#print axioms AKLTPalomar.aklt_gap` → `make_challenge.py --check` → source/header checks →
   statement comparison. Parameters: jobs, memory, input directory, report directory. For the H1 steps, read the
   H1 runner in `rel/H1` (read-only) and its `REGEN-H1.md` if present; if its interface is not final yet, leave
   that stage as a clearly marked call to `AKLT/Cert/H1/tools/production_regen.py` that the orchestrator
   completes. Do not run it. Explain in the README how the direct-compiled certificate objects relate to
   `lake build` (Lake would schedule the same compilations without the runners' memory guards).
7. `.gitignore`: generated certificate sources and build output excluded by pattern rather than by a 185 KB list,
   if patterns can express it exactly (verify with `git status --ignored` reasoning against
   `verification/generated-modules.json`; the hand-written files under `CertData/` must stay tracked).
8. `formalization.yaml`: leave author identities, ORCIDs and license as clearly marked author TODOs; make the
   rest current.

Report: `/home/ubuntu/aklt/reports/FINAL_TIDY/report.md`, first line `STATUS: TIDY COMPLETE | PARTIAL (reason)`:
final root listing, every moved file (old → new) and each reference updated, proof that no constrained file
changed (`git diff --stat 2707fd8 HEAD -- '*.lean' lakefile.toml lake-manifest.json lean-toolchain comparator.json`
empty; runner-hashed files byte-identical), remaining absolute paths, the list of `TBD-…` placeholders, commit
hash; end with `## ORCH-SUMMARY` (≤ 20 lines).
