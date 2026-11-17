# AKLT Lean campaign — state after posting (2026-11-17 17:32 UTC)

DONE. Nothing is running for this campaign.

- GitHub (private pmaronow/aklt-lean): `main` 375f0e0 = clean release commit; tag/release `v1.0` with inputs,
  generated sources, receipts; `development` bc8a413 = working history of the release tree;
  `pre-release-main` c5280ad = old main; `campaign-state` 02cc7f0 = log, briefs, tools, text reports.
- Workstation `aklt-ws`: release tree `~/aklt/final` (bc8a413, with all generated sources and objects built);
  reports `~/aklt/reports/FINAL`; release assets `~/aklt/release-final`; paper `~/aklt/manuscript-v2` (9806e35).
  RULE still in force: no `.lean` edits in `~/aklt/final` (they invalidate ~175 CPU-h of certificate receipts).
- The instance was left running because another campaign's job (tmux `tube`) was active on it. The certificate
  objects (~32 GB) exist only there; they can be rebuilt from the release (v1.0) in ~175 CPU-h.

Author items (not done, need the author):
1. License: add LICENSE at the root and its SPDX id in formalization.yaml (vendored QICLean files are Apache-2.0).
2. Authors, ORCIDs, maintainer, provenance notes in formalization.yaml.
3. Public repository decision; then the repository reference in the paper (`sec1-result.tex:124`, `% CHECK`).
4. Optional cleanup: prerelease `certificates-2026-11-17`; branches `palomar-package-wip`, `integration`,
   `validated-core`, `pre-release-main`.

If any of 1–3 changes files on main: edit in `~/aklt/final` (non-Lean files only), run the six pure-Python checks
in verification/layout/README.md, commit, bundle to the Mac, secret scan, push `development`, and add a new
commit on `main` (do not rewrite v1.0).
