Orchestrator message — fix round after two independent fidelity reviews of the statement layer. Both reviews
(`/home/ubuntu/aklt/reports/FID_FABLE/report.md`, `/home/ubuntu/aklt/reports/FID_ASTRA/report.md` — read both in
full) conclude FAITHFUL WITH REMARKS with no Fatal or Major finding. Apply their Minor findings in the release
root `/home/ubuntu/aklt/wt/PAL_FIT/_pkg`, under ONE hard constraint:

**Do not modify any file in the import closure of the generated certificate modules** (the modules listed in
`verification/regen-interface/H1-imports.tsv` and `H3-imports.tsv` and everything they import — 35 hand-written
modules, including `AKLT/Defs/Kernel.lean` and `AKLT/Defs/Stationary.lean`). Two other agents are rebuilding the
certificates against those files right now; any change to them, even a comment, would force a full rebuild.
Compute that closure first and check every file you touch against it. Remarks that concern such files are
recorded in a notes document instead (item 7).

1. Paper references in the Challenge's doc comments (both reviews): in the library sources the Challenge is
   generated from, and then in the regenerated `Challenge.lean`: the torus, bonds, determinant `q_xy`, the
   product state and the Hamiltonian are in Definition 1.1 (`d:model`, `sec1-result.tex`); the polynomial model
   and its norm in Definition 3.1 (`d:poly`, `sec3-quantum-frames.tex`); the main theorem is Theorem 1.2
   (`t:main`). Remove references to documents that are not paper locations ("revision plan", `FIDELITY.md`) from
   the statement files.
2. The superseded even-period statement `MainStatement` (`AKLT/Challenge/Main.lean`, with references in
   `Sanity.lean`): it is NOT the paper's theorem (even periods only, kernel only eventually, no `B ≠ 0`). If
   nothing in the proof of `MainStatementV2` needs it, delete it and its references; if something does, move it
   to a clearly named legacy module with a doc comment saying exactly how it differs from Theorem 1.2, so that
   the Challenge source file contains only what the Challenge copies.
3. `Solution.lean`: `main_iff` is `Iff.rfl` on a definition; say so in its doc comment, and say that the identity
   between the Challenge's copied definitions and the library's is established by the mechanical generation of
   `Challenge.lean` from the library sources and checked by the Comparator. Add to the verification scripts a
   check that `Challenge.lean` is byte-for-byte what the generator produces from the current library sources.
4. The two `run_elab … auxLemmasExt …` lines in `Challenge.lean`: a statement file should not contain
   environment-modifying code if that can be avoided. Try restructuring so they are not needed (for example,
   move `MainStatementV2` into the same library source file as the model definitions and keep `MainV2.lean` as a
   thin re-export, so that the Challenge is a copy of one file) and rerun the Comparator's statement comparison.
   If it cannot be avoided, keep the lines and document precisely why in the README section on the Comparator.
5. Add one sentence to the doc comment of the spin matrices: the label of `e_k` under `spinZ` is the negative of
   the weight the paper displays for the monomial `z₁^{4-k} z₂^k`; this relabeling does not change the Casimir,
   the projection, or the Hamiltonian.
6. `AKLT/Challenge/Sanity.lean`, the unproved sanity proposition `BondRank` (the eigenvalue-20 eigenspace of the
   bond Casimir has dimension `9·5^(LN−2)`): try to prove it (two-site computation on the 25-dimensional space
   — Casimir eigenvalue 20 has multiplicity 9 — then tensor with the spectator sites). Give it up to about one
   hour; if it does not close, leave the proposition, say in its doc comment that it is an unproved sanity
   statement that nothing depends on, and report how far you got. Same for any other stated-but-unproved sanity
   proposition in that file (list them).
7. `AKLT/Blueprint/Top/Response.lean`: "modified kernel" → "type-dependent kernel" (check the file is not in the
   forbidden closure). Create `docs/STATEMENT-NOTES.md` recording, for readers, the remarks that concern files
   you may not touch: `ClosedTrail` is the paper's class of first-hit trails `T_n^X` (Definition 7.7), not closed
   trails; the "legacy" definitions that sit beside the corrected `…V2` ones, which statements use which, and in
   particular that the legacy stationary coefficient differs from the paper's operator at the center site while
   agreeing with it on functions vanishing there (the Astra review's finding 2); the raw exchange-sign type has
   redundant indices on singles and U pairs (its finding 3); and the convention of item 5.
8. Rebuild what your edits affect from fresh objects, rerun the source/header checks, the strict hand-written
   Audit, the statement comparison, and the two-input regression; commit.
Report: append a section "fidelity fix round" to `/home/ubuntu/aklt/reports/PAL_FIT/report.md` (first line
`STATUS: FIDELITY FIXES COMPLETE | PARTIAL (reason)`): each review finding → what was done (or why not), the
forbidden-closure check, verification results, package commit hash. American English.
