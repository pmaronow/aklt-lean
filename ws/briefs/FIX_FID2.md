Orchestrator message (the orchestrator, Fable, issues this task; do it yourself, no subagents, no hand-off) —
second fidelity fix round in the release root `/home/ubuntu/aklt/wt/PAL_FIT/_pkg`.

**The freeze on the certificate dependency closure is lifted in `_pkg`.** Decision by the orchestrator: the final
release will be built once from scratch from the merged tree (hand-written sources + regenerated certificate
sources), so the hand-written files the generated modules import may now be edited in `_pkg`. The two
regeneration clones `/home/ubuntu/aklt/rel/H1` and `/home/ubuntu/aklt/rel/H3` are still building: do NOT touch
them, their `.lake` directories, or anything under `/home/ubuntu/aklt/reports/REGEN_*`. Work only in `_pkg`.
The machine is shared with those builds: use at most 12 Lake/Lean threads (`LEAN_NUM_THREADS=12`), CPUs as before.

Apply exactly the items your previous round deferred, and nothing else in those files (no change to any
definition body, statement, or proof; the generated-module interface — every name, type and universe that
`verification/regen-interface/*` records — must stay identical):

1. `AKLT/Challenge/Main.lean`: delete the superseded even-period `MainStatement` (your search found no Lean
   caller) together with any text that exists only to describe it; correct the doc comments in the library file
   to the paper locations (Definition 1.1 `d:model` in `sec1-result.tex`; Definition 3.1 `d:poly` in
   `sec3-quantum-frames.tex`; Theorem 1.2 `t:main`), remove references to non-paper documents ("revision plan",
   `FIDELITY.md`), and add the spin-convention sentence to the library doc comment of `spinZ`. After this the
   generator should copy the library comments verbatim: remove the comment-correction special case from
   `scripts/make_challenge.py`, regenerate `Challenge.lean`, and confirm `--check` passes. Aim for doc comments
   that read naturally: cite the paper location once per declaration in the form
   "Definition 1.1" / "Definition 3.1" / "Theorem 1.2" (the label and file name need appear only once, in the
   module doc comment at the top), instead of repeating "(`d:model`, `sec1-result.tex`)" in every comment.
2. `AKLT/Challenge/Sanity.lean` and any other file: remove what refers to the deleted statement; keep the
   even-size arithmetic only if something uses it.
3. `AKLT/Blueprint/Top/Response.lean`: "modified kernel" → "type-dependent kernel".
4. `docs/STATEMENT-NOTES.md`, `README.md`, `FIDELITY.md`: update so they describe the tree as it now is (no
   "frozen", no "deferred"; the old statement is gone). Keep the notes on first-hit trails, legacy vs V2
   matchers and stationary operators, exchange-sign indices, and the spin convention.
5. Verify that the interface used by the generated certificate modules is unchanged: for every declaration the
   generated H1 and H3 modules and the regeneration samples refer to, the fully elaborated type is identical
   before and after (compare `#check`/`#print` output or exported declarations at `61f1093` and now); build
   `RegenSamples.H1Consumer` and `RegenSamples.H3Consumer`.
6. Rebuild from fresh objects everything the edits affect (that is most of the hand-written tree), rerun the
   source/header checks, the strict hand-written Audit, `make_challenge.py --check`, the physical statement
   comparison with its negative control, and the two-input regression (Lean, NanoDa, con-ron). Commit.

Report: append a section "fidelity fix round 2" to `/home/ubuntu/aklt/reports/PAL_FIT/report.md` (first line of
the section `STATUS: ROUND 2 COMPLETE | PARTIAL (reason)`), with: the exact diff summary of the four statement
files (lines removed/added, confirmation that comment-stripped code differs only by the deleted definition), the
interface-identity check, verification results, the list of hand-written files changed since `d132032` that lie
in the old 65-module closure (the orchestrator needs it for the merge with the regeneration clones), and the
package commit hash. Refresh the ORCH-SUMMARY at the end (≤ 20 lines). American English.
