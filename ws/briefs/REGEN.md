# REGEN_<FAM> — regenerate and rebuild the <FAM> certificate library as module-system Lean (author-directed)

**Context.** A complete Lean 4 formalization of a spectral-gap theorem is being released with every Lean file in
Lean's module system. The hand-written development has been ported: the release root is your working directory
`/home/ubuntu/aklt/rel/<FAM>` (a clone of the ported package, already built for everything hand-written; Lean
4.35.0-rc2 + Mathlib; `.lake/packages` is a symlink to prebuilt dependencies — never run `lake update`, never
rebuild Mathlib). Read first, in this directory: `REGEN-INTERFACE.md` (what generated modules must import, which
declarations they reference, the header and visibility attributes each generated file needs, and the sample
generated modules under `RegenSamples/`), `README.md`, `PORT-CHANGES.md`, and the Lake layout.

The certificate for the input (<FAM>) is a family of GENERATED Lean modules checked by Lean's kernel
(`decide +kernel`-style checks of finite integer data) plus hand-written assemblies. It was produced once already,
in the legacy (non-module) form, by the certificate lane: report `/home/ubuntu/aklt/reports/CERT_<FAM>/report.md`
(generators, runner commands, module families, measured costs, memory caps, how sources were compacted, how the
closed statements were assembled: sections on phase 3 and the closing phase; for H3 also
`/home/ubuntu/aklt/reports/CLOSE_H3/report.md`), legacy production worktree `/home/ubuntu/aklt/wt/CERT_<FAM>`
(READ-ONLY), legacy attached tree `/home/ubuntu/aklt/wt/CLOSE_H3` (READ-ONLY: generated sources that still exist,
compiled legacy modules, closing modules, receipts), input data `/home/ubuntu/aklt/data/h1` and
`/home/ubuntu/aklt/compfeas/data`. A module-system file cannot import a legacy file, so the legacy compiled modules
are useless here: everything must be regenerated in module form and re-checked by the kernel.

**Deliver.**
1. GENERATORS: adapt the family's generators (they are in this tree under the family's `tools`/production
   scripts) so that every generated file is a module-system file that compiles against the ported hand-written
   kernels and is visible to the hand-written assemblies exactly as the interface note says. Where legacy
   generated sources still exist, you may transform them mechanically instead of re-exporting, provided the
   result is byte-identical to what the adapted generator emits for the same input (check on a sample); where
   sources were deleted after the legacy build, regenerate them from the input data. Generated files: `module`
   header, at most 10,000 physical lines each, no forbidden constructs (`sorry`, `native_decide`, `unsafe`,
   `implemented_by`, `extern`, new axioms), comments in American English. The arithmetic content of every check
   must be unchanged (same data, same checker definitions).
2. PILOT first: one small and one of the largest modules of each generated kind, built in fresh processes,
   compared with the legacy cost for the same module; fix anything that makes kernel reduction slower or stuck
   under the module system (definitions not exposed, etc. — report such findings to be fixed in the hand-written
   kernel: you may edit hand-written files of this family's checker in your tree if needed, listing every such
   edit in `REGEN-CHANGES.md` with the reason).
3. PRODUCTION: regenerate and build the ENTIRE family with kernel checking, from clean (no legacy oleans), with
   your runner (resumable, per-module logs and receipts: exit status, time, peak memory, source hash, axioms of
   every exported check theorem — only propext, Classical.choice, Quot.sound allowed). Resource budget for this
   run: at most <PROCS> Lean processes and <RAM> GB RAM in total (another family's production runs beside you;
   check `free -g` and keep 40 GB free; keep free disk above 100 GB; compress or delete literal sources only
   AFTER recording their hashes, and say exactly which sources remain on disk and how to regenerate the rest).
4. ASSEMBLE: build the family's hand-written assemblies that import generated modules, and the family's closing
   module giving the hypothesis-free proofs of the family's top-level certificate statements (the same statements
   and names as in the legacy closing module: for H1 `CertData.H1.Close.finiteData`, `CertData.H1.Close.certificate`;
   for H3 `CertData.H3.Close.automaton10`, `CertData.H3.Close.stationaryCheck`), using the ported leaf theorems
   `AKLT.W.<KEY>.main` already in the tree. Verify exact types by `example`, `#print axioms`, closedness.
5. HAND-OFF: `REGEN-<FAM>.md` in the tree: exact commands to regenerate and rebuild from the input data, the
   module counts, total CPU time, peak memory, where the generated sources and compiled modules are on disk
   (they are not tracked in git), a SHA-256 manifest of every generated source and compiled module, and what the
   final assembly (a module importing both families' closing modules) needs from you.
Report `/home/ubuntu/aklt/reports/REGEN_<FAM>/report.md`, first line
`STATUS: COMPLETE | PARTIAL (reason)`; write pilot results as soon as you have them and progress counts during
production; end with an ORCH-SUMMARY (≤ 20 lines). Commit your hand-written changes in this clone's git
repository (generated files untracked). This task was issued by the orchestrator (Fable); do it yourself.
