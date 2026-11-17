Orchestrator message — round 2. All 416 leaf hypotheses of `AKLT.Final.mainV2_of_open` now have merged proofs
(`python3 AKLT/Final/gen_final.py --check-only` on current `main` reports exactly the four certificate statements
missing: `H1FiniteDataStatementV2`, `CertificateStatement`, `Automaton10StatementV2`, `StationaryCheckStatementV2`).
The orchestrator has merged current `main` into your worktree. Do:
1. Add a mode `--conditional` to `gen_final.py` that writes `AKLT/Final/Conditional.lean` containing ONE theorem
   `AKLT.Final.main_of_certificates : <the four certificate statements, in the order of mainV2_of_open> →
   AKLT.Challenge.MainStatementV2`, obtained by applying `mainV2_of_open` to the 416 leaf proofs
   (`AKLT.W.<KEY>.main`) and the four hypotheses. Generate it, build it (`lake build AKLT.Final.Conditional`),
   and verify: exact type by an `example`, `#print axioms` = propext, Classical.choice, Quot.sound only, and that
   no certificate statement other than those four appears as a hypothesis.
2. Keep `Main.lean` generation as is (it will be used when the four certificate proofs exist); make
   `--proofs` accept the four certificate proof terms by name so that the final step is one command; document
   the exact command in your report.
3. Leaf-proof recheck: the generator said "Source-found proofs have not been rechecked by this run" — make the
   conditional build itself the recheck (it is: the term only type-checks if every leaf proof has exactly its
   statement's type); state this in the report, with the count of distinct leaf theorems the term uses and the
   list of hypotheses of `mainV2_of_open` that the assembly does not use (for information only).
Only files under `AKLT/Final/`. Report: append a section "round 2" to
`/home/ubuntu/aklt/reports/ARCH_FINAL/report.md` (first line `STATUS: COMPLETE | PARTIAL (reason)`).
