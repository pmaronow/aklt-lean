Orchestrator message — closing phase: make your certificate statements unconditional. Your production is complete
and accepted, and every one of your open leaf Props now has a merged proof on `main`
(`/home/ubuntu/aklt/repo`, branch `main`): the theorem for leaf number NNN of your `leaves-open.json` (1-based, in
file order) is `AKLT.W.<PART>NNN.main` in module `AKLT.W.<PART>NNN.Main`, where <PART> is `H1C` for the H1 lane
and `H3C` for the H3 lane; the exact map (key → statement) is in `/home/ubuntu/aklt/state/lw/leaves.json`
(fields `node`, `module`, `state` = merged). The final assembly of the project is
`AKLT.Final.main_of_certificates` (module `AKLT.Final.Conditional` on `main`), which needs proofs of
`AKLT.Blueprint.Top.H1FiniteDataStatementV2`, `AKLT.Blueprint.Top.CertificateStatement` (H1 lane) and
`AKLT.Blueprint.Top.Automaton10StatementV2`, `AKLT.Blueprint.Top.StationaryCheckStatementV2` (H3 lane).

Task: deliver named, kernel-checked, hypothesis-free proofs of YOUR TWO statements, of exactly those types as
they stand on `main`, by composing your generated assemblies (retained oleans), your hand-written assemblies and
the merged leaf theorems. Work in the fresh worktree `/home/ubuntu/aklt/wt/CERT_H1/_close_main` (a checkout of current `main`,
built for the ordinary `AKLT` library; you have write access to it and to your report directory; your old
production worktree stays as it is — attach its generated library by path/olean reuse as your merge notes
describe, without re-running the numerical production; if a statement or interface drifted between your
production base and `main`, repair the hand-written bridge, not the statements). Put the hand-written closing
module(s) under `CertData/H1/Close/` in the opt-in certificate library (not in the default `AKLT` target).
Verify: exact types by `example`, `#print axioms` (only propext, Classical.choice, Quot.sound), no `sorry`, and
that the proofs are closed (no leaf or certificate hypothesis left). Report the fully qualified names of the two
proofs and their modules, the exact build command from a state where your generated oleans are attached, time and
peak memory of that build, and anything that prevents a clean re-build from sources (and what that would cost).
If a leaf proof does not fit your assembly (type mismatch), report the exact mismatch instead of working around
it. Append a section "closing phase" to `report.md` (first line `STATUS: …`), ORCH-SUMMARY ≤ 15 lines.
