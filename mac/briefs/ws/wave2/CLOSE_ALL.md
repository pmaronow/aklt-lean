Orchestrator message — final closing step. Your two H3′ proofs are accepted. The H1 lane has delivered the other
two, in its own fresh worktree `/home/ubuntu/aklt/wt/CERT_H1/_close_main` (READ-ONLY for you; same base commit
63d176a): module `CertData.H1.Close.Main` with `CertData.H1.Close.finiteData :
AKLT.Blueprint.Top.H1FiniteDataStatementV2` and `CertData.H1.Close.certificate :
AKLT.Blueprint.Top.CertificateStatement`; its report section "closing phase" in
`/home/ubuntu/aklt/reports/CERT_H1/report.md` describes how the generated H1 library (`CertDataH1`, retained
oleans in the H1 lane's worktrees) is attached. Do, in YOUR worktree `/home/ubuntu/aklt/wt/CLOSE_H3`:
1. Attach the H1 closing module and the generated H1 library it needs (copy or hard-link sources/oleans exactly as
   you did for H3; verify hashes against the H1 lane's receipts; do not re-run any numerical production; keep the
   lakefile's default `AKLT` target unchanged, add the H1 opt-in library target as the H1 lane defines it).
2. Write `CertData/Close/All.lean` (opt-in library) with exactly these named, hypothesis-free theorems:
   - `CertData.Close.h1 : AKLT.Blueprint.Top.H1Statement`
   - `CertData.Close.h2 : AKLT.Blueprint.Top.H2Statement`
   - `CertData.Close.h3 : AKLT.Blueprint.Top.H3Statement`
   - `CertData.Close.main : AKLT.Challenge.MainStatementV2`
     (by `AKLT.Final.main_of_certificates` applied to the four closed certificate proofs)
   obtaining h1/h3 from the existing assemblies that derive the analytic inputs from the certificate statements
   and the merged leaves (find them in `AKLT/Blueprint/H1`, `AKLT/Blueprint/H3`, `AKLT/Blueprint/Top`), and h2 from
   `AKLT/Cert/H2`. If no existing assembly yields `H1Statement` / `H3Statement` in exactly that form, report the
   closest proved statements and the exact gap instead of improvising.
3. Verify: exact types by `example`; `#print axioms` for the four (only propext, Classical.choice, Quot.sound);
   forbidden-token scan of every hand-written source in the import closure that is not on `main`; and write a
   receipt `/home/ubuntu/aklt/reports/CLOSE_H3/final-receipt.json`: base commit, the four theorem names and types
   as printed by Lean, axioms, module counts and SHA-256 manifests of the attached generated libraries (H1 and
   H3), build command, wall time, peak memory, Lean/Mathlib versions.
Append a section "final closing" to `report.md` (first line `STATUS: …`), ORCH-SUMMARY ≤ 15 lines.
