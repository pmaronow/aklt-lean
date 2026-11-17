STATUS: PARTIAL

## Files

- `/home/ubuntu/aklt/wt/LW_GAP045/AKLT/W/GAP045/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP045/report.md`

## Delivered declarations

- `AKLT.W.GAP045.Residual_unskipped : Prop` — the row-existence obligation restricted to indices `j` with `(j.val + 2 : ℤ) ∉ exceptionalIndices a y u`. It retains the original geometric, energy, consistency, and window hypotheses and the full `RowConditions` conclusion.
- `AKLT.W.GAP045.skipped_row` — for an exceptional index, the point mass at the input pair satisfies `RowConditions`.
- `AKLT.W.GAP045.main_of_residual (hres : Residual_unskipped) : AKLT.Blueprint.Gap.ShellRowStatement` — the original statement follows from the unskipped residual plus the proved identity-row case.

The requested closed declaration `AKLT.W.GAP045.main : AKLT.Blueprint.Gap.ShellRowStatement` is not delivered because `Residual_unskipped` remains unproved. No existing file was modified, and no `sorry`, `admit`, or custom axiom was added.

## Axioms

Lean's `#print axioms` output:

```text
'AKLT.W.GAP045.skipped_row' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.GAP045.main_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the allowed standard axioms.

## Build

Command: `lake build AKLT.W.GAP045.Main`

Result: successful. Measured replay time: 5.56 s (the initial compilation of the new module was 4.0 s).

## Open issue

`Residual_unskipped` is the remaining hard part: construct a coupling for every nonexceptional row with the required conditional full-law marginals, support and predecessor-agreement behavior, and the success lower bound. In particular this requires deriving the conditional window comparison from `SpecWindow`, transporting finite energy to the row conditionals, and proving the finite maximal-coupling/completion/resampling construction. The paper's geometric and probabilistic argument suggests this residual is true; it has not been established here. No counterexample to the original statement was found.

## ORCH-SUMMARY

- Delivered a compiled partial module under `AKLT/W/GAP045/`.
- Proved exceptional rows are identity point masses satisfying `RowConditions`.
- Proved the full row statement from `Residual_unskipped`.
- `Residual_unskipped` is the exact unproved nonexceptional row-existence obligation.
- The requested closed `main` theorem is not present; status is PARTIAL.
- Build: `lake build AKLT.W.GAP045.Main`, successful, 5.56 s replay.
- Axioms for exported theorems: propext, Classical.choice, Quot.sound.
- No counterexample found; no existing files modified.
- Orchestrator: pass on the unskipped coupling construction as the remaining dependency.
