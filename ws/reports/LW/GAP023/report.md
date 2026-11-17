STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_GAP023/AKLT/W/GAP023/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP023/report.md`

Only the assigned new Lean file was added in the worktree.

## Exported declaration

- `AKLT.W.GAP023.main : AKLT.Blueprint.Gap.ReversibleEigenvalueGapStatement`

The proof conjugates the reversible kernel by `diag(sqrt p)`, obtains the real symmetric gap operator, and uses its finite dimensional spectral theorem. The eigenvalue hypothesis bounds every positive gap eigenvalue; the same hypothesis shows that the zero eigenspace consists only of constants. The resulting quadratic form estimate is transported back through the weighted coordinates, then applied to the centered complex function.

## Axioms

`#print axioms AKLT.W.GAP023.main`:

```text
'AKLT.W.GAP023.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the allowed Lean axioms. No forbidden proof escapes were found in the delivered directory.

## Build

- Command: `lake build AKLT.W.GAP023.Main`
- Result: success; module build reported 6.0 s (12.1 s total command time).
- A standalone `lake env lean /tmp/gap023_axioms.lean` check confirmed the exported theorem's axiom list.

The build emitted only linter warnings about unused section variables, unused simp arguments, and the deprecated `push_neg` tactic; there were no proof errors.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/GAP023/Main.lean` with `AKLT.W.GAP023.main` at the exact requested type.
- The closed leaf is proved using detailed-balance conjugation, finite dimensional Hermitian diagonalization, and centered complex coordinates.
- `lake build AKLT.W.GAP023.Main` succeeds.
- Axiom output: `[propext, Classical.choice, Quot.sound]`, all allowed.
- No residual statements or known limitations remain.
