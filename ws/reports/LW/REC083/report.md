STATUS: PROVED

## Files

- `AKLT/W/REC083/Main.lean`
- `/home/ubuntu/aklt/reports/LW/REC083/report.md`

## Exported declaration

- `AKLT.W.REC083.main : AKLT.Blueprint.Rec.RemovalEnvelopeStatement`

The proof constructs an ordinary consistent `U/X` network for the removed set, retaining the original pin assignment. It identifies its pinned and free partition sums with `pinnedSum` and `freeSum` by removing zero-weight `none` spin assignments and reindexing the remaining assignments. It proves the finite protected layer is nonempty for nonempty finite `G`, obtains finite endpoint distances, classifies the distance-two pair as `B` or `C`, and places the realized response in the bounded defining supremum. The bound used for boundedness follows from nonnegative partition weights and the unit norm bound on the spin support, including the zero-normalizer case.

## Axioms

Output of `#print axioms AKLT.W.REC083.main`:

```text
'AKLT.W.REC083.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC083.Main` — succeeded; module build reported 7.9s (full Lake invocation 12.7s).
- `lake env lean /tmp/rec083_axioms.lean` — succeeded and printed the declaration and axiom list above.

The build emits linter warnings for unused simp arguments/variables and the deprecated `ENat.coe_toNat` alias; they do not affect compilation or the proof.

## Open issues

None.

## ORCH-SUMMARY

Delivered `AKLT.W.REC083.main` with the exact requested type in `AKLT/W/REC083/Main.lean`.
The theorem builds successfully with `lake build AKLT.W.REC083.Main`.
Axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
The removal realization preserves original pins and adds no factors at removed sites.
The partition identities use a finite reindexing that discards zero-weight `none` assignments.
The defining response supremum is bounded by 2 using the support norm estimate, including zero normalizers.
No residual statements or deviations remain.
Only non-blocking linter/deprecation warnings remain.
