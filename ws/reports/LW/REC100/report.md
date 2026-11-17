STATUS: PROVED

# REC100 — prove one blueprint leaf

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC100/AKLT/W/REC100/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/REC100/report.md)

## Exported declarations

- `AKLT.W.REC100.main : AKLT.Blueprint.Rec.ShortKernelOrderingStatementV2`
- `AKLT.W.REC100.shortScore w i : WithTop ℚ`: zero reward maps to `⊤`; otherwise this is the rational short-order score.
- `AKLT.W.REC100.shortKey w i : WithTop ℚ × ℕ`: the score paired with the path index.
- `AKLT.W.REC100.shortKeyLE w i j`: lexicographic comparison of score and path index.
- `AKLT.W.REC100.shortKeyLEBool w i j`: the Boolean decision for `shortKeyLE`.
- `AKLT.W.REC100.shortOrderLE_eq_decide_shortKeyLE`: identifies the frozen comparator with that lexicographic Boolean comparison.
- `AKLT.W.REC100.shortKeyLE_trans` and `shortKeyLE_total`: transitivity and totality of the lexicographic relation.
- `AKLT.W.REC100.shortOrderLE_trans` and `shortOrderLE_total`: corresponding facts for the frozen Boolean comparator.

The short branch of `kernelOrdering` reduces to the specified `mergeSort`. Pairwise correctness follows from the merge-sort theorem using the comparator facts above. The proof is general in the word and does not need the `ClosedTrail` hypothesis.

## Axiom audit

`#print axioms AKLT.W.REC100.main`:

```text
'AKLT.W.REC100.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC100.Main` — passed; Lean reported the module build in 5.2 s (wall time 8.8 s).
- The build also emitted the axiom audit above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC100.main` with the exact requested type in `AKLT/W/REC100/Main.lean`.
- Proved short-order comparator transitivity and totality by identifying it with lexicographic order on an extended rational score and path index.
- Proved the requested pairwise merge-sort correctness and cutoff-branch equality.
- Axiom dependencies: `propext`, `Classical.choice`, `Quot.sound`.
- Build passed with `lake build AKLT.W.REC100.Main`.
- Open issues: none; no orchestrator decision is needed.
