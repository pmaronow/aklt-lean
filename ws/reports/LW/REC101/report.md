STATUS: PROVED

## Files

- [`AKLT/W/REC101/Main.lean`](/home/ubuntu/aklt/wt/LW_REC101/AKLT/W/REC101/Main.lean)

## Exported declaration

`AKLT.W.REC101.main : AKLT.Blueprint.Rec.LongKernelOrderingStatementV2`

Expanded statement:

```lean
∀ n X w, AKLT.Defs.ClosedTrail X w → 12 < n →
  AKLT.Defs.kernelOrdering w = AKLT.Defs.longOrdering w ∧
  ((AKLT.Defs.firstVisitList w).filter
    (AKLT.Defs.wordStraight AKLT.Defs.kernelIncoming w)).Pairwise
      (fun i j => i.val < j.val) ∧
  ((AKLT.Defs.firstVisitList w).filter
    (fun i => !(AKLT.Defs.wordStraight AKLT.Defs.kernelIncoming w i))).Pairwise
      (fun i j => i.val < j.val)
```

The long branch of `kernelOrdering` unfolds to `longOrdering`. The ordering clauses follow because `finRange` is strictly increasing, and `List.Pairwise.filter` preserves that relation through both filters. `ClosedTrail` is not needed for this statement.

## Axioms

Output of `#print axioms AKLT.W.REC101.main`:

```text
'AKLT.W.REC101.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC101.Main` — succeeded; Lake reported 5.4 s for the final build.
- `lake env lean AKLT/W/REC101/Axioms.lean` — succeeded and printed the axiom output above (the temporary check file was removed afterward).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC101.main` with the requested exact name and type in `AKLT/W/REC101/Main.lean`.
- Proof uses the increasing order of `List.finRange` and pairwise preservation under filtering; the closed-trail hypothesis is unused.
- Final build succeeded with `lake build AKLT.W.REC101.Main` (5.4 s).
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- No open declarations or residual statements; no deviations requiring orchestrator action.
