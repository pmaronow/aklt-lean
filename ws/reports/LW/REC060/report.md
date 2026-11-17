STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC060/AKLT/W/REC060/Main.lean)

## Exported declarations

- `AKLT.W.REC060.firstVisitList_nodup {n} (w : AKLT.Defs.DirectionWord n) : (AKLT.Defs.firstVisitList w).Nodup`
- `AKLT.W.REC060.main : AKLT.Blueprint.Rec.KernelOrderingStatement`

The proof establishes the requested statement for every direction word, as its definition requires. It obtains `Nodup` by filtering `List.finRange`; the short ordering preserves permutation and `Nodup` through `mergeSort`; and the long ordering is a partition by the straight-step Boolean predicate, proved permutation-equivalent to the original list. The proof does not require the `ClosedTrail` premise used to describe the orderings in the paper: the frozen Lean statement quantifies over all words and the ordering definitions give the same permutation property for all of them.

## Axioms

`#print axioms AKLT.W.REC060.main`:

```text
'AKLT.W.REC060.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC060.Main`

Result: successful; module compilation reported 4.6 seconds (Lake completed 8958 jobs).

Axiom inspection command: `PATH="$HOME/.elan/bin:$PATH" lake env lean /tmp/REC060_Axioms.lean`.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC060/Main.lean` and the exact theorem `AKLT.W.REC060.main`.
- Proved permutation and `Nodup` for the short and long ordering branches.
- Build succeeded; theorem uses only permitted axioms `[propext, Classical.choice, Quot.sound]`.
- No deviations or open issues.
- The frozen theorem covers all `DirectionWord`s; no `ClosedTrail` premise is present in its type.
