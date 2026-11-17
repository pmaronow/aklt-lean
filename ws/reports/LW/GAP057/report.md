STATUS: PROVED

## Files

- `AKLT/W/GAP057/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP057/report.md`

## Exported declaration

`AKLT.W.GAP057.main : AKLT.Blueprint.Gap.FarBoundaryEqualityStatement`

## Proof summary

The proof applies the range-one clause of `RegularSpec` to the square. Since the changed site is exterior, its distance to every point of the square is at least one, so its set distance is at least one. The hypothesis that this distance is not one therefore rules out the changed site itself in the range-one condition. Every other exterior site agrees between the two assignments, yielding equality of the full laws.

## Axioms

Output of `#print axioms AKLT.W.GAP057.main`:

```text
'AKLT.W.GAP057.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.GAP057.Main`
- Result: successful; target module built in 3.6 seconds (Lake reported 8956 jobs total, with dependencies already built).

## Open issues

None.

## ORCH-SUMMARY

- Delivered the proof as `AKLT.W.GAP057.main` in `AKLT/W/GAP057/Main.lean`.
- It proves the frozen `FarBoundaryEqualityStatement` from its `RegularSpec` range-one condition.
- The target module builds successfully.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, deviations, or open issues.
