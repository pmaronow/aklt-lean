STATUS: PROVED FROM DEPS

## Files

- `AKLT/W/H3M017/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3M017/report.md`

## Exported declaration

`AKLT.W.H3M017.main : AKLT.Blueprint.H3.ClosedTrailStepGeometryStatement`

The proof obtains the vertex recurrence from `AKLT.Cert.H2.vertex_succ`. It extracts centre avoidance at indices `i.val` and `i.val + 1`, and target avoidance at `i.val`, using `i.isLt` for the required bounds.

## Axioms

Output of `#print axioms AKLT.W.H3M017.main`:

```text
'AKLT.W.H3M017.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `lake build AKLT.W.H3M017.Main`

Result: successful. Lake reported the target built in 3.6 seconds; total command time was 9.374 seconds (`real`).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3M017.main` with the exact requested type in `AKLT/W/H3M017/Main.lean`.
- Proof uses the existing proved recurrence lemma `AKLT.Cert.H2.vertex_succ` and the quantified avoidance clauses of `ClosedTrail`.
- Build succeeded; axiom output contains only `propext`, `Classical.choice`, and `Quot.sound`.
- No open issues or deviations.
