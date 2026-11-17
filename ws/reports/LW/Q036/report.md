STATUS: PROVED

## Files

- `AKLT/W/Q036/Main.lean`
- `/home/ubuntu/aklt/reports/LW/Q036/report.md`

## Exported declaration

`AKLT.W.Q036.main : AKLT.Blueprint.Q.StarEdgeEnumerationStatement`

This proves injectivity of the four `starEdge` indices and the equality between their image and the oriented bonds whose endpoint set contains the selected site. For backward edges, the proof uses the preceding coordinate `x - 1`; the injectivity argument uses `1 ≠ 0` modulo each side length, which holds for all permitted lengths, including period three.

## Axioms

`#print axioms AKLT.W.Q036.main`:

```text
[propext, Classical.choice, Quot.sound]
```

These are allowed axioms. No residual statements or unproved assumptions were introduced.

## Build

Command: `lake build AKLT.W.Q036.Main`

Result: successful. The module build reported 6.0 s; the command completed in about 13.6 s including Lake overhead.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/Q036/Main.lean`.
- Status: PROVED; the target module builds successfully.
- The proof counts each oriented `Bond` once, including on period-three tori.
- Axioms: `propext`, `Classical.choice`, and `Quot.sound` only.
- No helper files, residual statements, or deviations.
- No open issues or decisions for the orchestrator.
