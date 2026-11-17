STATUS: PROVED

## Files

- `AKLT/W/H3M006/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3M006/report.md`

## Exported declaration

- `AKLT.W.H3M006.main : AKLT.Blueprint.H3.LongOrderingMultiplierStatement`

The proof partitions `finRange n` into first-visit straight and turning filters. It proves
the resulting concatenation is nodup and has the exact non-revisit support. For a member of
either filter, the prefix through that member is characterized by the earlier indices in
that filter; the ordered-list products then match the corresponding finite products in
`longMultiplier`.

## Axioms

```
'AKLT.W.H3M006.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake env lean AKLT/W/H3M006/Main.lean` — succeeded (about 7.1 s).
- `lake build AKLT.W.H3M006.Main` — succeeded (11.692 s wall time; Lean reported 6.1 s for the module).
- Axiom check: `lake env lean --stdin` with `import AKLT.W.H3M006.Main` and `#print axioms AKLT.W.H3M006.main`.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3M006.main` with the exact requested type.
- Proof and Lake target compile successfully.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No statement or existing project files were changed.
- Open declarations: none.
- Limitations or deviations: none.
- Orchestrator action required: none.
