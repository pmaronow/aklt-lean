STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_WIN008/AKLT/W/WIN008/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN008/report.md`

## Exported declaration

`AKLT.W.WIN008.main : AKLT.Blueprint.Win.ShellInclusionStatement`

The proof expands the `shell` and `farVolume` filters. For a shell point, its integer radius is `floor(i * shellSpacing u)`. The floor bound gives `i * s - 1 < floor(i * s)`, and `s ≥ 2` implies `(i - 1) * s < i * s - 1`. Thus the point satisfies the far-volume filter.

## Axioms

`#print axioms AKLT.W.WIN008.main`:

```text
'AKLT.W.WIN008.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `export PATH="$HOME/.elan/bin:$PATH"; lake build AKLT.W.WIN008.Main`
- Result: successful; module target reported 5.8 s (13.5 s total command wall time).
- A separate `lake env lean /tmp/WIN008Axioms.lean` invocation printed the axiom result above (7.0 s).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN008.main` with the requested type in `AKLT/W/WIN008/Main.lean`.
- Proof follows from the shell membership radius and `shellSpacing u ≥ 2`.
- Module build succeeded; axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No deviations or open issues.
