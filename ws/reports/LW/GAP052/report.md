STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_GAP052/AKLT/W/GAP052/Main.lean`

## Exported declaration

`AKLT.W.GAP052.main : AKLT.Blueprint.Gap.ScaleExistenceStatement`

The proof chooses `n` by the Archimedean property above a real maximum containing the four thresholds (using `C / d^20` for the final inequality). It then uses `n ≤ n^2`, `n ≤ n^8`, and `n ≤ n^12` for the required power bounds.

## Axioms

Output of `#print axioms AKLT.W.GAP052.main`:

```text
'AKLT.W.GAP052.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are within the allowed axiom set.

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.GAP052.Main` — succeeded; Lean build action 3.7 s (command elapsed 8.3 s).
- `PATH="$HOME/.elan/bin:$PATH" lake env lean /tmp/GAP052Axioms.lean` — succeeded; 4.2 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP052.main` with the exact requested type in `AKLT/W/GAP052/Main.lean`.
- The leaf is proved directly by an Archimedean choice above four thresholds.
- Build succeeded with `lake build AKLT.W.GAP052.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements, limitations, or deviations.
