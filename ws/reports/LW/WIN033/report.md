STATUS: PROVED

## Files

- `AKLT/W/WIN033/Main.lean`

## Exported declaration

- `AKLT.W.WIN033.main : AKLT.Blueprint.Win.RadialPathsStatement`

The proof unfolds taper/core membership and inducts on the natural radial offset. If the radius is above the shell radius, every maximal coordinate moves one unit inward; if it is below, one maximal coordinate moves outward. The offset drops by one in either case. Each step is star-adjacent, changes square depth by at most one, and preserves the condition `offset + 32 ≤ squareDepth`. At offset zero, the current site lies in `core`; the finite steps compose to the required `JoinedIn` path. The proof uses only `i ≥ 2` from `CutSetup` (to establish nonnegative shell radius) and nonnegativity of the square-root shell spacing; its other setup conditions are unused.

All geometric and arithmetic support declarations in the file are `private`.

## Axioms

`#print axioms AKLT.W.WIN033.main`:

```text
'AKLT.W.WIN033.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.WIN033.Main`
- Result: successful (`8955/8955` jobs; module replayed in 4.45 s).
- Lean emitted only deprecated `if_pos`/`if_neg` and unused simplifier/tactic warnings; there were no errors.
- `lake env lean /tmp/WIN033Axioms.lean` confirmed the theorem type and axiom list above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN033/Main.lean` and proved `AKLT.W.WIN033.main` at the exact requested type.
- Proof follows the radial-offset induction; the core endpoint is the final radius-`k` site.
- Build succeeded with `lake build AKLT.W.WIN033.Main` (4.45 s, cached replay).
- Axioms are `[propext, Classical.choice, Quot.sound]`.
- Only compiler warnings are deprecated conditional simp lemmas and unused tactic/simp arguments.
- No residual statements, deviations, or open issues.
