STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP033/AKLT/W/GAP033/Main.lean)

## Exported declaration

`AKLT.W.GAP033.main : AKLT.Blueprint.Gap.PullbackColourStatement`

The proof reduces plane adjacency to one of the torus's frozen positive bonds, in forward or reverse orientation, then applies the assumed proper torus colouring.

## Axioms

`#print axioms AKLT.W.GAP033.main` reports:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.GAP033.Main`
- Result: successful; leaf module compiled in 4.1 s (build command completed in 9.4 s).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP033.main` with the requested frozen statement type.
- Proof and report are in the assigned directories; no existing files were changed.
- Build passed with only permitted axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No open issues or deviations.
