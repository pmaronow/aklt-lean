STATUS: PROVED

## Delivered files

- `AKLT/W/GAP029/Main.lean`

## Exported declaration

- `AKLT.W.GAP029.main : AKLT.Blueprint.Gap.ExteriorBlockCountStatement`

The theorem proves the labeled exterior-block count for every `M ≥ 1` and periods `L,N ≥ 2M+3`. It identifies centers containing a fixed site with offsets in the corresponding square, proves the radius-`M+1` offset map injective from the strict coordinate-difference bounds, and counts the exterior labels as the difference of the larger and inner offset-square cardinalities. The annulus includes corner offsets, and the proof allows equality in either period bound.

## Axiom audit

`#print axioms AKLT.W.GAP029.main`:

```text
'AKLT.W.GAP029.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No forbidden proof placeholders or additional axioms are used.

## Build

Command:

```text
export PATH="$HOME/.elan/bin:$PATH"; lake build AKLT.W.GAP029.Main
```

Result: completed successfully. Lean reported the module build in 5.6 s (shell wall time 11.6 s).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/GAP029/Main.lean` with `AKLT.W.GAP029.main` at the requested exact type.
- The offset annulus count proves the exterior count, including corners and equality `L,N = 2M+3`.
- Axiom audit: `[propext, Classical.choice, Quot.sound]`.
- `lake build AKLT.W.GAP029.Main` succeeds; no open issues or deviations.
