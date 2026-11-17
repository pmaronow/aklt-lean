STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q005/AKLT/W/Q005/Main.lean)

## Exported declarations

Main result:

```lean
theorem AKLT.W.Q005.main : AKLT.Blueprint.Q.SelfRotationStatement
```

Supporting declarations in `AKLT.W.Q005`:

```lean
phi_pos : 0 < goldenRatio
phi_sq : goldenRatio ^ 2 = goldenRatio + 1
radius_pos : 0 < icoRadius
radius_sq : icoRadius ^ 2 = goldenRatio + 2
bound_alt : frameBound = 2 / (101 * (goldenRatio + 2))
dot_coord (u v : Vec3) : dot u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2
rot_one_coords (u : Vec3) :
  frameRotation.mulVec u 0 = (99 / 101) * u 0 - (20 / 101) * u 1 ∧
  frameRotation.mulVec u 1 = (20 / 101) * u 0 + (99 / 101) * u 1 ∧
  frameRotation.mulVec u 2 = u 2
rot_sq_coords (u : Vec3) :
  (frameRotation ^ 2).mulVec u 0 = (9401 / 10201) * u 0 - (3960 / 10201) * u 1 ∧
  (frameRotation ^ 2).mulVec u 1 = (3960 / 10201) * u 0 + (9401 / 10201) * u 1 ∧
  (frameRotation ^ 2).mulVec u 2 = u 2
gap_one (u : Vec3) (hu : normSq u = 1) :
  1 - dot u (frameRotation.mulVec u) = (2 / 101) * (u 0 ^ 2 + u 1 ^ 2)
gap_two (u : Vec3) (hu : normSq u = 1) :
  1 - dot u ((frameRotation ^ 2).mulVec u) = (800 / 10201) * (u 0 ^ 2 + u 1 ^ 2)
planarSq_lower (a : IcoLetter) :
  1 / (goldenRatio + 2) ≤ (icoVector a 0)^2 + (icoVector a 1)^2
gap_factor_one_eq : frameBound = (2 / 101) / (goldenRatio + 2)
gap_factor_two_le :
  2 / (101 * (goldenRatio + 2)) ≤ (800 / 10201) / (goldenRatio + 2)
witnessPlanar :
  (icoVector (0, 0, 0) 0)^2 + (icoVector (0, 0, 0) 1)^2 = 1 / (goldenRatio + 2)
ico_norm (a : IcoLetter) : normSq (icoVector a) = 1
```

The coordinate statements for `rot_one_coords` and `rot_sq_coords` are written explicitly in the source file. The proof expands the two matrix powers, uses unit normalization of each ico label, applies the planar-coordinate lower bound, and verifies the attained label equality.

## Axioms

`#print axioms` was run on every exported declaration listed above and on `main`. Each reported:

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `lake build AKLT.W.Q005.Main`

Result: success, 8953/8953 jobs. Final build wall time: 17.803 seconds (Lean module compilation: 9.5 seconds).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q005.main` with the required exact type.
- Added only `AKLT/W/Q005/Main.lean`; no existing project files were edited.
- The theorem and all helper declarations compile; build command and timing are recorded above.
- `#print axioms` for all exported declarations reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No open proof obligations or deviations remain.
