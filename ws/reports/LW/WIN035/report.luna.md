STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN035/AKLT/W/WIN035/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/WIN035/report.md)

## Delivered declarations

`AKLT.W.WIN035.main` with the requested exact type is **not proved**.
The file provides a conditional assembly theorem and leaves three explicit
region-specific escape statements as residuals:

- `AKLT.W.WIN035.Residual_outerEscape`: for an in-square point with
  `k ≤ ρ` and radial offset greater than `s/12`, produce an adjacent path in
  the taper complement to outside the square.
- `AKLT.W.WIN035.Residual_innerEscape`: the corresponding path when
  `ρ < k` and the radial offset is greater than `s/12`.
- `AKLT.W.WIN035.Residual_lowClearanceEscape`: the corresponding path when
  the radial offset is at most `s/12` and square depth is below offset plus 32.

`AKLT.W.WIN035.main_of_residuals` proves
`AKLT.Blueprint.Win.ComplementEscapeStatement` from those three residuals. Its
case split follows directly from the definition of `taper`; points already
outside the square use a reflexive path. The generic `joined_to_point` helper
constructs a path by a nearest-neighbour step toward a target and induction on
Manhattan distance.

The exact residual and assembly statements are:

```lean
AKLT.W.WIN035.Residual_outerEscape : Prop :=
  ∀ a y u i, CutSetup a y u i → ∀ z, z ∈ square a u →
    shellRadius u i ≤ (supDist z y : ℤ) →
    shellSpacing u / 12 < (radialOffset y u i z : ℝ) →
    ∃ w, w ∉ square a u ∧
      JoinedIn Adjacent {v | v ∉ taper a y u i} z w

AKLT.W.WIN035.Residual_innerEscape : Prop :=
  ∀ a y u i, CutSetup a y u i → ∀ z, z ∈ square a u →
    (supDist z y : ℤ) < shellRadius u i →
    shellSpacing u / 12 < (radialOffset y u i z : ℝ) →
    ∃ w, w ∉ square a u ∧
      JoinedIn Adjacent {v | v ∉ taper a y u i} z w

AKLT.W.WIN035.Residual_lowClearanceEscape : Prop :=
  ∀ a y u i, CutSetup a y u i → ∀ z, z ∈ square a u →
    (radialOffset y u i z : ℝ) ≤ shellSpacing u / 12 →
    squareDepth a u z < (radialOffset y u i z : ℤ) + 32 →
    ∃ w, w ∉ square a u ∧
      JoinedIn Adjacent {v | v ∉ taper a y u i} z w

AKLT.W.WIN035.main_of_residuals
  (hOuter : Residual_outerEscape)
  (hInner : Residual_innerEscape)
  (hLow : Residual_lowClearanceEscape) :
  AKLT.Blueprint.Win.ComplementEscapeStatement
```

Other proved helper statements are `joined_refl`, `joined_step`,
`stepToward_adj`, `stepToward_dist_lt`, and
`joined_to_point`; they are available with their full signatures in
[Main.lean](/home/ubuntu/aklt/wt/LW_WIN035/AKLT/W/WIN035/Main.lean).

The residuals are closed propositions and each is strictly restricted to one
of the three in-square regions. They isolate the remaining proof: establish the
appropriate decreasing coordinate move in each region, prove it preserves the
taper complement, and show it terminates outside the square. In particular,
the formal shell scale bounds and the one-step radial/depth inequalities have
not been completed here.

## Axiom audit

Output from `#print axioms`:

```text
'AKLT.W.WIN035.joined_refl' does not depend on any axioms
'AKLT.W.WIN035.joined_step' does not depend on any axioms
'AKLT.W.WIN035.stepToward_adj' depends on [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN035.stepToward_dist_lt' depends on [propext, Quot.sound]
'AKLT.W.WIN035.joined_to_point' depends on [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN035.main_of_residuals' depends on [propext, Classical.choice, Quot.sound]
```

These are allowed kernel axioms. No forbidden proof escape hatches are used.

## Build

Command: `lake build AKLT.W.WIN035.Main`

Result: successful; module build reported 4.2 seconds (8.91 seconds wall time
including Lake startup). Lean emitted only deprecation warnings for `if_pos` /
`if_neg` and an unused binder warning on `joined_to_point`.

## Open issues

- Prove `AKLT.W.WIN035.Residual_outerEscape`.
- Prove `AKLT.W.WIN035.Residual_innerEscape`.
- Prove `AKLT.W.WIN035.Residual_lowClearanceEscape`.
- Then export `AKLT.W.WIN035.main` at the exact requested type.

## ORCH-SUMMARY

- Delivered a compiled partial module with a conditional assembly theorem.
- The exact theorem `AKLT.W.WIN035.main` is not present.
- The three open residual declarations are `Residual_outerEscape`, `Residual_innerEscape`, and `Residual_lowClearanceEscape` in `AKLT.W.WIN035`.
- `main_of_residuals` reduces the original statement to those three case-specific path constructions.
- Generic Manhattan path induction and adjacency helpers are proved.
- Build succeeded with `lake build AKLT.W.WIN035.Main`.
- No edits were made to frozen definitions or existing project files.
- Orchestrator follow-up: discharge the three residual paths and add the exact exported theorem.
