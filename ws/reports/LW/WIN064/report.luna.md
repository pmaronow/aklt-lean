STATUS: PARTIAL

## Files

- `AKLT/W/WIN064/Main.lean` — proved the local incidence bound and added two explicit residual propositions plus a conditional assembly theorem. The required exported theorem `AKLT.W.WIN064.main` is not yet present.

## Exported declarations

- `AKLT.W.WIN064.incidence_bound`:
  `∀ G D : Finset Plane, D ⊆ G → ∀ z, z ∈ D → ((internalBonds D).filter (fun e => e.1 = z ∨ e.2 = z)).card + ((originalLegs G).filter (fun e => e.1 = z)).card ≤ 4`.
  This embeds incident internal edges and surviving original legs into disjoint subsets of the four nearest-neighbor directions.
- `AKLT.W.WIN064.Residual_ComplementPolynomial` asks for a separate-degree-four polynomial representing both the actual frame pinned sum and the reference pinned sum.
- `AKLT.W.WIN064.Residual_ExactQuadratureTransfer` asks for the exact theorem and three-frame moment laws to equate the resulting two finite quadratures.
- `AKLT.W.WIN064.main_of_residuals` proves `ComplementQuadratureStatement` from those two residuals. It is conditional and does not have the requested `main` signature.

## Axioms

`#print axioms AKLT.W.WIN064.incidence_bound`:
`[propext, Classical.choice, Quot.sound]`

`#print axioms AKLT.W.WIN064.main_of_residuals`:
`[propext, Classical.choice, Quot.sound]`

## Build

- `lake env lean AKLT/W/WIN064/Main.lean` — completed successfully.
- `lake build AKLT.W.WIN064.Main` — completed successfully; Lake reported the module build in 4.0 seconds (9.4 seconds wall time for the command).
- The build emitted only deprecated `if_pos`/`if_neg` and unused simp argument warnings.

## Open issues

- Prove `Residual_ComplementPolynomial`: construct the multivariate interaction polynomial and establish its separate degree bound from `incidence_bound`, then connect its evaluations to both partition sums.
- Prove `Residual_ExactQuadratureTransfer`: construct the per-site frame data from `ThreeFramesStatement`, apply `ExactStatement`, and reindex its finite sums to `frameQuadrature` and `referenceQuadrature`.
- Once those residuals are discharged, `main_of_residuals` supplies the target implication. The exact theorem `AKLT.W.WIN064.main : AKLT.Blueprint.Win.ComplementQuadratureStatement` remains open.

## ORCH-SUMMARY

- Delivered `AKLT/W/WIN064/Main.lean` and this report.
- Proved `AKLT.W.WIN064.incidence_bound` with only allowed axioms.
- Added the smaller residual propositions `Residual_ComplementPolynomial` and `Residual_ExactQuadratureTransfer`.
- Added the conditional assembly theorem `main_of_residuals`; the required exact `main` declaration is absent.
- Open: polynomial factor encoding/evaluation; separate-degree proof; exact quadrature sum transfer/reindexing.
- Build command passed: `lake build AKLT.W.WIN064.Main`.
- Limitation: status is PARTIAL; no claim that the frozen leaf statement is proved.
