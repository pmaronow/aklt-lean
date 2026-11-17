STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_Q060/AKLT/W/Q060/Main.lean`

## Exported declarations

- `AKLT.W.Q060.main : AKLT.Blueprint.Q.DensityDirichletStatement`
- Helpers in `AKLT.W.Q060`: `weighted_mean_min`, `weighted_complex_mean_min`, `sum_first_fiber`, `fiberCenter`, `fiberDirichlet`, `fiberDirichlet_lower`, `Rest`, `splitAt`, `agreeOutside_iff_split`, and `blockDirichlet_eq_fiber`.

The proof splits each configuration at a fixed site, identifies singleton exterior fibres with fixed first coordinates, and proves the weighted squared-error minimum on each fibre. The pointwise lower density bound is applied to errors centered at the q-conditional mean; p-minimality then yields the factor `m`. Summing the fibre inequalities and physical sites proves the statement. Strict positivity of p and its unit total mass establish that every site alphabet is nonempty.

## Axiom check

`#print axioms` was run on each of the seven exported lemmas, including `AKLT.W.Q060.main`. Each returned:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.Q060.Main` — successful; module built in 7.1 s (12.0 s wall time).
- Lean emitted only style-linter suggestions about local `letI` declarations.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q060.main` with the exact requested type in `AKLT/W/Q060/Main.lean`.
- The requested Lake build succeeds.
- Axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
- No statement changes, extra premises, residual propositions, or deviations.
- No open issues for the orchestrator.
