STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC037/AKLT/W/REC037/Main.lean): requested public theorem.
- [Contract.lean](/home/ubuntu/aklt/wt/LW_REC037/AKLT/W/REC037/Contract.lean): first through fourth moment contractions and the finite `k = 0,1,2,3` proof.
- [Moments.lean](/home/ubuntu/aklt/wt/LW_REC037/AKLT/W/REC037/Moments.lean): direct finite-sum tensor identities for the icosahedron and local U/D functional reductions.

## Exported declarations

The requested declaration is exactly:

```lean
theorem AKLT.W.REC037.main : AKLT.Blueprint.Rec.UStepMomentStatement
```

Its proof is `uStepMoment` in `Contract.lean`. The statement's four cases are proved by expanding the U functional through degree four and evaluating the remaining D products (empty, one factor, or two factors).

The supporting exported declarations are finite-sum and contraction helpers in `Contract.lean` (`moment_sum`, `moment_smul`, `sum_diag2`, `sum_diag_pair`, `sum_pairing_ikjl`, `sum_pairing_iljk`, `moment_add`, `dot_comm`, `dot_two_expand`); first through fourth dot-product moments (`moment_dot_one`, `moment_dot_two`, `moment_dot_three`, `moment_dot_four`, `moment_mixed_two`, `moment_mixed_three`, `moment_mixed_four`, `moment_left_dot`, `moment_left_dot_two`); U contractions (`siteU_dot`, `siteU_dot_two`, `siteU_dot_three`, `siteU_dot_four`, `siteU_zero_factors`, `siteU_one_factor`, `siteU_two_factors`, `siteU_three_factors`); D contractions (`siteD_dot`, `siteD_const`, `siteD_one_factor`, `siteD_product_two`); and `uStepMoment`, whose type equals the requested statement.

`Moments.lean` exports `moment_first_coord`, `moment_second_coord`, `moment_second_tensor`, `moment_third_tensor`, `moment_four_tensor`, `siteU_eq_moment`, `siteD_eq_moment`, and `moment_const`. Their exact Lean signatures are in the linked source file.

## Axioms

`#print axioms AKLT.W.REC037.main`:

```text
'AKLT.W.REC037.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC037.Main` — succeeded; 10.2 s in the final invocation (supporting modules were already built).
- Initial helper build compiled `Moments.lean` in 62 s; `Contract.lean` then compiled in 4.4 s.
- A separate `lake env lean /tmp/REC037AxiomAudit.lean` printed the axiom list above and succeeded in 6.5 s.

## Open issues

None. No residual propositions or statement deviations remain.

## ORCH-SUMMARY

- PROVED `AKLT.Blueprint.Rec.UStepMomentStatement` as `AKLT.W.REC037.main`.
- Deliverables: `AKLT/W/REC037/Main.lean`, `Contract.lean`, and `Moments.lean`.
- Proof uses explicit finite icosahedron moment tensors through degree four, contracts dot products, and checks all `k ≤ 3` cases.
- `lake build AKLT.W.REC037.Main` succeeded.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
- Open issues: none; no residuals or deviations.
