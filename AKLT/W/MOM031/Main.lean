module
public import AKLT.Blueprint.Mom.NodesExact

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Mom

namespace AKLT.W.MOM031

theorem main : AKLT.Blueprint.Mom.SingleSiteQuadratureStatement := by
  intro k F hF s hs m hm
  let p : MvPolynomial (Fin 3) ℝ :=
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm m) 1
  have hp : DegreeFour p := by
    change (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm m) (1 : ℝ)).totalDegree ≤ 4
    rw [MvPolynomial.totalDegree_monomial _ (by norm_num : (1 : ℝ) ≠ 0)]
    rw [Finsupp.equivFunOnFinite_symm_sum]
    exact hm
  have hEval (a : Vec3) : MvPolynomial.eval a p = mono m a := by
    simp [p, mono, MvPolynomial.eval_monomial,
      Finsupp.equivFunOnFinite_symm_apply_apply]
  have hMoment : (∑ j, F.weight j * mono m (F.point j)) = moment (mono m) := by
    have h := hF.2.2.2 p hp
    simpa only [hEval] using h
  rcases hs with rfl | rfl
  · change (∑ j, F.weight j * mono m (F.point j)) = siteFunctional .U (mono m)
    exact hMoment.trans (siteLawDecomposition.1 (mono m)).symm
  · change (3 / 5 : ℝ) * (∑ j, F.weight j * mono m (F.point j)) +
      (2 / 5 : ℝ) * mono m 0 = siteFunctional .D (mono m)
    rw [hMoment]
    exact (siteLawDecomposition.2 (mono m)).symm

end AKLT.W.MOM031
