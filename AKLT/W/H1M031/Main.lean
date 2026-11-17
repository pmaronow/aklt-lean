module
public import AKLT.Blueprint.H1.NodesReduction

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M031

theorem main : AKLT.Blueprint.H1.DifferenceStructureStatement := by
  intro J p q c hp hq hpInv hqInv hpSupp hqSupp
  classical
  have hscalar : (MvPolynomial.C c * q).support ⊆ q.support := by
    rw [MvPolynomial.C_mul']
    exact MvPolynomial.support_smul
  have hsub : (p - MvPolynomial.C c * q).support ⊆ p.support ∪ q.support := by
    exact (MvPolynomial.support_sub (p := p) (q := MvPolynomial.C c * q)).trans
      (Finset.union_subset_union (fun _ hx => hx) hscalar)
  refine ⟨?_, ?_, ?_⟩
  · intro m hm j
    rcases Finset.mem_union.mp (hsub hm) with hpm | hqm
    · exact hp m hpm j
    · exact hq m hqm j
  · intro R hR u
    change evaluateReduced (p - MvPolynomial.C c * q)
        (fun j => R.mulVec (u j)) =
      evaluateReduced (p - MvPolynomial.C c * q) u
    simp only [evaluateReduced, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C]
    have hpEq := hpInv R hR u
    have hqEq := hqInv R hR u
    change MvPolynomial.eval₂ (Rat.castHom ℝ) (fun v => R.mulVec (u v.1) v.2) p =
      MvPolynomial.eval₂ (Rat.castHom ℝ) (fun v => u v.1 v.2) p at hpEq
    change MvPolynomial.eval₂ (Rat.castHom ℝ) (fun v => R.mulVec (u v.1) v.2) q =
      MvPolynomial.eval₂ (Rat.castHom ℝ) (fun v => u v.1 v.2) q at hqEq
    rw [hpEq, hqEq]
  · intro m hm j hj k
    rcases Finset.mem_union.mp (hsub hm) with hpm | hqm
    · exact hpSupp m hpm j hj k
    · exact hqSupp m hqm j hj k

end AKLT.W.H1M031
