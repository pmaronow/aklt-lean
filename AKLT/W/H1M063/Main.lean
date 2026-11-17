module
public import AKLT.Blueprint.H1.NodesV2Reduction

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder Pointwise
open AKLT.Defs

namespace AKLT.W.H1M063

private theorem support_difference_scalar_subset {σ : Type*} [DecidableEq σ]
    (p q : MvPolynomial σ ℝ) (c : ℝ) :
    (p - MvPolynomial.C c * q).support ⊆ p.support ∪ q.support := by
  classical
  have hC : (MvPolynomial.C c : MvPolynomial σ ℝ).support ⊆ ({0} : Finset (σ →₀ ℕ)) := by
    rw [MvPolynomial.support_C]
    split_ifs <;> simp
  calc
    (p - MvPolynomial.C c * q).support ⊆ p.support ∪ (MvPolynomial.C c * q).support :=
      MvPolynomial.support_sub σ p (MvPolynomial.C c * q)
    _ ⊆ p.support ∪ q.support := by
      intro m hm
      rcases Finset.mem_union.mp hm with hp | hmul
      · exact Finset.mem_union.mpr (Or.inl hp)
      · have hmul' := MvPolynomial.support_mul (MvPolynomial.C c) q hmul
        rcases Finset.mem_add.mp hmul' with ⟨a, ha, b, hb, hab⟩
        have ha0 : a = 0 := Finset.mem_singleton.mp (hC ha)
        have hm_eq : m = b := by simpa [ha0] using hab.symm
        exact Finset.mem_union.mpr (Or.inr (by simpa [hm_eq] using hb))

private theorem evaluate_difference {n : ℕ} (p q : RealVectorPolynomial n) (c : ℝ)
    (u : Fin n → Vec3) :
    evaluateRealPolynomial (p - MvPolynomial.C c * q) u =
      evaluateRealPolynomial p u - c * evaluateRealPolynomial q u := by
  simp [evaluateRealPolynomial]

theorem main : AKLT.Blueprint.H1.DifferenceStructureStatementV2 := by
  classical
  intro J p q c hp hq hip hiq hsp hsq
  have hsupport := support_difference_scalar_subset p q c
  refine ⟨?_, ?_, ?_⟩
  · intro m hm j
    rcases Finset.mem_union.mp (hsupport hm) with hp' | hq'
    · exact hp m hp' j
    · exact hq m hq' j
  · intro R hR u
    have hpInv := hip R hR u
    have hqInv := hiq R hR u
    rw [evaluate_difference, evaluate_difference, hpInv, hqInv]
  · intro m hm j hj k
    rcases Finset.mem_union.mp (hsupport hm) with hp' | hq'
    · exact hsp m hp' j hj k
    · exact hsq m hq' j hj k

end AKLT.W.H1M063

#print axioms AKLT.W.H1M063.main
