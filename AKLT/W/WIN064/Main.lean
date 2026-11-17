module
public import AKLT.W.WIN064.Polynomial
public import AKLT.W.WIN064.Quadrature

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN064

lemma framePinnedSum_eq_quadrature (κ : Plane → Fin 3) (G Y : Finset Plane)
    (τ : PinAssignment G) :
    framePinnedSum κ G Y τ =
      quadrature (fun x : ↥(G \ Y) => frameVector (κ x.val)) (complementPolynomial G Y τ) := by
  classical
  unfold framePinnedSum quadrature
  refine Finset.sum_congr (by ext; simp only [Finset.mem_univ]) ?_
  intro σ hσ
  rw [eval_complementPolynomial G Y τ (fun x => frameVector (κ x.val) (σ x))]
  have hext : extendVectors (fun x : ↥(G \ Y) => frameVector (κ x.val) (σ x)) =
      frameSpins κ σ := rfl
  simp only [hext, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  simp only [mul_assoc]

lemma pinnedSum_eq_quadrature (G Y : Finset Plane) (τ : PinAssignment G) :
    pinnedSum G Y τ (fun _ => 1) =
      quadrature (fun _ : ↥(G \ Y) => icoVector) (complementPolynomial G Y τ) := by
  classical
  unfold pinnedSum quadrature
  refine Finset.sum_congr (by ext; simp only [Finset.mem_univ]) ?_
  intro σ hσ
  rw [eval_complementPolynomial G Y τ (fun x => icoVector (σ x))]
  have hext : extendVectors (fun x : ↥(G \ Y) => icoVector (σ x)) = extendIcoSpins σ := rfl
  simp only [hext, Finset.prod_const, Finset.card_univ, Fintype.card_coe, mul_one]
  simp only [mul_assoc]

/-- The complementary partition polynomial can be transferred with its pins fixed. -/
theorem main : AKLT.Blueprint.Win.ComplementQuadratureStatement := by
  intro hThree _hExact κ G Y τ
  rw [framePinnedSum_eq_quadrature, pinnedSum_eq_quadrature]
  exact frame_quadrature hThree (fun x : ↥(G \ Y) => κ x.val)
    (complementPolynomial G Y τ) (complementPolynomial_degree G Y τ)

#print axioms incidence_bound
#print axioms framePinnedSum_eq_quadrature
#print axioms pinnedSum_eq_quadrature
#print axioms main

end AKLT.W.WIN064
