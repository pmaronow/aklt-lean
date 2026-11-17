module
public import AKLT.Blueprint.Win.NodesTopology

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Blueprint.Win

namespace AKLT.W.WIN029

private theorem sum_thicken_le_sum_cross (X : Finset AKLT.Defs.Plane)
    (f : AKLT.Defs.Plane → ℝ) (hf : ∀ z, 0 ≤ f z) :
    ∑ z ∈ thicken X, f z ≤ ∑ x ∈ X, ∑ z ∈ cross x, f z := by
  classical
  induction X using Finset.induction_on with
  | empty => simp [thicken]
  | @insert a X ha ih =>
    change (∑ z ∈ (insert a X).biUnion cross, f z) ≤
      ∑ x ∈ insert a X, ∑ z ∈ cross x, f z
    rw [Finset.biUnion_insert]
    rw [Finset.sum_insert ha]
    have hunion := Finset.sum_union_inter (s₁ := cross a) (s₂ := thicken X) (f := f)
    have hinter : 0 ≤ ∑ z ∈ cross a ∩ thicken X, f z :=
      Finset.sum_nonneg (fun z hz => hf z)
    have hsum : (∑ z ∈ cross a ∪ thicken X, f z) ≤
        (∑ z ∈ cross a, f z) + ∑ z ∈ thicken X, f z := by
      linarith
    calc
      ∑ z ∈ cross a ∪ thicken X, f z ≤
          (∑ z ∈ cross a, f z) + ∑ z ∈ thicken X, f z := hsum
      _ ≤ (∑ z ∈ cross a, f z) + ∑ x ∈ X, ∑ z ∈ cross x, f z :=
        add_le_add_right ih (∑ z ∈ cross a, f z)

 theorem main : AKLT.Blueprint.Win.CrossWeightSumStatement := by
  intro X f hf c hc hcard hlocal
  calc
    ∑ z ∈ thicken X, f z ≤ ∑ x ∈ X, ∑ z ∈ cross x, f z :=
      sum_thicken_le_sum_cross X f hf
    _ ≤ ∑ x ∈ X, 5 * c * f x := by
      apply Finset.sum_le_sum
      intro x hx
      calc
        ∑ z ∈ cross x, f z ≤ ∑ z ∈ cross x, c * f x := by
          apply Finset.sum_le_sum
          intro z hz
          exact hlocal x hx z hz
        _ = 5 * c * f x := by
          rw [Finset.sum_const, hcard x]
          simp [mul_assoc]
    _ = 5 * c * ∑ x ∈ X, f x := by rw [Finset.mul_sum]

end AKLT.W.WIN029

#print axioms AKLT.W.WIN029.main
