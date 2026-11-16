import AKLT.Blueprint.Rec.NodesWalk
open scoped BigOperators
example (c : ℝ) (f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) :
    (∑ i : Fin 3, ∑ j, ∑ k, ∑ l, c * f i j k l) =
      c * ∑ i, ∑ j, ∑ k, ∑ l, f i j k l := by
  simp_rw [← Finset.mul_sum]
