module
public import AKLT.Blueprint.Win.NodesRemoval

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN061

theorem main : AKLT.Blueprint.Win.RemovalTelescopeStatement := by
  classical
  intro G X τ e hzero hlast A θ hstep
  let f : ℕ → ℝ := fun n =>
    AKLT.Blueprint.Win.logRatio G (AKLT.Blueprint.Win.removedPrefix e n) τ
  have htel :
      (∑ j ∈ Finset.range (e.last + 1), (f j - f (j + 1))) =
        f 0 - f (e.last + 1) := by
    calc
      (∑ j ∈ Finset.range (e.last + 1), (f j - f (j + 1))) =
          ∑ j ∈ Finset.range (e.last + 1), ((-f (j + 1)) - (-f j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (-f (e.last + 1)) - (-f 0) :=
        Finset.sum_range_sub (fun j => -f j) (e.last + 1)
      _ = f 0 - f (e.last + 1) := by ring
  have hcut : AKLT.Blueprint.Win.cutError G X τ = f (e.last + 1) - f 0 := by
    simp [AKLT.Blueprint.Win.cutError, f, hlast, hzero]
  have habs :
      |AKLT.Blueprint.Win.cutError G X τ| =
        |∑ j ∈ Finset.range (e.last + 1), (f j - f (j + 1))| := by
    rw [hcut]
    rw [abs_sub_comm]
    rw [← htel]
  have hseed :
      |f 0 - f 1| ≤
        1 + 4 * A * θ ^ AKLT.Blueprint.Win.depthShift G (e.site ⟨0, by omega⟩) := by
    have h := hstep ⟨0, by omega⟩
    simpa [f] using h
  have htail :
      (∑ j : Fin e.last, |f (j.val + 1) - f (j.val + 2)|) ≤
        2 * A * (∑ j : Fin e.last,
          θ ^ AKLT.Blueprint.Win.depthShift G (e.site j.succ)) := by
    calc
      (∑ j : Fin e.last, |f (j.val + 1) - f (j.val + 2)|) ≤
          ∑ j : Fin e.last, 2 * A * θ ^ AKLT.Blueprint.Win.depthShift G
            (e.site j.succ) := by
              apply Finset.sum_le_sum
              intro j hj
              have h := hstep j.succ
              simpa [f, Nat.add_assoc] using h
      _ = 2 * A * (∑ j : Fin e.last,
            θ ^ AKLT.Blueprint.Win.depthShift G (e.site j.succ)) := by
              rw [← Finset.mul_sum]
  have hsplit :
      (∑ j ∈ Finset.range (e.last + 1), |f j - f (j + 1)|) =
        |f 0 - f 1| +
          ∑ i : Fin e.last, |f (i.val + 1) - f (i.val + 2)| := by
    rw [Finset.sum_range_succ', Finset.sum_fin_eq_sum_range]
    rw [add_comm (∑ i ∈ Finset.range e.last, |f (i + 1) - f (i + 2)|)
      |f 0 - f 1|]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [hi]
  calc
    |AKLT.Blueprint.Win.cutError G X τ| ≤
        ∑ j ∈ Finset.range (e.last + 1), |f j - f (j + 1)| := by
          rw [habs]
          exact Finset.abs_sum_le_sum_abs
            (fun j => f j - f (j + 1)) (Finset.range (e.last + 1))
    _ = |f 0 - f 1| +
          ∑ i : Fin e.last, |f (i.val + 1) - f (i.val + 2)| := hsplit
    _ ≤ 1 + 4 * A * θ ^ AKLT.Blueprint.Win.depthShift G (e.site ⟨0, by omega⟩) +
          2 * A * ∑ j : Fin e.last,
            θ ^ AKLT.Blueprint.Win.depthShift G (e.site j.succ) := by
          exact add_le_add hseed htail

end AKLT.W.WIN061

#print axioms AKLT.W.WIN061.main
