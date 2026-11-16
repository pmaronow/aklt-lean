import AKLT.Blueprint.H1.NodesLeaf

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.W.H1M004

private theorem siteFunctional_dot_localProduct (s : Status) {k : ℕ}
    (a : Fin k → Vec3) (v : Vec3) :
    siteFunctional s (fun n => localProduct a n * dot n v) =
      ∑ i : Fin 3, siteFunctional s (fun n => n i * localProduct a n) * v i := by
  unfold siteFunctional dot
  calc
    (∑ n : SpinLetter, spinWeight s n *
        (localProduct a (spinVector n) *
          ∑ i : Fin 3, spinVector n i * v i)) =
        ∑ n : SpinLetter, ∑ i : Fin 3,
          spinWeight s n * (localProduct a (spinVector n) *
            (spinVector n i * v i)) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp_rw [Finset.mul_sum]
    _ = ∑ i : Fin 3, ∑ n : SpinLetter,
          spinWeight s n * (localProduct a (spinVector n) *
            (spinVector n i * v i)) := Finset.sum_comm
    _ = ∑ i : Fin 3,
          (∑ n : SpinLetter,
            spinWeight s n * (spinVector n i * localProduct a (spinVector n))) * v i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      ring

theorem main : AKLT.Blueprint.H1.NormalizedMeanFactorStatement := by
  intro k a s ρ hρ hA hMean
  let A : ℝ := siteFunctional s (localProduct a)
  let u : Vec3 := fun i => localMean s a i / ρ
  have hρ2 : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hu : normSq u ≤ 1 := by
    have hdiv : normSq (localMean s a) / ρ ^ 2 ≤ 1 :=
      (div_le_iff₀ hρ2).2 (by nlinarith)
    have hnorm : normSq u = normSq (localMean s a) / ρ ^ 2 := by
      simp [u, normSq, dot, div_mul_div_comm, ← Finset.sum_div, pow_two]
    rw [hnorm]
    exact hdiv
  have hcoeff (i : Fin 3) :
      siteFunctional s (fun n => n i * localProduct a n) =
        A * localMean s a i := by
    dsimp [A, localMean]
    have hden : siteFunctional s (localProduct a) ≠ 0 := ne_of_gt hA
    field_simp
  have hscaled : dot (localMean s a) = fun v : Vec3 => ρ * dot u v := by
    funext v
    unfold dot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [u]
    field_simp
  refine ⟨A, ?_, u, hu, ?_⟩
  · exact hA
  · intro v hv
    have hexpand :
        siteFunctional s (fun n => localProduct a n * (1 + dot n v)) =
          siteFunctional s (localProduct a) +
            siteFunctional s (fun n => localProduct a n * dot n v) := by
      unfold siteFunctional
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    rw [hexpand, siteFunctional_dot_localProduct]
    have hcoeffSum :
        (∑ i : Fin 3,
          siteFunctional s (fun n => n i * localProduct a n) * v i) =
          A * dot (localMean s a) v := by
      rw [dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcoeff i]
      ring
    rw [hcoeffSum, hscaled]
    dsimp [A]
    ring

end AKLT.W.H1M004

