import AKLT.W.REC029.Realize

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC029

private theorem siteFunctional_add (s : Status) (f g : Vec3 → ℝ) :
    siteFunctional s (fun n => f n + g n) =
      siteFunctional s f + siteFunctional s g := by
  simp only [siteFunctional]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem siteFunctional_dot_mul (s : Status) (f : Vec3 → ℝ)
    (v : Vec3) :
    siteFunctional s (fun n => dot n v * f n) =
      ∑ i, v i * siteFunctional s (fun n => n i * f n) := by
  change
    (∑ j : SpinLetter, spinWeight s j *
      ((∑ i : Fin 3, spinVector j i * v i) * f (spinVector j))) =
    ∑ i : Fin 3, v i *
      ∑ j : SpinLetter, spinWeight s j *
        (spinVector j i * f (spinVector j))
  calc
    _ = ∑ j : SpinLetter, ∑ i : Fin 3,
        v i * (spinWeight s j * (spinVector j i * f (spinVector j))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i : Fin 3, ∑ j : SpinLetter,
        v i * (spinWeight s j * (spinVector j i * f (spinVector j))) := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin 3, v i *
        ∑ j : SpinLetter, spinWeight s j *
          (spinVector j i * f (spinVector j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

/-- Integrating a factor `1 + n·v` only uses the normalizer and the
normalized first moment. -/
theorem affineFactor_identity (s : Status) {k : ℕ} (a : Fin k → Vec3)
    (v : Vec3) (hA : siteFunctional s (localProduct a) ≠ 0) :
    siteFunctional s (fun n => (1 + dot n v) * localProduct a n) =
      siteFunctional s (localProduct a) *
        (1 + dot (localMean s a) v) := by
  let P : Vec3 → ℝ := localProduct a
  have hsplit :
      siteFunctional s (fun n => (1 + dot n v) * P n) =
        siteFunctional s P + siteFunctional s (fun n => dot n v * P n) := by
    have hf : (fun n => (1 + dot n v) * P n) =
        (fun n => P n + dot n v * P n) := by
      funext n
      ring
    rw [hf, siteFunctional_add]
  rw [show (fun n => (1 + dot n v) * localProduct a n) =
      (fun n => (1 + dot n v) * P n) by rfl, hsplit,
    siteFunctional_dot_mul]
  have hmean : dot (localMean s a) v =
      (∑ i, v i * siteFunctional s (fun n => n i * localProduct a n)) /
        siteFunctional s (localProduct a) := by
    unfold dot localMean
    calc
      (∑ i, siteFunctional s (fun n => n i * localProduct a n) /
          siteFunctional s (localProduct a) * v i) =
        ∑ i, (v i * siteFunctional s (fun n => n i * localProduct a n)) /
          siteFunctional s (localProduct a) := by
            apply Finset.sum_congr rfl
            intro i hi
            field_simp [hA]
      _ = (∑ i, v i * siteFunctional s (fun n => n i * localProduct a n)) /
          siteFunctional s (localProduct a) := by rw [Finset.sum_div]
  rw [hmean]
  dsimp [P]
  field_simp

/-- Replace an active tip by a U tip with the same effective mean and
rescale its scalar and vector moments by the same positive number. -/
theorem main : AKLT.Blueprint.Rec.TipReplacementStatement := by
  intro s hs k hk b hb
  obtain ⟨hA, hMean⟩ := tip_mean_bound hk b hb s hs
  obtain ⟨a, hA', hRealize⟩ := realize_mean (localMean s b) hMean
  let A := siteFunctional s (localProduct b)
  let A' := siteFunctional .U (localProduct (fun j => (a j).val))
  refine ⟨a, A' / A, ?_, ?_⟩
  · exact div_pos hA' hA
  · intro v
    have hU := affineFactor_identity .U (fun j => (a j).val) v (ne_of_gt hA')
    have hS := affineFactor_identity s b v (ne_of_gt hA)
    rw [hRealize] at hU
    change
      siteFunctional .U (fun n => (1 + dot n v) *
        localProduct (fun j => (a j).val) n) =
      (A' / A) * siteFunctional s (fun n => (1 + dot n v) * localProduct b n)
    rw [hU, hS]
    dsimp [A', A]
    field_simp [ne_of_gt hA]

end AKLT.W.REC029

#print axioms AKLT.W.REC029.main
#print axioms AKLT.W.REC029.affineFactor_identity
