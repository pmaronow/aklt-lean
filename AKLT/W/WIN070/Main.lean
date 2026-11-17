module
public import AKLT.Blueprint.Win.NodesCut

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.W.WIN070

/-- A uniformly bounded exponential tilt preserves full support and changes
normalized point masses by at most the square of the tilt bound. -/
theorem main : AKLT.Blueprint.Win.BoundedTiltStatement := by
  classical
  intro Ω hΩ hΩne w hw E hE
  let Z : ℝ := ∑ s : Ω, w s
  have hZ : 0 < Z := by
    dsimp [Z]
    apply Finset.sum_pos
    · intro s hs
      exact hw s
    · exact ⟨Classical.choice hΩne, Finset.mem_univ _⟩
  have hbase_pos : ∀ s : Ω, 0 < AKLT.Defs.normalize w s := by
    intro s
    exact div_pos (hw s) hZ
  have hbase_sum : (∑ s : Ω, AKLT.Defs.normalize w s) = 1 := by
    change (∑ s ∈ Finset.univ, w s / Z) = 1
    rw [← Finset.sum_div]
    change (∑ s : Ω, w s) / Z = 1
    dsimp [Z]
    exact div_self hZ.ne'
  refine ⟨⟨hbase_pos, hbase_sum⟩, ?_⟩
  intro e he
  let v : Ω → ℝ := fun s => w s * Real.exp (-e s)
  let A : ℝ := ∑ s : Ω, v s
  have hev : ∀ s : Ω, -E ≤ e s ∧ e s ≤ E := by
    intro s
    exact abs_le.mp (he s)
  have hexp_lo : ∀ s : Ω, Real.exp (-E) ≤ Real.exp (-e s) := by
    intro s
    apply Real.exp_le_exp.mpr
    linarith [(hev s).2]
  have hexp_hi : ∀ s : Ω, Real.exp (-e s) ≤ Real.exp E := by
    intro s
    apply Real.exp_le_exp.mpr
    linarith [(hev s).1]
  have hvpos : ∀ s : Ω, 0 < v s := by
    intro s
    dsimp [v]
    exact mul_pos (hw s) (Real.exp_pos _)
  have hA : 0 < A := by
    dsimp [A]
    apply Finset.sum_pos
    · intro s hs
      exact hvpos s
    · exact ⟨Classical.choice hΩne, Finset.mem_univ _⟩
  have hAlo : Real.exp (-E) * Z ≤ A := by
    calc
      Real.exp (-E) * Z = ∑ s : Ω, w s * Real.exp (-E) := by
        dsimp [Z]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ ≤ ∑ s : Ω, w s * Real.exp (-e s) := by
        apply Finset.sum_le_sum
        intro s hs
        exact mul_le_mul_of_nonneg_left (hexp_lo s) (hw s).le
      _ = A := by simp [A, v]
  have hAhi : A ≤ Real.exp E * Z := by
    calc
      A = ∑ s : Ω, w s * Real.exp (-e s) := by simp [A, v]
      _ ≤ ∑ s : Ω, w s * Real.exp E := by
        apply Finset.sum_le_sum
        intro s hs
        exact mul_le_mul_of_nonneg_left (hexp_hi s) (hw s).le
      _ = Real.exp E * Z := by
        dsimp [Z]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring
  have htilt_pos : ∀ s : Ω, 0 < AKLT.Defs.normalize v s := by
    intro s
    exact div_pos (hvpos s) hA
  have htilt_sum : (∑ s : Ω, AKLT.Defs.normalize v s) = 1 := by
    change (∑ s ∈ Finset.univ, v s / A) = 1
    rw [← Finset.sum_div]
    change (∑ s : Ω, v s) / A = 1
    dsimp [A]
    exact div_self hA.ne'
  refine ⟨⟨htilt_pos, htilt_sum⟩, ?_⟩
  intro s
  constructor
  · change Real.exp (-2 * E) * (w s / Z) ≤ v s / A
    rw [← mul_div_assoc]
    rw [div_le_div_iff₀ hZ hA]
    calc
      (Real.exp (-2 * E) * w s) * A
          ≤ (Real.exp (-2 * E) * w s) * (Real.exp E * Z) :=
              mul_le_mul_of_nonneg_left hAhi
                (mul_nonneg (Real.exp_pos _).le (hw s).le)
      _ = (w s * (Real.exp (-2 * E) * Real.exp E)) * Z := by ring
      _ = (w s * Real.exp (-E)) * Z := by
            have hexp : Real.exp (-2 * E) * Real.exp E = Real.exp (-E) := by
              rw [← Real.exp_add]
              congr 1 <;> ring
            rw [hexp]
      _ ≤ (w s * Real.exp (-e s)) * Z := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hexp_lo s) (hw s).le) hZ.le
  · change v s / A ≤ Real.exp (2 * E) * (w s / Z)
    rw [← mul_div_assoc]
    rw [div_le_div_iff₀ hA hZ]
    have hexp : Real.exp (2 * E) * Real.exp (-E) = Real.exp E := by
      rw [← Real.exp_add]
      congr 1 <;> ring
    calc
      v s * Z ≤ (w s * Real.exp E) * Z := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hexp_hi s) (hw s).le) hZ.le
      _ = (w s * (Real.exp (2 * E) * Real.exp (-E))) * Z := by rw [← hexp]
      _ = (Real.exp (2 * E) * w s) * (Real.exp (-E) * Z) := by ring
      _ ≤ (Real.exp (2 * E) * w s) * A :=
        mul_le_mul_of_nonneg_left hAlo
          (mul_nonneg (Real.exp_pos _).le (hw s).le)

end AKLT.W.WIN070
