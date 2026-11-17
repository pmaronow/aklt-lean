module
public import AKLT.W.REC070.Foundations

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec
namespace AKLT.W.REC070
set_option maxHeartbeats 1000000

lemma shift_increment (b θ : ℝ) (hb : 0 < b) (hbθ : b < θ) (hθ1 : θ ≤ 1)
    (n s : ℕ) (hs : s ≤ n + 1) :
    0 ≤ θ^(-(s : ℤ)) - 1 ∧
    θ^(-(s : ℤ)) - 1 ≤ (1 - θ) * (n + 1 : ℝ) * b^(-(n : ℤ) - 2) := by
  have hθ : 0 < θ := hb.trans hbθ
  have hb1 : b ≤ 1 := hbθ.le.trans hθ1
  have h1 : 1 ≤ θ^(-(s : ℤ)) := by
    simpa using zpow_le_zpow_right_of_le_one₀ hθ hθ1 (show -(s : ℤ) ≤ 0 by omega)
  have hbern (k : ℕ) : 1 - θ^k ≤ (k : ℝ) * (1 - θ) := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        1 - θ^(k+1) = (1 - θ) + θ * (1 - θ^k) := by rw [pow_succ]; ring
        _ ≤ (1 - θ) + θ * ((k : ℝ) * (1 - θ)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left ih hθ.le)
        _ ≤ ((k+1 : ℕ) : ℝ) * (1 - θ) := by
          have hh := mul_le_mul_of_nonneg_right hθ1
            (mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr hθ1))
          push_cast
          nlinarith
  have hpow : θ^(-(s : ℤ)) ≤ b^(-(n : ℤ) - 2) := by
    calc
      θ^(-(s : ℤ)) ≤ b^(-(s : ℤ)) := by
        simp only [zpow_neg, zpow_natCast]
        exact inv_anti₀ (pow_pos hb s) (pow_le_pow_left₀ hb.le hbθ.le s)
      _ ≤ b^(-(n : ℤ) - 2) :=
        zpow_le_zpow_right_of_le_one₀ hb hb1 (by omega)
  refine ⟨sub_nonneg.mpr h1, ?_⟩
  calc
    θ^(-(s : ℤ)) - 1 = (1 - θ^s) * θ^(-(s : ℤ)) := by
      simp only [zpow_neg, zpow_natCast]
      field_simp
    _ ≤ ((s : ℝ) * (1 - θ)) * θ^(-(s : ℤ)) :=
      mul_le_mul_of_nonneg_right (hbern s) (zpow_pos hθ _).le
    _ ≤ ((n + 1 : ℝ) * (1 - θ)) * b^(-(n : ℤ) - 2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (sub_nonneg.mpr hθ1)
      · exact hpow
      · exact (zpow_pos hθ _).le
      · positivity
    _ = _ := by ring

end AKLT.W.REC070
