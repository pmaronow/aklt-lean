import AKLT.Blueprint.Rec.NodesKernel

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs

namespace AKLT.W.REC071

theorem main : AKLT.Blueprint.Rec.ShiftedRowsRealStatement := by
  classical
  intro θ ρ hθ hθ1 hρ hρ1 hw
  rcases hw with ⟨hentry, hrow⟩
  let e : PairType → (PairType × ℕ) → ℝ≥0∞ := fun X j =>
    shiftKernel X j.1 j.2 * ENNReal.ofReal (θ ^ (-(j.2 : ℤ))) *
      ENNReal.ofReal (AKLT.Blueprint.Rec.witnessReal j.1)
  have heq (X : PairType) : (∑' j : PairType × ℕ, e X j) =
      ∑ Y : PairType, shiftedKernel θ X Y *
        ENNReal.ofReal (AKLT.Blueprint.Rec.witnessReal Y) := by
    rw [ENNReal.tsum_prod']
    simp only [e, tsum_fintype]
    apply Finset.sum_congr rfl
    intro Y hY
    rw [ENNReal.tsum_mul_right]
    rfl
  have htotal (X : PairType) : (∑' j : PairType × ℕ, e X j) ≠ ∞ := by
    rw [heq X]
    exact (lt_of_le_of_lt (hrow X) ENNReal.ofReal_lt_top).ne
  have htermReal (X Y : PairType) (s : ℕ) :
      (e X (Y, s)).toReal =
        AKLT.Blueprint.Rec.realKernel X Y s * AKLT.Blueprint.Rec.witnessReal Y *
          θ ^ (-(s : ℤ)) := by
    have hterm : shiftKernel X Y s * ENNReal.ofReal (θ ^ (-(s : ℤ))) ≠ ∞ := by
      have hsum := hentry X Y
      have hle : shiftKernel X Y s * ENNReal.ofReal (θ ^ (-(s : ℤ))) ≤
          shiftedKernel θ X Y := by
        change shiftKernel X Y s * ENNReal.ofReal (θ ^ (-(s : ℤ))) ≤
          ∑' t : ℕ, shiftKernel X Y t * ENNReal.ofReal (θ ^ (-(t : ℤ)))
        exact ENNReal.le_tsum
          (f := fun t : ℕ => shiftKernel X Y t * ENNReal.ofReal (θ ^ (-(t : ℤ)))) s
      exact (lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hsum)).ne
    have hpow : 0 < θ ^ (-(s : ℤ)) := zpow_pos hθ (-(s : ℤ))
    have hshift : shiftKernel X Y s ≠ ∞ :=
      (ENNReal.lt_top_of_mul_ne_top_left hterm (ENNReal.ofReal_pos.mpr hpow).ne').ne
    have _ := hshift
    simp only [e, AKLT.Blueprint.Rec.realKernel, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hpow.le,
      ENNReal.toReal_ofReal (AKLT.Blueprint.Rec.witness_positive Y).le]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y s
    exact ENNReal.toReal_nonneg
  · intro X
    exact AKLT.Blueprint.Rec.witness_positive X
  · intro X
    have hs := ENNReal.summable_toReal (htotal X)
    refine hs.congr ?_
    intro j
    rcases j with ⟨Y, s⟩
    exact htermReal X Y s
  · intro X
    have hreal : (∑' j : PairType × ℕ, e X j).toReal =
        ∑' j : PairType × ℕ, (e X j).toReal :=
      ENNReal.tsum_toReal_eq (fun _ => ENNReal.ne_top_of_tsum_ne_top (htotal X) _)
    calc
      (∑' j : PairType × ℕ,
          AKLT.Blueprint.Rec.realKernel X j.1 j.2 *
            AKLT.Blueprint.Rec.witnessReal j.1 * θ ^ (-(j.2 : ℤ))) =
          ∑' j : PairType × ℕ, (e X j).toReal := by
        apply tsum_congr
        intro j
        rcases j with ⟨Y, s⟩
        exact (htermReal X Y s).symm
      _ = (∑' j : PairType × ℕ, e X j).toReal := hreal.symm
      _ ≤ (ENNReal.ofReal (ρ * AKLT.Blueprint.Rec.witnessReal X)).toReal := by
        apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
        rw [heq X]
        exact hrow X
      _ = ρ * AKLT.Blueprint.Rec.witnessReal X :=
        ENNReal.toReal_ofReal (mul_nonneg hρ.le (AKLT.Blueprint.Rec.witness_positive X).le)

end AKLT.W.REC071
