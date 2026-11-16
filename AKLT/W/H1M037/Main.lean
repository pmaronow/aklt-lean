import AKLT.Blueprint.H1.NodesSector

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs
open AKLT.Blueprint.H1

namespace AKLT.W.H1M037

private theorem transfer
    (J : Finset (Fin 20))
    (hadj : ∀ ψ χ : TensorSpace J,
      inner ℂ (totalSpinZ J ψ) χ = inner ℂ ψ (totalSpinZ J χ) ∧
      inner ℂ (totalSpinPlus J ψ) χ = inner ℂ ψ (totalSpinMinus J χ))
    (hcomm : ∀ ψ : TensorSpace J,
      totalSpinZ J (totalSpinPlus J ψ) - totalSpinPlus J (totalSpinZ J ψ) = totalSpinPlus J ψ ∧
      totalSpinZ J (totalSpinMinus J ψ) - totalSpinMinus J (totalSpinZ J ψ) = -totalSpinMinus J ψ ∧
      totalSpinPlus J (totalSpinMinus J ψ) - totalSpinMinus J (totalSpinPlus J ψ) =
        (2 : ℂ) • totalSpinZ J ψ) : WeightLadder J := by
  intro v m hv
  rcases hcomm v with ⟨hplus, hminus, hpm⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hplus
    rw [hv, map_smul] at h
    have h' : totalSpinZ J (totalSpinPlus J v) =
        ((m : ℂ) • totalSpinPlus J v) + totalSpinPlus J v := by
      calc
        _ = (_ - (m : ℂ) • totalSpinPlus J v) +
            (m : ℂ) • totalSpinPlus J v := by abel
        _ = totalSpinPlus J v + (m : ℂ) • totalSpinPlus J v := by rw [h]
        _ = _ := add_comm _ _
    calc
      totalSpinZ J (totalSpinPlus J v) =
          ((m : ℂ) • totalSpinPlus J v) + totalSpinPlus J v := h'
      _ = ((m : ℂ) + 1) • totalSpinPlus J v := by
        simpa using (add_smul (m : ℂ) (1 : ℂ) (totalSpinPlus J v)).symm
      _ = ((m + 1 : ℝ) : ℂ) • totalSpinPlus J v := by
        congr 1
        push_cast
        ring
  · have h := hminus
    rw [hv, map_smul] at h
    have h' : totalSpinZ J (totalSpinMinus J v) =
        ((m : ℂ) • totalSpinMinus J v) + -totalSpinMinus J v := by
      calc
        _ = (_ - (m : ℂ) • totalSpinMinus J v) +
            (m : ℂ) • totalSpinMinus J v := by abel
        _ = -totalSpinMinus J v + (m : ℂ) • totalSpinMinus J v := by rw [h]
        _ = _ := add_comm _ _
    calc
      totalSpinZ J (totalSpinMinus J v) =
          ((m : ℂ) • totalSpinMinus J v) + -totalSpinMinus J v :=
        h'
      _ = ((m : ℂ) + -1) • totalSpinMinus J v := by
        simpa using (add_smul (m : ℂ) (-1 : ℂ) (totalSpinMinus J v)).symm
      _ = ((m - 1 : ℝ) : ℂ) • totalSpinMinus J v := by
        congr 1
        push_cast
        ring
  · intro hvnz hm hzero
    have hminusAdj := (hadj (totalSpinMinus J v) v).2
    have hplusAdj := (hadj v (totalSpinPlus J v)).2
    have hpair0 := congrArg (fun x : TensorSpace J =>
      (inner ℂ v x).re) hpm
    rw [inner_sub_right, Complex.sub_re] at hpair0
    have hpair : (inner ℂ v (totalSpinPlus J (totalSpinMinus J v))).re -
        (inner ℂ v (totalSpinMinus J (totalSpinPlus J v))).re =
        2 * m * ‖v‖ ^ 2 := by
      calc
        _ = (inner ℂ v ((2 : ℂ) • totalSpinZ J v)).re := by
          exact hpair0
        _ = 2 * m * ‖v‖ ^ 2 := by
          rw [inner_smul_right, hv, inner_smul_right]
          rw [← mul_assoc]
          have hc : (2 : ℂ) * (m : ℂ) = ((2 * m : ℝ) : ℂ) := by push_cast; ring
          rw [hc, Complex.re_ofReal_mul]
          exact congrArg (fun t : ℝ => 2 * m * t)
            (inner_self_eq_norm_sq (𝕜 := ℂ) v)
    have hminusNorm : (inner ℂ v (totalSpinPlus J (totalSpinMinus J v))).re =
        ‖totalSpinMinus J v‖ ^ 2 := by
      calc
        _ = (inner ℂ (totalSpinPlus J (totalSpinMinus J v)) v).re :=
          inner_re_symm (𝕜 := ℂ) v (totalSpinPlus J (totalSpinMinus J v))
        _ = (inner ℂ (totalSpinMinus J v) (totalSpinMinus J v)).re := by rw [hminusAdj]
        _ = _ := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
    have hplusNorm : (inner ℂ v (totalSpinMinus J (totalSpinPlus J v))).re =
        ‖totalSpinPlus J v‖ ^ 2 := by
      calc
        _ = (inner ℂ (totalSpinPlus J v) (totalSpinPlus J v)).re := by rw [← hplusAdj]
        _ = _ := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
    have hdiff : ‖totalSpinMinus J v‖ ^ 2 - ‖totalSpinPlus J v‖ ^ 2 =
        2 * m * ‖v‖ ^ 2 := by
      calc
        _ = (inner ℂ v (totalSpinPlus J (totalSpinMinus J v))).re -
            (inner ℂ v (totalSpinMinus J (totalSpinPlus J v))).re := by
          rw [hminusNorm, hplusNorm]
        _ = _ := hpair
    have hvnorm : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hvnz)
    rw [hzero, norm_zero] at hdiff
    nlinarith [sq_nonneg ‖totalSpinPlus J v‖]
  · intro hvnz hm hzero
    have hminusAdj := (hadj (totalSpinMinus J v) v).2
    have hplusAdj := (hadj v (totalSpinPlus J v)).2
    have hpair0 := congrArg (fun x : TensorSpace J =>
      (inner ℂ v x).re) hpm
    rw [inner_sub_right, Complex.sub_re] at hpair0
    have hpair : (inner ℂ v (totalSpinPlus J (totalSpinMinus J v))).re -
        (inner ℂ v (totalSpinMinus J (totalSpinPlus J v))).re =
        2 * m * ‖v‖ ^ 2 := by
      calc
        _ = (inner ℂ v ((2 : ℂ) • totalSpinZ J v)).re := by
          exact hpair0
        _ = 2 * m * ‖v‖ ^ 2 := by
          rw [inner_smul_right, hv, inner_smul_right]
          rw [← mul_assoc]
          have hc : (2 : ℂ) * (m : ℂ) = ((2 * m : ℝ) : ℂ) := by push_cast; ring
          rw [hc, Complex.re_ofReal_mul]
          exact congrArg (fun t : ℝ => 2 * m * t)
            (inner_self_eq_norm_sq (𝕜 := ℂ) v)
    have hminusNorm : (inner ℂ v (totalSpinPlus J (totalSpinMinus J v))).re =
        ‖totalSpinMinus J v‖ ^ 2 := by
      calc
        _ = (inner ℂ (totalSpinPlus J (totalSpinMinus J v)) v).re :=
          inner_re_symm (𝕜 := ℂ) v (totalSpinPlus J (totalSpinMinus J v))
        _ = (inner ℂ (totalSpinMinus J v) (totalSpinMinus J v)).re := by rw [hminusAdj]
        _ = _ := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
    have hplusNorm : (inner ℂ v (totalSpinMinus J (totalSpinPlus J v))).re =
        ‖totalSpinPlus J v‖ ^ 2 := by
      calc
        _ = (inner ℂ (totalSpinPlus J v) (totalSpinPlus J v)).re := by rw [← hplusAdj]
        _ = _ := (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
    have hdiff : ‖totalSpinMinus J v‖ ^ 2 - ‖totalSpinPlus J v‖ ^ 2 =
        2 * m * ‖v‖ ^ 2 := by
      calc
        _ = (inner ℂ v (totalSpinPlus J (totalSpinMinus J v))).re -
            (inner ℂ v (totalSpinMinus J (totalSpinPlus J v))).re := by
          rw [hminusNorm, hplusNorm]
        _ = _ := hpair
    have hvnorm : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hvnz)
    rw [hzero, norm_zero] at hdiff
    nlinarith [sq_nonneg ‖totalSpinMinus J v‖]

theorem main : AKLT.Blueprint.H1.WeightLadderTransferStatement := by
  intro J hadj hcomm
  exact transfer J hadj hcomm

#print axioms AKLT.W.H1M037.main

end AKLT.W.H1M037
