module
public import AKLT.Blueprint.Gap.NodesShell

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

open AKLT.Defs

namespace AKLT.W.GAP043

/-- The far regions decrease with their index, and the later shell lies in the
preceding far region. -/
theorem main : AKLT.Blueprint.Gap.ShellNestingStatement := by
  intro a y u hs i j hij
  have hs0 : 0 ≤ shellSpacing u := le_trans (by norm_num) hs
  constructor
  · intro x hx
    simp only [farVolume, Finset.mem_filter] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have hcoefZ : i ≤ j - 1 := by omega
    have hcoef : (i : ℝ) ≤ (j : ℝ) - 1 := by
      exact_mod_cast hcoefZ
    have hmul := mul_le_mul_of_nonneg_right hcoef hs0
    have hidx : ((i + 1 : ℤ) : ℝ) - 1 = (i : ℝ) := by
      push_cast
      ring
    rw [hidx]
    exact lt_of_le_of_lt hmul hx.2
  · intro x hx
    change x ∈ (square a u).filter
      (fun z : Plane => (supDist z y : ℤ) = shellRadius u (j - 1)) at hx
    rw [Finset.mem_filter] at hx
    rw [shellRadius] at hx
    simp only [farVolume, Finset.mem_filter]
    refine ⟨hx.1, ?_⟩
    have hfloor :
        ((j - 1 : ℤ) : ℝ) * shellSpacing u - 1 <
          (⌊((j - 1 : ℤ) : ℝ) * shellSpacing u⌋ : ℝ) := by
      exact Int.sub_one_lt_floor (((j - 1 : ℤ) : ℝ) * shellSpacing u)
    have hgapZ : i + 1 ≤ j - 1 := by omega
    have hgap : (i : ℝ) + 1 ≤ ((j - 1 : ℤ) : ℝ) := by
      exact_mod_cast hgapZ
    have hgapExtra : 0 ≤ (((j - 1 : ℤ) : ℝ) - (i : ℝ) - 1) * shellSpacing u :=
      mul_nonneg (by linarith [hgap]) hs0
    have hfloorLower :
        (i : ℝ) * shellSpacing u <
          ((j - 1 : ℤ) : ℝ) * shellSpacing u - 1 := by
      nlinarith [hgapExtra]
    have heqReal :
        (supDist x y : ℝ) =
          (⌊((j - 1 : ℤ) : ℝ) * shellSpacing u⌋ : ℝ) := by
      exact_mod_cast hx.2
    have hidx : ((i + 1 : ℤ) : ℝ) - 1 = (i : ℝ) := by
      push_cast
      ring
    rw [hidx, heqReal]
    exact lt_trans hfloorLower hfloor

end AKLT.W.GAP043
