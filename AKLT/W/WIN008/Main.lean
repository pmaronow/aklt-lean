module
public import AKLT.Blueprint.Win.NodesShell

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs

namespace AKLT.W.WIN008

theorem main : AKLT.Blueprint.Win.ShellInclusionStatement := by
  intro a y u hs i hi x hx
  simp only [AKLT.Defs.shell, Finset.mem_filter] at hx
  rcases hx with ⟨hxsq, hr⟩
  simp only [AKLT.Defs.farVolume, Finset.mem_filter]
  refine ⟨hxsq, ?_⟩
  have hs1 : 1 < shellSpacing u := lt_of_lt_of_le (by norm_num) hs
  have hfloor : (i : ℝ) * shellSpacing u - 1 <
      ((⌊(i : ℝ) * shellSpacing u⌋ : ℤ) : ℝ) := by
    have h := Int.lt_floor_add_one ((i : ℝ) * shellSpacing u)
    linarith
  have hineq : ((i : ℝ) - 1) * shellSpacing u <
      ((⌊(i : ℝ) * shellSpacing u⌋ : ℤ) : ℝ) := by
    calc
      ((i : ℝ) - 1) * shellSpacing u = (i : ℝ) * shellSpacing u - shellSpacing u := by ring
      _ < (i : ℝ) * shellSpacing u - 1 := by linarith
      _ < ((⌊(i : ℝ) * shellSpacing u⌋ : ℤ) : ℝ) := hfloor
  have hr' : (supDist x y : ℝ) =
      ((⌊(i : ℝ) * shellSpacing u⌋ : ℤ) : ℝ) := by
    change (supDist x y : ℤ) = ⌊(i : ℝ) * shellSpacing u⌋ at hr
    exact_mod_cast hr
  rw [hr']
  exact hineq

end AKLT.W.WIN008
