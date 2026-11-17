module
public import AKLT.Blueprint.Win.NodesShell

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs

namespace AKLT.W.WIN010

theorem main : AKLT.Blueprint.Win.SeedSeparationStatement := by
  intro a y u hs i hi hle
  change (⨅ z : (↑(AKLT.Defs.farVolume a y u i) : Set AKLT.Defs.Plane),
      (AKLT.Defs.supDist y z.val : ℕ∞)) ≤ 1 at hle
  have hbound : (2 : ℕ∞) ≤
      ⨅ z : (↑(AKLT.Defs.farVolume a y u i) : Set AKLT.Defs.Plane),
        (AKLT.Defs.supDist y z.val : ℕ∞) := by
    apply le_iInf
    intro z
    have hz : z.val ∈ AKLT.Defs.farVolume a y u i := z.property
    have hfilter := (Finset.mem_filter.mp hz).2
    have hiReal : (1 : ℝ) ≤ (i : ℝ) - 1 := by
      exact_mod_cast (show (1 : ℤ) ≤ i - 1 by omega)
    have hsReal : (2 : ℝ) ≤ AKLT.Defs.shellSpacing u := hs
    have hprod : (2 : ℝ) ≤ ((i : ℝ) - 1) * AKLT.Defs.shellSpacing u := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hiReal) (sub_nonneg.mpr hsReal)]
    have hdist : (2 : ℝ) < (AKLT.Defs.supDist z.val y : ℝ) := by
      exact lt_of_le_of_lt hprod hfilter
    have hdistNat : 2 < AKLT.Defs.supDist z.val y := by
      exact_mod_cast hdist
    have hcomm : AKLT.Defs.supDist z.val y = AKLT.Defs.supDist y z.val := by
      unfold AKLT.Defs.supDist
      rw [show z.val.1 - y.1 = -(y.1 - z.val.1) by omega,
        show z.val.2 - y.2 = -(y.2 - z.val.2) by omega,
        Int.natAbs_neg, Int.natAbs_neg]
    rw [← hcomm]
    exact_mod_cast (show 2 ≤ AKLT.Defs.supDist z.val y by omega)
  have hcontra : (2 : ℕ∞) ≤ 1 := le_trans hbound hle
  norm_num at hcontra

end AKLT.W.WIN010

#print axioms AKLT.W.WIN010.main
