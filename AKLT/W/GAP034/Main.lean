import AKLT.Blueprint.Gap.NodesPeriodic

noncomputable section

namespace AKLT.W.GAP034

open AKLT.Defs AKLT.Challenge

/-- A coordinate difference inside the expanded square is smaller than either
period, so equal residues must be equal integers. -/
theorem main : AKLT.Blueprint.Gap.HaloInjectionStatement := by
  intro L N M hM hL hN a
  classical
  intro x hx y hy hxy
  have hx' : x ∈ square a (M + 1) := (Finset.mem_coe).mp hx
  have hy' : y ∈ square a (M + 1) := (Finset.mem_coe).mp hy
  simp only [square, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hx' hy'
  rcases hx' with ⟨⟨hx1lo, hx1hi⟩, ⟨hx2lo, hx2hi⟩⟩
  rcases hy' with ⟨⟨hy1lo, hy1hi⟩, ⟨hy2lo, hy2hi⟩⟩
  have hLz : (2 * (M : ℤ) + 3) ≤ (L.val : ℤ) := by exact_mod_cast hL
  have hNz : (2 * (M : ℤ) + 3) ≤ (N.val : ℤ) := by exact_mod_cast hN
  have hcast : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by omega
  have h1lo : -(2 * (M : ℤ) + 2) ≤ y.1 - x.1 := by rw [hcast] at hx1lo hx1hi hy1lo hy1hi; omega
  have h1hi : y.1 - x.1 ≤ 2 * (M : ℤ) + 2 := by rw [hcast] at hx1lo hx1hi hy1lo hy1hi; omega
  have h2lo : -(2 * (M : ℤ) + 2) ≤ y.2 - x.2 := by rw [hcast] at hx2lo hx2hi hy2lo hy2hi; omega
  have h2hi : y.2 - x.2 ≤ 2 * (M : ℤ) + 2 := by rw [hcast] at hx2lo hx2hi hy2lo hy2hi; omega
  have hxy1 : (x.1 : ZMod L.val) = (y.1 : ZMod L.val) := congrArg Prod.fst hxy
  have hxy2 : (x.2 : ZMod N.val) = (y.2 : ZMod N.val) := congrArg Prod.snd hxy
  have hdiv1 : (L.val : ℤ) ∣ y.1 - x.1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub x.1 y.1 L.val).mp hxy1
  have hdiv2 : (N.val : ℤ) ∣ y.2 - x.2 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub x.2 y.2 N.val).mp hxy2
  have habs1 : |y.1 - x.1| < (L.val : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have habs2 : |y.2 - x.2| < (N.val : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have heq1 : y.1 - x.1 = 0 := Int.eq_zero_of_abs_lt_dvd hdiv1 habs1
  have heq2 : y.2 - x.2 = 0 := Int.eq_zero_of_abs_lt_dvd hdiv2 habs2
  have hxyeq : x = y := by
    apply Prod.ext <;> omega
  exact hxyeq

end AKLT.W.GAP034
