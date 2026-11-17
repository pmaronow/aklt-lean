module
public import AKLT.Blueprint.Win.NodesShell

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs

namespace AKLT.W.WIN003

private theorem supDist_symm (x y : Plane) : supDist x y = supDist y x := by
  have h₁ : (x.1 - y.1).natAbs = (y.1 - x.1).natAbs := by
    rw [show x.1 - y.1 = -(y.1 - x.1) by ring, Int.natAbs_neg]
  have h₂ : (x.2 - y.2).natAbs = (y.2 - x.2).natAbs := by
    rw [show x.2 - y.2 = -(y.2 - x.2) by ring, Int.natAbs_neg]
  simp [supDist, h₁, h₂]

private theorem supDist_triangle (x y z : Plane) :
    supDist x z ≤ supDist x y + supDist y z := by
  apply max_le
  · have hsub := Int.natAbs_sub_le (x.1 - y.1) (z.1 - y.1)
    have hleft : (x.1 - y.1).natAbs ≤ supDist x y := Nat.le_max_left _ _
    have hright : (z.1 - y.1).natAbs ≤ supDist y z := by
      rw [show z.1 - y.1 = -(y.1 - z.1) by ring, Int.natAbs_neg]
      exact Nat.le_max_left _ _
    have heq : x.1 - z.1 = (x.1 - y.1) - (z.1 - y.1) := by ring
    rw [heq]
    exact hsub.trans (Nat.add_le_add hleft hright)
  · have hsub := Int.natAbs_sub_le (x.2 - y.2) (z.2 - y.2)
    have hleft : (x.2 - y.2).natAbs ≤ supDist x y := Nat.le_max_right _ _
    have hright : (z.2 - y.2).natAbs ≤ supDist y z := by
      rw [show z.2 - y.2 = -(y.2 - z.2) by ring, Int.natAbs_neg]
      exact Nat.le_max_right _ _
    have heq : x.2 - z.2 = (x.2 - y.2) - (z.2 - y.2) := by ring
    rw [heq]
    exact hsub.trans (Nat.add_le_add hleft hright)

theorem main : AKLT.Blueprint.Win.ExceptionalLocalizationStatement := by
  classical
  intro a y u hscale i hi
  let s : ℝ := shellSpacing u
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  simp only [AKLT.Defs.exceptionalIndices, Finset.mem_filter, Finset.mem_Icc] at hi
  obtain ⟨⟨_hiLower, hiUpper⟩, hex⟩ := hi
  obtain ⟨x, hxShell, c, hcCorner, hclose⟩ := hex
  have hxShell' : x ∈ shell a y u i := hxShell
  simp only [AKLT.Defs.shell, Finset.mem_filter] at hxShell'
  have hxRadius : (supDist x y : ℤ) = shellRadius u i := hxShell'.2
  have hiUpper' : i ≤ Int.floor (shellSpacing u) + 1 := by
    change i ≤ lastShellIndex u at hiUpper
    exact hiUpper
  have hiReal : (i : ℝ) ≤ s + 1 := by
    have hfloor : (Int.floor (shellSpacing u) : ℝ) ≤ s := by
      dsimp [s]
      exact Int.floor_le _
    have hiReal' : (i : ℝ) ≤ (Int.floor (shellSpacing u) : ℝ) + 1 := by
      exact_mod_cast hiUpper'
    linarith
  have hRadiusUpper : (shellRadius u i : ℝ) ≤ s ^ 2 + s := by
    have hmul : (i : ℝ) * s ≤ (s + 1) * s :=
      mul_le_mul_of_nonneg_right hiReal hs_nonneg
    have hfloor : ((Int.floor ((i : ℝ) * s) : ℤ) : ℝ) ≤ (i : ℝ) * s :=
      Int.floor_le _
    change ((Int.floor ((i : ℝ) * shellSpacing u) : ℤ) : ℝ) ≤ s ^ 2 + s
    dsimp [s] at hmul ⊢
    rw [show (s + 1) * s = s ^ 2 + s by ring] at hmul
    exact hfloor.trans hmul
  have hxRadiusReal : (supDist x y : ℝ) = (shellRadius u i : ℝ) := by
    exact_mod_cast hxRadius
  have hcloseReal : (supDist x c : ℝ) < s / 3 := by
    simpa [s] using hclose
  have hcornerTriangleNat : supDist c y ≤ supDist c x + supDist x y :=
    supDist_triangle c x y
  have hcornerTriangle : (supDist c y : ℝ) ≤ (supDist x c : ℝ) + (supDist x y : ℝ) := by
    have h := hcornerTriangleNat
    rw [supDist_symm c x] at h
    exact_mod_cast h
  have hcornerNear : (supDist c y : ℝ) < (u : ℝ) := by
    have hradius : (supDist x y : ℝ) ≤ s ^ 2 + s := by
      rw [hxRadiusReal]
      exact hRadiusUpper
    have hsmall : (supDist c y : ℝ) < s ^ 2 + 4 * s / 3 := by
      linarith
    exact hsmall.trans hscale
  have hreverseTriangleNat : supDist x y ≤ supDist x c + supDist c y :=
    supDist_triangle x c y
  have hreverseTriangle : (supDist x y : ℝ) ≤ (supDist x c : ℝ) + (supDist c y : ℝ) := by
    exact_mod_cast hreverseTriangleNat
  have hradialBound :
      |(supDist c y : ℝ) - (shellRadius u i : ℝ)| ≤ (supDist x c : ℝ) := by
    rw [← hxRadiusReal]
    apply abs_le.mpr
    constructor <;> linarith
  have hcornerNearNat : supDist c y < u := by
    exact_mod_cast hcornerNear
  refine ⟨c, hcCorner, hcornerNearNat, ?_⟩
  exact hradialBound.trans_lt hcloseReal

end AKLT.W.WIN003
