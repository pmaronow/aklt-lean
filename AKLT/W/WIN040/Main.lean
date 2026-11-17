module
public import AKLT.Blueprint.Win.NodesTaper

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs

namespace AKLT.W.WIN040

open AKLT.Blueprint.Win

private theorem natAbs_sub_add_le (p q r : ℤ) :
    (p - r).natAbs ≤ (p - q).natAbs + (q - r).natAbs := by
  rw [show p - r = (p - q) + (q - r) by omega]
  exact Int.natAbs_add_le _ _

private theorem supDist_step_le (x v a : Plane) (h : supDist x v ≤ 1) :
    supDist x a ≤ supDist v a + 1 := by
  have h₁ := Nat.le_max_left (x.1 - v.1).natAbs (x.2 - v.2).natAbs
  have h₂ := Nat.le_max_right (x.1 - v.1).natAbs (x.2 - v.2).natAbs
  have hx₁ : (x.1 - a.1).natAbs ≤ (v.1 - a.1).natAbs + 1 := by
    have ht := natAbs_sub_add_le x.1 v.1 a.1
    dsimp [supDist] at h
    omega
  have hx₂ : (x.2 - a.2).natAbs ≤ (v.2 - a.2).natAbs + 1 := by
    have ht := natAbs_sub_add_le x.2 v.2 a.2
    dsimp [supDist] at h
    omega
  dsimp [supDist]
  omega

private theorem supDist_abs_step (x v a : Plane) (h : supDist x v ≤ 1) :
    |(supDist x a : ℤ) - (supDist v a : ℤ)| ≤ 1 := by
  have h₁ := supDist_step_le x v a h
  have hsymm : supDist v x = supDist x v := by
    dsimp [supDist]
    rw [show v.1 - x.1 = -(x.1 - v.1) by omega,
      show v.2 - x.2 = -(x.2 - v.2) by omega]
    simp only [Int.natAbs_neg]
  have h₂ := supDist_step_le v x a (by rw [hsymm]; exact h)
  rw [abs_le]
  constructor <;> omega

private theorem radialOffset_step_le (x v y : Plane) (u : ℕ) (i : ℤ)
    (h : supDist x v ≤ 1) :
    radialOffset y u i x ≤ radialOffset y u i v + 1 := by
  dsimp [radialOffset]
  have hd := supDist_abs_step x v y h
  have ht := natAbs_sub_add_le (supDist x y : ℤ) (supDist v y : ℤ)
    (shellRadius u i)
  have hdist : ((supDist x y : ℤ) - (supDist v y : ℤ)).natAbs ≤ 1 := by
    change ((supDist x y : ℤ) - (supDist v y : ℤ)).natAbs ≤ (1 : ℤ).natAbs
    rw [Int.natAbs_le_iff_sq_le]
    rw [abs_le] at hd
    nlinarith
  omega

private theorem supDist_starBall_le_one (x v : Plane) (h : x ∈ starBall v) :
    supDist x v ≤ 1 := by
  change (x.1, x.2) ∈
    (Finset.Icc (v.1 - 1) (v.1 + 1)).product
      (Finset.Icc (v.2 - 1) (v.2 + 1)) at h
  have hp := Finset.mem_product.mp h
  simp only [Finset.mem_Icc] at hp
  rcases hp with ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
  dsimp [supDist]
  apply max_le
  · change (x.1 - v.1).natAbs ≤ (1 : ℤ).natAbs
    rw [Int.natAbs_le_iff_sq_le]
    have hlo : -1 ≤ x.1 - v.1 := by omega
    have hhi : x.1 - v.1 ≤ 1 := by omega
    nlinarith
  · change (x.2 - v.2).natAbs ≤ (1 : ℤ).natAbs
    rw [Int.natAbs_le_iff_sq_le]
    have hlo : -1 ≤ x.2 - v.2 := by omega
    have hhi : x.2 - v.2 ≤ 1 := by omega
    nlinarith

private theorem squareDepth_step_lower (x v a : Plane) (u : ℕ)
    (h : supDist x v ≤ 1) (hv : 0 < squareDepth a u v) :
    squareDepth a u x + 1 ≥ squareDepth a u v := by
  have hd := supDist_step_le x v a h
  have hrawv : 0 ≤ (u : ℤ) + 1 - (supDist v a : ℤ) := by
    dsimp [squareDepth] at hv
    omega
  have hEq : (u : ℤ) + 1 - (supDist v a : ℤ) = squareDepth a u v := by
    dsimp [squareDepth]
    exact (max_eq_right hrawv).symm
  have hxraw : (u : ℤ) + 1 - (supDist x a : ℤ) + 1 ≥
      (u : ℤ) + 1 - (supDist v a : ℤ) := by
    have hd' : (supDist x a : ℤ) ≤ (supDist v a : ℤ) + 1 := by
      exact_mod_cast hd
    omega
  rw [← hEq]
  dsimp [squareDepth]
  have hxle : (u : ℤ) + 1 - (supDist x a : ℤ) ≤
      max 0 ((u : ℤ) + 1 - (supDist x a : ℤ)) := le_max_right _ _
  omega

theorem main : AKLT.Blueprint.Win.RawHeightStatement := by
  intro a y u i hsetup x hx
  change x ∈ rawBoundary (taper a y u i) at hx
  rw [rawBoundary, Finset.mem_sdiff, Finset.mem_biUnion] at hx
  rcases hx with ⟨⟨v, hv, hxball⟩, _⟩
  have hstep : supDist x v ≤ 1 := supDist_starBall_le_one x v hxball
  have hradial : radialOffset y u i x ≤ radialOffset y u i v + 1 :=
    radialOffset_step_le x v y u i hstep
  have hvDepth : (radialOffset y u i v : ℤ) + 32 ≤ squareDepth a u v := by
    simp only [taper, Finset.mem_filter] at hv
    exact hv.2.2
  have hpositive : 0 < squareDepth a u v := by
    have : 0 ≤ (radialOffset y u i v : ℤ) := Nat.cast_nonneg _
    omega
  have hdepth : squareDepth a u x + 1 ≥ squareDepth a u v :=
    squareDepth_step_lower x v a u hstep hpositive
  have hradialCast : (radialOffset y u i x : ℤ) ≤
      (radialOffset y u i v : ℤ) + 1 := by exact_mod_cast hradial
  have : 30 + (radialOffset y u i x : ℤ) ≤ squareDepth a u x := by omega
  exact this

end AKLT.W.WIN040

#print axioms AKLT.W.WIN040.main
