module
public import AKLT.Blueprint.Win.NodesTaper

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN037

private theorem natAbs_near (z : ℤ) (hz₁ : z ≤ 1) (hz₂ : -1 ≤ z) : z.natAbs ≤ 1 := by
  have hsq : z * z ≤ (1 : ℤ) * 1 := by nlinarith
  simpa using (Int.natAbs_le_iff_mul_self_le (a := z) (b := 1)).2 hsq

private theorem supDist_symm (x v : Plane) : supDist x v = supDist v x := by
  change max (x.1 - v.1).natAbs (x.2 - v.2).natAbs =
    max (v.1 - x.1).natAbs (v.2 - x.2).natAbs
  rw [show x.1 - v.1 = -(v.1 - x.1) by omega, Int.natAbs_neg,
    show x.2 - v.2 = -(v.2 - x.2) by omega, Int.natAbs_neg]

private theorem int_abs_bounds {z : ℤ} {u : ℕ} (h : z.natAbs ≤ u) :
    -(u : ℤ) ≤ z ∧ z ≤ u := by
  have hc : (z.natAbs : ℤ) ≤ u := by exact_mod_cast h
  by_cases hz : 0 ≤ z
  · rw [Int.natAbs_of_nonneg hz] at hc
    omega
  · have hz' : 0 ≤ -z := by omega
    have hc' : ((-z).natAbs : ℤ) ≤ u := by
      simpa only [Int.natAbs_neg] using hc
    rw [Int.natAbs_of_nonneg hz'] at hc'
    omega

private theorem supDist_step {x v y : Plane} (h : supDist x v ≤ 1) :
    supDist x y ≤ supDist v y + 1 := by
  have h₁ : (x.1 - v.1).natAbs ≤ 1 := by
    change max (x.1 - v.1).natAbs (x.2 - v.2).natAbs ≤ 1 at h
    exact (max_le_iff.mp h).1
  have h₂ : (x.2 - v.2).natAbs ≤ 1 := by
    change max (x.1 - v.1).natAbs (x.2 - v.2).natAbs ≤ 1 at h
    exact (max_le_iff.mp h).2
  have hc₁ : (x.1 - y.1).natAbs ≤ (v.1 - y.1).natAbs + 1 := by
    calc
      (x.1 - y.1).natAbs = ((x.1 - v.1) + (v.1 - y.1)).natAbs := by congr 1; omega
      _ ≤ (x.1 - v.1).natAbs + (v.1 - y.1).natAbs := Int.natAbs_add_le _ _
      _ ≤ (v.1 - y.1).natAbs + 1 := by omega
  have hc₂ : (x.2 - y.2).natAbs ≤ (v.2 - y.2).natAbs + 1 := by
    calc
      (x.2 - y.2).natAbs = ((x.2 - v.2) + (v.2 - y.2)).natAbs := by congr 1; omega
      _ ≤ (x.2 - v.2).natAbs + (v.2 - y.2).natAbs := Int.natAbs_add_le _ _
      _ ≤ (v.2 - y.2).natAbs + 1 := by omega
  change max (x.1 - y.1).natAbs (x.2 - y.2).natAbs ≤ _
  apply max_le_iff.mpr
  constructor
  · exact hc₁.trans (Nat.add_le_add_right (Nat.le_max_left _ _) 1)
  · exact hc₂.trans (Nat.add_le_add_right (Nat.le_max_right _ _) 1)

private theorem radialOffset_step {y : Plane} {u : ℕ} {i : ℤ} {x v : Plane}
    (h : supDist x v ≤ 1) :
    radialOffset y u i x ≤ radialOffset y u i v + 1 := by
  have hrev : supDist v x ≤ 1 := by
    rw [supDist_symm]
    exact h
  have hxy := supDist_step (x := x) (v := v) (y := y) h
  have hvy := supDist_step (x := v) (v := x) (y := y) hrev
  have hxy' : (supDist x y : ℤ) ≤ (supDist v y : ℤ) + 1 := by exact_mod_cast hxy
  have hvy' : (supDist v y : ℤ) ≤ (supDist x y : ℤ) + 1 := by exact_mod_cast hvy
  have hdiff : ((supDist x y : ℤ) - (supDist v y : ℤ)).natAbs ≤ 1 :=
    natAbs_near _ (by omega) (by omega)
  unfold radialOffset
  change ((supDist x y : ℤ) - shellRadius u i).natAbs ≤
    ((supDist v y : ℤ) - shellRadius u i).natAbs + 1
  calc
    _ = (((supDist x y : ℤ) - (supDist v y : ℤ)) +
        ((supDist v y : ℤ) - shellRadius u i)).natAbs := by congr 1; ring
    _ ≤ ((supDist x y : ℤ) - (supDist v y : ℤ)).natAbs +
        ((supDist v y : ℤ) - shellRadius u i).natAbs := Int.natAbs_add_le _ _
    _ ≤ _ := by omega

private theorem squareDepth_step {a : Plane} {u : ℕ} {x v : Plane}
    (h : supDist x v ≤ 1) :
    squareDepth a u v ≤ squareDepth a u x + 1 ∧
    squareDepth a u x ≤ squareDepth a u v + 1 := by
  have hrev : supDist v x ≤ 1 := by
    rw [supDist_symm]
    exact h
  have h₁ := supDist_step (x := x) (v := v) (y := a) h
  have h₂ := supDist_step (x := v) (v := x) (y := a) hrev
  have h₁' : (supDist x a : ℤ) ≤ (supDist v a : ℤ) + 1 := by exact_mod_cast h₁
  have h₂' : (supDist v a : ℤ) ≤ (supDist x a : ℤ) + 1 := by exact_mod_cast h₂
  constructor
  · change max 0 ((u : ℤ) + 1 - (supDist v a : ℤ)) ≤
      max 0 ((u : ℤ) + 1 - (supDist x a : ℤ)) + 1
    apply max_le_iff.mpr
    constructor
    · omega
    · omega
  · change max 0 ((u : ℤ) + 1 - (supDist x a : ℤ)) ≤
      max 0 ((u : ℤ) + 1 - (supDist v a : ℤ)) + 1
    apply max_le_iff.mpr
    constructor
    · omega
    · omega

private theorem square_of_depth_pos {a : Plane} {u : ℕ} {x : Plane}
    (h : 0 < squareDepth a u x) : x ∈ square a u := by
  have hdZ : (supDist x a : ℤ) ≤ u := by
    change 0 < max 0 ((u : ℤ) + 1 - (supDist x a : ℤ)) at h
    omega
  have hd : supDist x a ≤ u := by exact_mod_cast hdZ
  have hcoords : (x.1 - a.1).natAbs ≤ u ∧ (x.2 - a.2).natAbs ≤ u := by
    change max (x.1 - a.1).natAbs (x.2 - a.2).natAbs ≤ u at hd
    exact max_le_iff.mp hd
  have hcoord₁ := int_abs_bounds hcoords.1
  have hcoord₂ := int_abs_bounds hcoords.2
  have hmem : (x.1, x.2) ∈
      Finset.Icc (a.1 - (u : ℤ)) (a.1 + (u : ℤ)) ×ˢ
        Finset.Icc (a.2 - (u : ℤ)) (a.2 + (u : ℤ)) := by
    simp only [Finset.mem_product, Finset.mem_Icc]
    constructor <;> omega
  simpa [square] using hmem

/-- The raw boundary lies within one radial layer of the taper and has the stated near height window. -/
theorem main : AKLT.Blueprint.Win.RawRangeStatement := by
  intro a y u i hsetup x hx
  change x ∈ rawBoundary (taper a y u i) at hx
  rcases Finset.mem_sdiff.mp hx with ⟨hstar, hxnot⟩
  rcases Finset.mem_biUnion.mp hstar with ⟨v, hv, hxv⟩
  have hxv' : supDist x v ≤ 1 := by
    change x ∈ starBall v at hxv
    have hcoord : (v.1 ≤ x.1 + 1 ∧ x.1 ≤ v.1 + 1) ∧
        (v.2 ≤ x.2 + 1 ∧ x.2 ≤ v.2 + 1) := by
      simpa [starBall] using hxv
    have h₁ : (x.1 - v.1).natAbs ≤ 1 := natAbs_near _ (by omega) (by omega)
    have h₂ : (x.2 - v.2).natAbs ≤ 1 := natAbs_near _ (by omega) (by omega)
    change max (x.1 - v.1).natAbs (x.2 - v.2).natAbs ≤ 1
    exact max_le_iff.mpr ⟨h₁, h₂⟩
  have hv' : v ∈ square a u ∧
      (radialOffset y u i v : ℝ) ≤ shellSpacing u / 12 ∧
      (radialOffset y u i v : ℤ) + 32 ≤ squareDepth a u v := by
    simpa [taper] using hv
  have hrad : radialOffset y u i x ≤ radialOffset y u i v + 1 := radialOffset_step hxv'
  have hradReal : (radialOffset y u i x : ℝ) ≤ shellSpacing u / 12 + 1 := by
    have hcast : (radialOffset y u i x : ℝ) ≤ (radialOffset y u i v : ℝ) + 1 := by
      exact_mod_cast hrad
    linarith [hv'.2.1]
  refine ⟨hradReal, ?_⟩
  intro hnear
  have hdepth := squareDepth_step (a := a) (u := u) hxv'
  have hvRadInt : (radialOffset y u i v : ℤ) ≤ (radialOffset y u i x : ℤ) + 1 := by
    have hxvRev : supDist v x ≤ 1 := by rw [supDist_symm]; exact hxv'
    have hrev := radialOffset_step (y := y) (u := u) (i := i) (x := v) (v := x) hxvRev
    exact_mod_cast hrev
  have hlow : 30 + (radialOffset y u i x : ℤ) ≤ squareDepth a u x := by
    have hvlo : (radialOffset y u i v : ℤ) + 32 ≤ squareDepth a u v := hv'.2.2
    omega
  have hxdepthpos : 0 < squareDepth a u x := by omega
  have hxsquare : x ∈ square a u := square_of_depth_pos hxdepthpos
  have hbad : ¬ ((radialOffset y u i x : ℤ) + 32 ≤ squareDepth a u x) := by
    intro hbad
    apply hxnot
    change x ∈ (square a u).filter (fun z =>
      (radialOffset y u i z : ℝ) ≤ shellSpacing u / 12 ∧
      (radialOffset y u i z : ℤ) + 32 ≤ squareDepth a u z)
    exact Finset.mem_filter.mpr ⟨hxsquare, ⟨hnear, hbad⟩⟩
  have hupr : squareDepth a u x < 32 + (radialOffset y u i x : ℤ) := by omega
  exact ⟨hlow, by omega⟩

end AKLT.W.WIN037

#print axioms AKLT.W.WIN037.main
