module
public import AKLT.Blueprint.Win.NodesTaper

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Win

namespace AKLT.W.WIN038

private lemma natAbs_sub_le_of_le_add {m n d : ℕ}
    (h₁ : m ≤ d + n) (h₂ : n ≤ d + m) :
    Int.natAbs ((m : ℤ) - (n : ℤ)) ≤ d := by
  by_cases h : m ≤ n
  · rw [Int.natAbs_natCast_sub_natCast_of_le h]
    omega
  · have hn : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge h)
    rw [show (m : ℤ) - (n : ℤ) = ((m - n : ℕ) : ℤ) by
      rw [Nat.cast_sub hn]]
    simp only [Int.natAbs_natCast]
    omega

private lemma supDist_comm (x y : Plane) : supDist x y = supDist y x := by
  unfold supDist
  congr 1
  · rw [show x.1 - y.1 = -(y.1 - x.1) by ring, Int.natAbs_neg]
  · rw [show x.2 - y.2 = -(y.2 - x.2) by ring, Int.natAbs_neg]

private lemma supDist_triangle (x y z : Plane) :
    supDist x z ≤ supDist x y + supDist y z := by
  apply max_le
  · calc
      Int.natAbs (x.1 - z.1) = Int.natAbs ((x.1 - y.1) + (y.1 - z.1)) := by
        congr 1; ring
      _ ≤ Int.natAbs (x.1 - y.1) + Int.natAbs (y.1 - z.1) := Int.natAbs_add_le _ _
      _ ≤ supDist x y + supDist y z := by
        exact Nat.add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc
      Int.natAbs (x.2 - z.2) = Int.natAbs ((x.2 - y.2) + (y.2 - z.2)) := by
        congr 1; ring
      _ ≤ Int.natAbs (x.2 - y.2) + Int.natAbs (y.2 - z.2) := Int.natAbs_add_le _ _
      _ ≤ supDist x y + supDist y z := by
        exact Nat.add_le_add (le_max_right _ _) (le_max_right _ _)

private lemma radialOffset_le_supDist_of_shell
    (y x z : Plane) (u : ℕ) (i : ℤ)
    (hz : (supDist z y : ℤ) = shellRadius u i) :
    radialOffset y u i x ≤ supDist x z := by
  unfold radialOffset
  rw [← hz]
  apply natAbs_sub_le_of_le_add
  · exact supDist_triangle x z y
  · calc
      supDist z y ≤ supDist z x + supDist x y := supDist_triangle z x y
      _ = supDist x z + supDist x y := by rw [supDist_comm z x]

private lemma squareDepth_le_add (a x z : Plane) (u : ℕ) :
    squareDepth a u x ≤ squareDepth a u z + (supDist x z : ℤ) := by
  unfold squareDepth
  have h₁ : supDist x a ≤ supDist x z + supDist z a := supDist_triangle x z a
  have h₂ : supDist z a ≤ supDist x z + supDist x a := by
    calc
      supDist z a ≤ supDist z x + supDist x a := supDist_triangle z x a
      _ = supDist x z + supDist x a := by rw [supDist_comm z x]
  have hq : (u : ℤ) + 1 - (supDist x a : ℤ) ≤
      (u : ℤ) + 1 - (supDist z a : ℤ) + (supDist x z : ℤ) := by omega
  have hd : 0 ≤ (supDist x z : ℤ) := by exact_mod_cast Nat.zero_le _
  apply max_le
  · linarith [le_max_left 0 ((u : ℤ) + 1 - (supDist z a : ℤ))]
  · linarith [hq, le_max_right 0 ((u : ℤ) + 1 - (supDist z a : ℤ))]

private lemma squareDepth_lipschitz (a x z : Plane) (u : ℕ) :
    |(squareDepth a u x : ℝ) - (squareDepth a u z : ℝ)| ≤ (supDist x z : ℝ) := by
  have h₁ := squareDepth_le_add a x z u
  have h₂ := squareDepth_le_add a z x u
  rw [supDist_comm z x] at h₂
  have h₁' : (squareDepth a u x : ℝ) ≤ squareDepth a u z + (supDist x z : ℝ) := by exact_mod_cast h₁
  have h₂' : (squareDepth a u z : ℝ) ≤ squareDepth a u x + (supDist x z : ℝ) := by exact_mod_cast h₂
  rw [abs_le]
  constructor <;> linarith

private lemma supDist_le_latticeDist (x z : Plane) :
    supDist x z ≤ latticeDist x z := by
  simp [supDist, latticeDist]

private lemma cutVolume_subset_square (a y : Plane) (u : ℕ) (i : ℤ) :
    cutVolume a y u i ⊆ square a u := by
  intro z hz
  have hz' : z ∈ farVolume a y u i := (Finset.mem_sdiff.mp hz).1
  exact (Finset.mem_filter.mp hz').1

private lemma shellSpacing_floor_gap (u : ℕ) (i : ℤ) :
    shellSpacing u - 1 ≤ (shellRadius u i : ℝ) - (i - 1 : ℝ) * shellSpacing u := by
  unfold shellRadius
  have hf := Int.lt_floor_add_one ((i : ℝ) * shellSpacing u)
  unfold shellSpacing at *
  linarith


private lemma natAbs_cast_real (z : ℤ) :
    (Int.natAbs z : ℝ) = |(z : ℝ)| := by
  by_cases hz : 0 ≤ z
  · have hn := Int.natAbs_of_nonneg hz
    rw [abs_of_nonneg (by exact_mod_cast hz)]
    have hnR : (Int.natAbs z : ℝ) = (z : ℝ) := by
      have h := congrArg (fun t : ℤ => (t : ℝ)) hn
      simpa using h
    exact hnR
  · have hn : 0 ≤ -z := by omega
    have heq : (Int.natAbs z : ℤ) = -z := by
      rw [← Int.natAbs_neg]
      exact Int.natAbs_of_nonneg hn
    rw [abs_of_nonpos (by exact_mod_cast (le_of_lt (lt_of_not_ge hz)))]
    have heqR : (Int.natAbs z : ℝ) = ((-z : ℤ) : ℝ) := by
      have h := congrArg (fun t : ℤ => (t : ℝ)) heq
      simpa using h
    simpa using heqR

private lemma supDist_cast_real (x z : Plane) :
    (supDist x z : ℝ) = max |(x.1 : ℝ) - z.1| |(x.2 : ℝ) - z.2| := by
  simp only [supDist, Nat.cast_max, natAbs_cast_real]
  norm_cast

private lemma squareDepth_pos_mem_square (a x : Plane) (u : ℕ)
    (h : 0 < squareDepth a u x) : x ∈ square a u := by
  have hq : (supDist x a : ℤ) ≤ (u : ℤ) := by
    unfold squareDepth at h
    have : 0 < max 0 ((u : ℤ) + 1 - (supDist x a : ℤ)) := h
    omega
  have hqn : supDist x a ≤ u := by exact_mod_cast hq
  have hx1n : Int.natAbs (x.1 - a.1) ≤ u := le_trans (Nat.le_max_left _ _) hqn
  have hx2n : Int.natAbs (x.2 - a.2) ≤ u := le_trans (Nat.le_max_right _ _) hqn
  have hx1 : |x.1 - a.1| ≤ (u : ℤ) := by
    have hc : (Int.natAbs (x.1 - a.1) : ℤ) ≤ (u : ℤ) := by exact_mod_cast hx1n
    simpa [Int.natCast_natAbs] using hc
  have hx2 : |x.2 - a.2| ≤ (u : ℤ) := by
    have hc : (Int.natAbs (x.2 - a.2) : ℤ) ≤ (u : ℤ) := by exact_mod_cast hx2n
    simpa [Int.natCast_natAbs] using hc
  have hx1' := abs_le.mp hx1
  have hx2' := abs_le.mp hx2
  apply Finset.mem_product.mpr
  constructor
  · apply Finset.mem_Icc.mpr
    constructor <;> omega
  · apply Finset.mem_Icc.mpr
    constructor <;> omega

private lemma outside_square_depth_le_supDist (a x z : Plane) (u : ℕ)
    (hx : 0 < squareDepth a u x) (hz : z ∉ square a u) :
    (squareDepth a u x : ℝ) ≤ (supDist x z : ℝ) := by
  have hxsq := squareDepth_pos_mem_square a x u hx
  have hqpos : 0 < (u : ℤ) + 1 - (supDist x a : ℤ) := by
    unfold squareDepth at hx
    omega
  have hInt : squareDepth a u x = (u : ℤ) + 1 - (supDist x a : ℤ) := by
    unfold squareDepth
    rw [max_eq_right (le_of_lt hqpos)]
  have hformula : (squareDepth a u x : ℝ) =
      (u : ℝ) + 1 - max |(x.1 : ℝ) - a.1| |(x.2 : ℝ) - a.2| := by
    rw [hInt]
    push_cast
    rw [supDist_cast_real]
  have hbranches : z.1 < a.1 - (u : ℤ) ∨ a.1 + u < z.1 ∨
      z.2 < a.2 - (u : ℤ) ∨ a.2 + u < z.2 := by
    by_contra hn
    push Not at hn
    apply hz
    have hprod : z ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + u) ×ˢ
        Finset.Icc (a.2 - (u : ℤ)) (a.2 + u) := by
      apply Finset.mem_product.mpr
      constructor <;> apply Finset.mem_Icc.mpr <;> omega
    simpa [square] using hprod
  have hxmem1 : a.1 - (u : ℤ) ≤ x.1 ∧ x.1 ≤ a.1 + u := by
    have hprod : x ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + u) ×ˢ
        Finset.Icc (a.2 - (u : ℤ)) (a.2 + u) := by simpa [square] using hxsq
    exact Finset.mem_Icc.mp (Finset.mem_product.mp hprod |>.1)
  have hxmem2 : a.2 - (u : ℤ) ≤ x.2 ∧ x.2 ≤ a.2 + u := by
    have hprod : x ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + u) ×ˢ
        Finset.Icc (a.2 - (u : ℤ)) (a.2 + u) := by simpa [square] using hxsq
    exact Finset.mem_Icc.mp (Finset.mem_product.mp hprod |>.2)
  have hx1abs : |x.1 - a.1| ≤ (u : ℤ) := by rw [abs_le]; omega
  have hx2abs : |x.2 - a.2| ≤ (u : ℤ) := by rw [abs_le]; omega
  rcases hbranches with hz1l | hz1r | hz2l | hz2r
  · have hz1lR : (z.1 : ℝ) ≤ a.1 - u - 1 := by
      have hi : z.1 ≤ a.1 - (u : ℤ) - 1 := by omega
      exact_mod_cast hi
    have hx1lR : (x.1 : ℝ) ≥ a.1 - u := by exact_mod_cast hxmem1.1
    have hcoord : |(x.1 : ℝ) - z.1| = (x.1 : ℝ) - z.1 := by
      rw [abs_of_nonneg (by linarith)]
    rw [hformula, supDist_cast_real, hcoord]
    have habs : |(x.1 : ℝ) - a.1| ≥ -((x.1 : ℝ) - a.1) := by
      simpa [abs_sub_comm] using le_abs_self (a.1 - (x.1 : ℝ))
    have hmax : max |(x.1 : ℝ) - a.1| |(x.2 : ℝ) - a.2| ≥ |(x.1 : ℝ) - a.1| := le_max_left _ _
    have hdistmax : (x.1 : ℝ) - z.1 ≤ max ((x.1 : ℝ) - z.1) |(x.2 : ℝ) - z.2| := le_max_left _ _
    linarith
  · have hz1rR : (z.1 : ℝ) ≥ a.1 + u + 1 := by
      have hi : a.1 + (u : ℤ) + 1 ≤ z.1 := by omega
      exact_mod_cast hi
    have hx1rR : (x.1 : ℝ) ≤ a.1 + u := by exact_mod_cast hxmem1.2
    have hcoord : |(x.1 : ℝ) - z.1| = (z.1 : ℝ) - x.1 := by
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [hformula, supDist_cast_real, hcoord]
    have habs : |(x.1 : ℝ) - a.1| ≥ (x.1 : ℝ) - a.1 := le_abs_self _
    have hmax : max |(x.1 : ℝ) - a.1| |(x.2 : ℝ) - a.2| ≥ |(x.1 : ℝ) - a.1| := le_max_left _ _
    have hdistmax : (z.1 : ℝ) - x.1 ≤ max ((z.1 : ℝ) - x.1) |(x.2 : ℝ) - z.2| := le_max_left _ _
    linarith
  · have hz2lR : (z.2 : ℝ) ≤ a.2 - u - 1 := by
      have hi : z.2 ≤ a.2 - (u : ℤ) - 1 := by omega
      exact_mod_cast hi
    have hx2lR : (x.2 : ℝ) ≥ a.2 - u := by exact_mod_cast hxmem2.1
    have hcoord : |(x.2 : ℝ) - z.2| = (x.2 : ℝ) - z.2 := by
      rw [abs_of_nonneg (by linarith)]
    rw [hformula, supDist_cast_real, hcoord]
    have habs : |(x.2 : ℝ) - a.2| ≥ -((x.2 : ℝ) - a.2) := by
      simpa [abs_sub_comm] using le_abs_self (a.2 - (x.2 : ℝ))
    have hmax : max |(x.1 : ℝ) - a.1| |(x.2 : ℝ) - a.2| ≥ |(x.2 : ℝ) - a.2| := le_max_right _ _
    have hdistmax : (x.2 : ℝ) - z.2 ≤ max |(x.1 : ℝ) - z.1| ((x.2 : ℝ) - z.2) := le_max_right _ _
    linarith
  · have hz2rR : (z.2 : ℝ) ≥ a.2 + u + 1 := by
      have hi : a.2 + (u : ℤ) + 1 ≤ z.2 := by omega
      exact_mod_cast hi
    have hx2rR : (x.2 : ℝ) ≤ a.2 + u := by exact_mod_cast hxmem2.2
    have hcoord : |(x.2 : ℝ) - z.2| = (z.2 : ℝ) - x.2 := by
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [hformula, supDist_cast_real, hcoord]
    have habs : |(x.2 : ℝ) - a.2| ≥ (x.2 : ℝ) - a.2 := le_abs_self _
    have hmax : max |(x.1 : ℝ) - a.1| |(x.2 : ℝ) - a.2| ≥ |(x.2 : ℝ) - a.2| := le_max_right _ _
    have hdistmax : (z.2 : ℝ) - x.2 ≤ max |(x.1 : ℝ) - z.1| ((z.2 : ℝ) - x.2) := le_max_right _ _
    linarith

private lemma square_depth_positive_of_mem_square (a x : Plane) (u : ℕ)
    (hx : x ∈ square a u) : 0 < squareDepth a u x := by
  have hprod : x ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + u) ×ˢ
      Finset.Icc (a.2 - (u : ℤ)) (a.2 + u) := by simpa [square] using hx
  have hx1 := Finset.mem_Icc.mp (Finset.mem_product.mp hprod).1
  have hx2 := Finset.mem_Icc.mp (Finset.mem_product.mp hprod).2
  have h1 : |x.1 - a.1| ≤ (u : ℤ) := by rw [abs_le]; omega
  have h2 : |x.2 - a.2| ≤ (u : ℤ) := by rw [abs_le]; omega
  have h1n : Int.natAbs (x.1 - a.1) ≤ u := by
    have hc : (Int.natAbs (x.1 - a.1) : ℤ) ≤ (u : ℤ) := by
      simpa [Int.natCast_natAbs] using h1
    exact_mod_cast hc
  have h2n : Int.natAbs (x.2 - a.2) ≤ u := by
    have hc : (Int.natAbs (x.2 - a.2) : ℤ) ≤ (u : ℤ) := by
      simpa [Int.natCast_natAbs] using h2
    exact_mod_cast hc
  have hq : supDist x a ≤ u := by
    unfold supDist
    exact max_le h1n h2n
  unfold squareDepth
  have hq' : (supDist x a : ℤ) ≤ (u : ℤ) := by exact_mod_cast hq
  rw [max_eq_right (show 0 ≤ (u : ℤ) + 1 - (supDist x a : ℤ) by omega)]
  omega

private lemma exists_outside_square_at_depth (a x : Plane) (u : ℕ)
    (hx : x ∈ square a u) :
    ∃ z, z ∉ square a u ∧ supDist x z = u + 1 - supDist x a := by
  have hprod : x ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + u) ×ˢ
      Finset.Icc (a.2 - (u : ℤ)) (a.2 + u) := by simpa [square] using hx
  have hx1 := Finset.mem_Icc.mp (Finset.mem_product.mp hprod).1
  have hx2 := Finset.mem_Icc.mp (Finset.mem_product.mp hprod).2
  have hq : supDist x a ≤ u := by
    have h1 : |x.1 - a.1| ≤ (u : ℤ) := by rw [abs_le]; omega
    have h2 : |x.2 - a.2| ≤ (u : ℤ) := by rw [abs_le]; omega
    have h1n : Int.natAbs (x.1 - a.1) ≤ u := by
      have hc : (Int.natAbs (x.1 - a.1) : ℤ) ≤ (u : ℤ) := by
        simpa [Int.natCast_natAbs] using h1
      exact_mod_cast hc
    have h2n : Int.natAbs (x.2 - a.2) ≤ u := by
      have hc : (Int.natAbs (x.2 - a.2) : ℤ) ≤ (u : ℤ) := by
        simpa [Int.natCast_natAbs] using h2
      exact_mod_cast hc
    unfold supDist
    exact max_le h1n h2n
  by_cases haxis : Int.natAbs (x.2 - a.2) ≤ Int.natAbs (x.1 - a.1)
  · have hqeq : supDist x a = Int.natAbs (x.1 - a.1) := by
      unfold supDist
      exact max_eq_left haxis
    by_cases hsign : 0 ≤ x.1 - a.1
    · let z : Plane := (a.1 + (u : ℤ) + 1, x.2)
      have hz : z ∉ square a u := by
        intro hm
        have hp : z ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + u) ×ˢ
            Finset.Icc (a.2 - (u : ℤ)) (a.2 + u) := by simpa [square] using hm
        have hb := Finset.mem_Icc.mp (Finset.mem_product.mp hp).1
        dsimp [z] at hb
        omega
      have hqint : (supDist x a : ℤ) = x.1 - a.1 := by
        rw [hqeq]
        exact Int.natAbs_of_nonneg hsign
      have hdiff : x.1 - (a.1 + (u : ℤ) + 1) = -((u + 1 - supDist x a : ℕ) : ℤ) := by
        rw [Nat.cast_sub (by omega : supDist x a ≤ u + 1)]
        push_cast
        rw [hqint]
        ring
      refine ⟨z, hz, ?_⟩
      simp [supDist, z, hdiff, Int.natAbs_neg]
    · have hsign' : x.1 - a.1 < 0 := by omega
      let z : Plane := (a.1 - (u : ℤ) - 1, x.2)
      have hz : z ∉ square a u := by
        intro hm
        have hp : z ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + u) ×ˢ
            Finset.Icc (a.2 - (u : ℤ)) (a.2 + u) := by simpa [square] using hm
        have hb := Finset.mem_Icc.mp (Finset.mem_product.mp hp).1
        dsimp [z] at hb
        omega
      have hqint : (supDist x a : ℤ) = -(x.1 - a.1) := by
        rw [hqeq, ← Int.natAbs_neg]
        exact Int.natAbs_of_nonneg (by omega)
      have hdiff : x.1 - (a.1 - (u : ℤ) - 1) = ((u + 1 - supDist x a : ℕ) : ℤ) := by
        rw [Nat.cast_sub (by omega : supDist x a ≤ u + 1)]
        push_cast
        rw [hqint]
        ring
      refine ⟨z, hz, ?_⟩
      simp [supDist, z, hdiff]
  · have haxis' : Int.natAbs (x.1 - a.1) ≤ Int.natAbs (x.2 - a.2) := by omega
    have hqeq : supDist x a = Int.natAbs (x.2 - a.2) := by
      unfold supDist
      exact max_eq_right haxis'
    by_cases hsign : 0 ≤ x.2 - a.2
    · let z : Plane := (x.1, a.2 + (u : ℤ) + 1)
      have hz : z ∉ square a u := by
        intro hm
        have hp : z ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + u) ×ˢ
            Finset.Icc (a.2 - (u : ℤ)) (a.2 + u) := by simpa [square] using hm
        have hb := Finset.mem_Icc.mp (Finset.mem_product.mp hp).2
        dsimp [z] at hb
        omega
      have hqint : (supDist x a : ℤ) = x.2 - a.2 := by
        rw [hqeq]
        exact Int.natAbs_of_nonneg hsign
      have hdiff : x.2 - (a.2 + (u : ℤ) + 1) = -((u + 1 - supDist x a : ℕ) : ℤ) := by
        rw [Nat.cast_sub (by omega : supDist x a ≤ u + 1)]
        push_cast
        rw [hqint]
        ring
      refine ⟨z, hz, ?_⟩
      simp [supDist, z, hdiff, Int.natAbs_neg]
    · let z : Plane := (x.1, a.2 - (u : ℤ) - 1)
      have hz : z ∉ square a u := by
        intro hm
        have hp : z ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + u) ×ˢ
            Finset.Icc (a.2 - (u : ℤ)) (a.2 + u) := by simpa [square] using hm
        have hb := Finset.mem_Icc.mp (Finset.mem_product.mp hp).2
        dsimp [z] at hb
        omega
      have hqint : (supDist x a : ℤ) = -(x.2 - a.2) := by
        rw [hqeq, ← Int.natAbs_neg]
        exact Int.natAbs_of_nonneg (by omega)
      have hdiff : x.2 - (a.2 - (u : ℤ) - 1) = ((u + 1 - supDist x a : ℕ) : ℤ) := by
        rw [Nat.cast_sub (by omega : supDist x a ≤ u + 1)]
        push_cast
        rw [hqint]
        ring
      refine ⟨z, hz, ?_⟩
      simp [supDist, z, hdiff]

private lemma window_depth_ge_65 (a y : Plane) (u : ℕ) (i : ℤ)
    {w : Plane} (hw : w ∈ window a y u 64 i) :
    65 ≤ squareDepth a u w := by
  have hwShell : w ∈ shell a y u i := (Finset.mem_sdiff.mp hw).1
  have hnotNear : w ∉ nearShell a y u 64 i := (Finset.mem_sdiff.mp hw).2
  have hwsq : w ∈ square a u := (Finset.mem_filter.mp hwShell).1
  have hdepthPos := square_depth_positive_of_mem_square a w u hwsq
  obtain ⟨z, hz, hdist⟩ := exists_outside_square_at_depth a w u hwsq
  have hdepthInt : squareDepth a u w = (u : ℤ) + 1 - (supDist w a : ℤ) := by
    have hq : supDist w a ≤ u := by
      have hq' : (supDist w a : ℤ) ≤ (u : ℤ) := by
        unfold squareDepth at hdepthPos
        omega
      exact_mod_cast hq'
    unfold squareDepth
    rw [max_eq_right (show 0 ≤ (u : ℤ) + 1 - (supDist w a : ℤ) by omega)]
  have hdepthNat : (squareDepth a u w).toNat = u + 1 - supDist w a := by
    have hq : supDist w a ≤ u := by
      have hq' : (supDist w a : ℤ) ≤ (u : ℤ) := by
        unfold squareDepth at hdepthPos
        omega
      exact_mod_cast hq'
    have hcast : ((squareDepth a u w).toNat : ℤ) =
        ((u + 1 - supDist w a : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (le_of_lt hdepthPos), hdepthInt]
      rw [Nat.cast_sub (by omega : supDist w a ≤ u + 1)]
      push_cast
      ring
    exact_mod_cast hcast
  have hsetle : setDistance supDist w {z | z ∉ square a u} ≤
      ((squareDepth a u w).toNat : ℕ∞) := by
    unfold setDistance
    apply iInf_le_of_le ⟨z, hz⟩
    simp [hdist, hdepthNat]
  have hnotdist : ¬ setDistance supDist w {z | z ∉ square a u} ≤ (64 : ℕ∞) := by
    intro hd
    apply hnotNear
    exact Finset.mem_filter.mpr ⟨hwShell, hd⟩
  by_contra hn
  have hdepthLE : squareDepth a u w ≤ 64 := by omega
  have hnatLE : (squareDepth a u w).toNat ≤ 64 := by
    have hcast := Int.toNat_of_nonneg (le_of_lt hdepthPos)
    have hle : ((squareDepth a u w).toNat : ℤ) ≤ 64 := by
      rw [hcast]
      exact_mod_cast hdepthLE
    exact_mod_cast hle
  have hleENat : ((squareDepth a u w).toNat : ℕ∞) ≤ (64 : ℕ∞) := by exact_mod_cast hnatLE
  exact hnotdist (le_trans hsetle hleENat)

private lemma radial_radius_lower (y : Plane) (u : ℕ) (i : ℤ) (x : Plane) :
    (shellRadius u i : ℝ) - (radialOffset y u i x : ℝ) ≤
      (supDist x y : ℝ) := by
  have heq : Int.natAbs ((supDist x y : ℤ) - shellRadius u i) =
      radialOffset y u i x := by rfl
  rcases Int.natAbs_eq_iff.mp heq with h | h
  · have hR : (supDist x y : ℝ) - shellRadius u i = radialOffset y u i x := by
      exact_mod_cast h
    linarith
  · have hR : (supDist x y : ℝ) - shellRadius u i = -(radialOffset y u i x : ℝ) := by
      exact_mod_cast h
    linarith

private lemma distance_obstruction_pointwise (a y : Plane) (u : ℕ) (i : ℤ)
    (x z : Plane) (hz : z ∉ cutVolume a y u i) :
    min (max (radialOffset y u i x : ℝ) (65 - (squareDepth a u x : ℝ)))
      (min (squareDepth a u x : ℝ)
        (shellSpacing u - 1 - (radialOffset y u i x : ℝ))) ≤
      (latticeDist x z : ℝ) := by
  by_cases hw : z ∈ window a y u 64 i
  · have hzShell : z ∈ shell a y u i := (Finset.mem_sdiff.mp hw).1
    have hzRadius : (supDist z y : ℤ) = shellRadius u i :=
      (Finset.mem_filter.mp hzShell).2
    have hradN := radialOffset_le_supDist_of_shell y x z u i hzRadius
    have hrad : (radialOffset y u i x : ℝ) ≤ (supDist x z : ℝ) := by exact_mod_cast hradN
    have hwindowDepth := window_depth_ge_65 a y u i hw
    have hwindowDepthR : (65 : ℝ) ≤ (squareDepth a u z : ℝ) := by exact_mod_cast hwindowDepth
    have hlip := squareDepth_lipschitz a x z u
    have hdep : 65 - (squareDepth a u x : ℝ) ≤ (supDist x z : ℝ) := by
      have hl := (abs_le.mp hlip).1
      linarith
    calc
      min (max (radialOffset y u i x : ℝ) (65 - (squareDepth a u x : ℝ)))
          (min (squareDepth a u x : ℝ)
            (shellSpacing u - 1 - (radialOffset y u i x : ℝ)))
          ≤ max (radialOffset y u i x : ℝ) (65 - (squareDepth a u x : ℝ)) := min_le_left _ _
      _ ≤ (supDist x z : ℝ) := max_le hrad hdep
      _ ≤ (latticeDist x z : ℝ) := by exact_mod_cast supDist_le_latticeDist x z
  · have hznotFar : z ∉ farVolume a y u i := by
      have hnot : z ∉ farVolume a y u i \ window a y u 64 i := by
        simpa [cutVolume] using hz
      intro hF
      exact hnot (Finset.mem_sdiff.mpr ⟨hF, hw⟩)
    by_cases hzSquare : z ∈ square a u
    · have hcond : ¬ ((i : ℝ) - 1) * shellSpacing u < (supDist z y : ℝ) := by
        intro hc
        apply hznotFar
        exact Finset.mem_filter.mpr ⟨hzSquare, hc⟩
      have hradZ : (supDist z y : ℝ) ≤ ((i : ℝ) - 1) * shellSpacing u := le_of_not_gt hcond
      have hradX := radial_radius_lower y u i x
      have hgap := shellSpacing_floor_gap u i
      have htriN := supDist_triangle x z y
      have htri : (supDist x y : ℝ) ≤ (supDist x z : ℝ) + (supDist z y : ℝ) := by
        exact_mod_cast htriN
      have hthird : shellSpacing u - 1 - (radialOffset y u i x : ℝ) ≤
          (supDist x z : ℝ) := by linarith
      calc
        min (max (radialOffset y u i x : ℝ) (65 - (squareDepth a u x : ℝ)))
            (min (squareDepth a u x : ℝ)
              (shellSpacing u - 1 - (radialOffset y u i x : ℝ)))
            ≤ min (squareDepth a u x : ℝ)
                (shellSpacing u - 1 - (radialOffset y u i x : ℝ)) := min_le_right _ _
        _ ≤ shellSpacing u - 1 - (radialOffset y u i x : ℝ) := min_le_right _ _
        _ ≤ (supDist x z : ℝ) := hthird
        _ ≤ (latticeDist x z : ℝ) := by exact_mod_cast supDist_le_latticeDist x z
    · have hdepthN : 0 ≤ squareDepth a u x := by
        unfold squareDepth
        exact le_max_left _ _
      have hdepth : squareDepth a u x ≤ (supDist x z : ℝ) := by
        by_cases hp : 0 < squareDepth a u x
        · exact_mod_cast outside_square_depth_le_supDist a x z u hp hzSquare
        · have hzero : squareDepth a u x = 0 := by omega
          simp [hzero]
      calc
        min (max (radialOffset y u i x : ℝ) (65 - (squareDepth a u x : ℝ)))
            (min (squareDepth a u x : ℝ)
              (shellSpacing u - 1 - (radialOffset y u i x : ℝ)))
            ≤ min (squareDepth a u x : ℝ)
                (shellSpacing u - 1 - (radialOffset y u i x : ℝ)) := min_le_right _ _
        _ ≤ (squareDepth a u x : ℝ) := min_le_left _ _
        _ ≤ (supDist x z : ℝ) := hdepth
        _ ≤ (latticeDist x z : ℝ) := by exact_mod_cast supDist_le_latticeDist x z

private lemma obstruction_le_boundaryDepth (a y : Plane) (u : ℕ) (i : ℤ)
    (x : Plane) :
    min (max (radialOffset y u i x : ℝ) (65 - (squareDepth a u x : ℝ)))
      (min (squareDepth a u x : ℝ)
        (shellSpacing u - 1 - (radialOffset y u i x : ℝ))) ≤
      ((boundaryDepth (cutVolume a y u i) x).toNat : ℝ) := by
  let b := min (max (radialOffset y u i x : ℝ) (65 - (squareDepth a u x : ℝ)))
      (min (squareDepth a u x : ℝ)
        (shellSpacing u - 1 - (radialOffset y u i x : ℝ)))
  let n := Nat.ceil b
  have hn : ∀ z, z ∉ cutVolume a y u i → n ≤ latticeDist x z := by
    intro z hz
    apply Nat.ceil_le.mpr
    exact distance_obstruction_pointwise a y u i x z hz
  have hInf : (n : ℕ∞) ≤ boundaryDepth (cutVolume a y u i) x := by
    unfold boundaryDepth setDistance
    apply le_iInf
    intro z
    exact_mod_cast hn z.val z.property
  let z₀ : Plane := (a.1 + (u : ℤ) + 1, a.2)
  have hz₀sq : z₀ ∉ square a u := by
    intro hs
    have hp : z₀ ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + u) ×ˢ
        Finset.Icc (a.2 - (u : ℤ)) (a.2 + u) := by simpa [square] using hs
    have hb := Finset.mem_Icc.mp (Finset.mem_product.mp hp).1
    dsimp [z₀] at hb
    omega
  have hz₀ : z₀ ∉ cutVolume a y u i := by
    intro hv
    exact hz₀sq (cutVolume_subset_square a y u i hv)
  have hle : boundaryDepth (cutVolume a y u i) x ≤ (latticeDist x z₀ : ℕ∞) := by
    unfold boundaryDepth setDistance
    exact iInf_le_of_le ⟨z₀, hz₀⟩ le_rfl
  have hfinite : boundaryDepth (cutVolume a y u i) x ≠ ⊤ := by
    intro ht
    simp [ht] at hle
  have hnNat : n ≤ (boundaryDepth (cutVolume a y u i) x).toNat := by
    have h := ENat.toNat_le_toNat hInf hfinite
    simpa using h
  change b ≤ ((boundaryDepth (cutVolume a y u i) x).toNat : ℝ)
  calc
    b ≤ (n : ℝ) := Nat.le_ceil _
    _ ≤ ((boundaryDepth (cutVolume a y u i) x).toNat : ℝ) := by exact_mod_cast hnNat


theorem main : RawDistanceObstructionsStatement := by
  intro a y u i hsetup x hx
  exact obstruction_le_boundaryDepth a y u i x

#print axioms main

end AKLT.W.WIN038
