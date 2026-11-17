module
public import AKLT.Blueprint.Win.NodesTaper

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN036

private lemma spacing_ge_390 {u : ℕ} (hu : geometryThreshold 64 ≤ u) :
    390 ≤ shellSpacing u := by
  have hu' : 390 ^ 4 ≤ u := by simpa [geometryThreshold] using hu
  have huR : (390 : ℝ) ^ 4 ≤ (u : ℝ) := by exact_mod_cast hu'
  have h1 : (390 : ℝ) ^ 2 ≤ Real.sqrt (u : ℝ) := by
    apply (Real.le_sqrt (by positivity) (by positivity : 0 ≤ (u : ℝ))).2
    nlinarith [huR]
  have h2 : (390 : ℝ) ≤ Real.sqrt (Real.sqrt (u : ℝ)) :=
    (Real.le_sqrt (by positivity) (Real.sqrt_nonneg _)).2 h1
  simpa [shellSpacing] using h2

private lemma supDist_triangle (x y z : Plane) :
    supDist x z ≤ supDist x y + supDist y z := by
  unfold supDist
  apply Nat.max_le.mpr
  constructor
  · have h := Int.natAbs_add_le (x.1 - y.1) (y.1 - z.1)
    have he : x.1 - z.1 = (x.1 - y.1) + (y.1 - z.1) := by omega
    rw [he]
    calc
      ((x.1 - y.1) + (y.1 - z.1)).natAbs ≤
          (x.1 - y.1).natAbs + (y.1 - z.1).natAbs := h
      _ ≤ max (x.1 - y.1).natAbs (x.2 - y.2).natAbs +
          max (y.1 - z.1).natAbs (y.2 - z.2).natAbs := by omega
  · have h := Int.natAbs_add_le (x.2 - y.2) (y.2 - z.2)
    have he : x.2 - z.2 = (x.2 - y.2) + (y.2 - z.2) := by omega
    rw [he]
    calc
      ((x.2 - y.2) + (y.2 - z.2)).natAbs ≤
          (x.2 - y.2).natAbs + (y.2 - z.2).natAbs := h
      _ ≤ max (x.1 - y.1).natAbs (x.2 - y.2).natAbs +
          max (y.1 - z.1).natAbs (y.2 - z.2).natAbs := by omega

private lemma supDist_comm (x y : Plane) : supDist x y = supDist y x := by
  unfold supDist
  rw [show x.1 - y.1 = -(y.1 - x.1) by omega, Int.natAbs_neg,
    show x.2 - y.2 = -(y.2 - x.2) by omega, Int.natAbs_neg]

private lemma supDist_adj_le_one {x y : Plane} (h : Adjacent x y) :
    supDist x y ≤ 1 := by
  have h' : (x.1 - y.1).natAbs + (x.2 - y.2).natAbs = 1 := h
  unfold supDist
  omega

private lemma squareDepth_le_formula {a z : Plane} {u : ℕ}
    (hz : z ∈ square a u) :
    squareDepth a u z = (u : ℤ) + 1 - (supDist z a : ℤ) := by
  have hz' : z.1 ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + u) ∧
      z.2 ∈ Finset.Icc (a.2 - (u : ℤ)) (a.2 + u) := by
    change z ∈ Finset.Icc _ _ ×ˢ Finset.Icc _ _ at hz
    rw [Finset.mem_product] at hz
    exact hz
  simp only [Finset.mem_Icc] at hz'
  rcases hz' with ⟨⟨hz1l, hz1u⟩, ⟨hz2l, hz2u⟩⟩
  have h1 : |z.1 - a.1| ≤ (u : ℤ) := by
    apply abs_le.mpr
    constructor <;> omega
  have h2 : |z.2 - a.2| ≤ (u : ℤ) := by
    apply abs_le.mpr
    constructor <;> omega
  have h1' : (z.1 - a.1).natAbs ≤ u := by
    have hc : ((z.1 - a.1).natAbs : ℤ) ≤ (u : ℤ) := by
      simpa [Int.natCast_natAbs] using h1
    exact_mod_cast hc
  have h2' : (z.2 - a.2).natAbs ≤ u := by
    have hc : ((z.2 - a.2).natAbs : ℤ) ≤ (u : ℤ) := by
      simpa [Int.natCast_natAbs] using h2
    exact_mod_cast hc
  have hd : supDist z a ≤ u := by
    unfold supDist
    exact Nat.max_le.mpr ⟨h1', h2'⟩
  unfold squareDepth
  have hnonneg : 0 ≤ (u : ℤ) + 1 - (supDist z a : ℤ) := by omega
  rw [max_eq_right hnonneg]

private lemma supDist_le_of_square {a z : Plane} {u : ℕ}
    (hz : z ∈ square a u) : supDist z a ≤ u := by
  have hz' : z.1 ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + u) ∧
      z.2 ∈ Finset.Icc (a.2 - (u : ℤ)) (a.2 + u) := by
    change z ∈ Finset.Icc _ _ ×ˢ Finset.Icc _ _ at hz
    rw [Finset.mem_product] at hz
    exact hz
  simp only [Finset.mem_Icc] at hz'
  rcases hz' with ⟨⟨hz1l, hz1u⟩, ⟨hz2l, hz2u⟩⟩
  have h1 : |z.1 - a.1| ≤ (u : ℤ) := by
    apply abs_le.mpr
    constructor <;> omega
  have h2 : |z.2 - a.2| ≤ (u : ℤ) := by
    apply abs_le.mpr
    constructor <;> omega
  have h1c : ((z.1 - a.1).natAbs : ℤ) ≤ (u : ℤ) := by
    simpa [Int.natCast_natAbs] using h1
  have h2c : ((z.2 - a.2).natAbs : ℤ) ≤ (u : ℤ) := by
    simpa [Int.natCast_natAbs] using h2
  have h1n : (z.1 - a.1).natAbs ≤ u := by exact_mod_cast h1c
  have h2n : (z.2 - a.2).natAbs ≤ u := by exact_mod_cast h2c
  unfold supDist
  exact Nat.max_le.mpr ⟨h1n, h2n⟩

private lemma square_of_positive_depth {a z : Plane} {u : ℕ}
    (hz : 1 ≤ squareDepth a u z) : z ∈ square a u := by
  have hd : (supDist z a : ℤ) ≤ (u : ℤ) := by
    unfold squareDepth at hz
    omega
  have hdNat : supDist z a ≤ u := by exact_mod_cast hd
  have h1n : (z.1 - a.1).natAbs ≤ u :=
    (Nat.le_max_left _ _).trans hdNat
  have h2n : (z.2 - a.2).natAbs ≤ u :=
    (Nat.le_max_right _ _).trans hdNat
  have h1cast : ((z.1 - a.1).natAbs : ℤ) ≤ (u : ℤ) := by exact_mod_cast h1n
  have h2cast : ((z.2 - a.2).natAbs : ℤ) ≤ (u : ℤ) := by exact_mod_cast h2n
  have h1 : |z.1 - a.1| ≤ (u : ℤ) := by simpa [Int.natCast_natAbs] using h1cast
  have h2 : |z.2 - a.2| ≤ (u : ℤ) := by simpa [Int.natCast_natAbs] using h2cast
  have hz1 := abs_le.mp h1
  have hz2 := abs_le.mp h2
  change z ∈ Finset.Icc _ _ ×ˢ Finset.Icc _ _
  rw [Finset.mem_product]
  simp only [Finset.mem_Icc]
  constructor <;> omega

private lemma depth_close {a x z : Plane} {u d : ℕ}
    (hclose : supDist x z ≤ d) :
    squareDepth a u x ≤ squareDepth a u z + (d : ℤ) := by
  have htri : supDist z a ≤ supDist z x + supDist x a := supDist_triangle z x a
  have hclose' : supDist z x ≤ d := by simpa [supDist_comm] using hclose
  have htriNat : supDist z a ≤ supDist x a + d := by
    calc
      supDist z a ≤ supDist z x + supDist x a := htri
      _ ≤ d + supDist x a := Nat.add_le_add_right hclose' _
      _ = supDist x a + d := Nat.add_comm _ _
  have htri' : (supDist z a : ℤ) ≤ (supDist x a : ℤ) + (d : ℤ) := by exact_mod_cast htriNat
  have harg : (u : ℤ) + 1 - (supDist x a : ℤ) ≤
      (u : ℤ) + 1 - (supDist z a : ℤ) + (d : ℤ) := by linarith
  unfold squareDepth
  apply max_le_iff.mpr
  constructor
  · exact add_nonneg (le_max_left 0 _) (Int.natCast_nonneg d)
  · calc
      (u : ℤ) + 1 - (supDist x a : ℤ) ≤
          (u : ℤ) + 1 - (supDist z a : ℤ) + (d : ℤ) := harg
      _ ≤ max 0 ((u : ℤ) + 1 - (supDist z a : ℤ)) + (d : ℤ) := by
        gcongr
        exact le_max_right 0 _

private lemma supDist_starBall_le_one {x y : Plane} (h : x ∈ starBall y) :
    supDist x y ≤ 1 := by
  have h' : x.1 ∈ Finset.Icc (y.1 - 1) (y.1 + 1) ∧
      x.2 ∈ Finset.Icc (y.2 - 1) (y.2 + 1) := by
    change x ∈ Finset.Icc _ _ ×ˢ Finset.Icc _ _ at h
    rw [Finset.mem_product] at h
    simpa only [Finset.mem_Icc] using h
  simp only [Finset.mem_Icc] at h'
  rcases h' with ⟨⟨hx₁, hx₂⟩, ⟨hy₁, hy₂⟩⟩
  have hx : |x.1 - y.1| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> omega
  have hy : |x.2 - y.2| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> omega
  have hx' : (x.1 - y.1).natAbs ≤ 1 := by
    have hc : ((x.1 - y.1).natAbs : ℤ) ≤ 1 := by simpa [Int.natCast_natAbs] using hx
    exact_mod_cast hc
  have hy' : (x.2 - y.2).natAbs ≤ 1 := by
    have hc : ((x.2 - y.2).natAbs : ℤ) ≤ 1 := by simpa [Int.natCast_natAbs] using hy
    exact_mod_cast hc
  unfold supDist
  exact Nat.max_le.mpr ⟨hx', hy'⟩

private lemma radial_margin {y z : Plane} {u : ℕ} {i : ℤ}
    (ht : (radialOffset y u i z : ℝ) ≤ shellSpacing u / 12) :
    ((i : ℝ) - 1) * shellSpacing u + (11 * shellSpacing u / 12 - 1) <
      (supDist z y : ℝ) := by
  have hrad : |(supDist z y : ℤ) - shellRadius u i| ≤ shellSpacing u / 12 := by
    have heq : (radialOffset y u i z : ℝ) =
        |(supDist z y : ℤ) - shellRadius u i| := by
      simp [radialOffset, Int.natCast_natAbs]
    rw [← heq]
    exact ht
  have hfloor : ((i : ℝ) * shellSpacing u) - 1 < (shellRadius u i : ℝ) := by
    simpa [shellRadius] using Int.sub_one_lt_floor ((i : ℝ) * shellSpacing u)
  have hlow : (shellRadius u i : ℝ) - shellSpacing u / 12 ≤ (supDist z y : ℝ) := by
    have hradReal : |(supDist z y : ℝ) - (shellRadius u i : ℝ)| ≤ shellSpacing u / 12 := by
      simpa [Int.cast_abs, Int.cast_sub] using hrad
    have hh := (abs_sub_le_iff (G := ℝ)).mp hradReal
    linarith
  linarith

private lemma far_of_close_taper {a y z w : Plane} {u : ℕ} {i : ℤ}
    (hspacing : 390 ≤ shellSpacing u) (hz : z ∈ taper a y u i)
    (hclose : supDist z w ≤ 1) : w ∈ farVolume a y u i := by
  classical
  have hz' : z ∈ square a u ∧
      (radialOffset y u i z : ℝ) ≤ shellSpacing u / 12 ∧
      (radialOffset y u i z : ℤ) + 32 ≤ squareDepth a u z := by
    simpa [taper] using hz
  rcases hz' with ⟨_, hrad, hdepth⟩
  have hdepthZ : 32 ≤ squareDepth a u z := by
    have hnonneg : 0 ≤ (radialOffset y u i z : ℤ) := Int.natCast_nonneg _
    omega
  have hdepthW : 31 ≤ squareDepth a u w := by
    have hclose' := depth_close (a := a) (u := u) (x := z) (z := w) hclose
    omega
  have hwSquare : w ∈ square a u := square_of_positive_depth (by omega)
  have hradZ := radial_margin hrad
  have htri : supDist z y ≤ supDist z w + supDist w y := supDist_triangle z w y
  have htriReal : (supDist z y : ℝ) ≤ 1 + (supDist w y : ℝ) := by
    have htriNat : supDist z y ≤ 1 + supDist w y := by omega
    exact_mod_cast htriNat
  have hmargin : 1 < 11 * shellSpacing u / 12 - 1 := by nlinarith [hspacing]
  have hradW : ((i : ℝ) - 1) * shellSpacing u < (supDist w y : ℝ) := by
    linarith
  simpa [farVolume, hwSquare, hradW]

private lemma distance_le_depth {a x : Plane} {u : ℕ}
    (hx : x ∈ square a u) :
    setDistance supDist x {z | z ∉ square a u} ≤
      (squareDepth a u x).toNat := by
  classical
  have hdepth := squareDepth_le_formula hx
  have hx' : x.1 ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + u) ∧
      x.2 ∈ Finset.Icc (a.2 - (u : ℤ)) (a.2 + u) := by
    change x ∈ Finset.Icc _ _ ×ˢ Finset.Icc _ _ at hx
    rw [Finset.mem_product] at hx
    exact hx
  simp only [Finset.mem_Icc] at hx'
  have hdx : |x.1 - a.1| ≤ (u : ℤ) := by
    have hx'' := hx'
    rcases hx'' with ⟨⟨hl, hu⟩, _⟩
    apply abs_le.mpr
    constructor <;> omega
  rcases hx' with ⟨_, ⟨hl2, hu2⟩⟩
  have hdy : |x.2 - a.2| ≤ (u : ℤ) := by
    apply abs_le.mpr
    constructor <;> omega
  let dx : ℤ := x.1 - a.1
  let dy : ℤ := x.2 - a.2
  let qx : Plane := (if 0 ≤ dx then a.1 + (u : ℤ) + 1 else a.1 - (u : ℤ) - 1, x.2)
  let qy : Plane := (x.1, if 0 ≤ dy then a.2 + (u : ℤ) + 1 else a.2 - (u : ℤ) - 1)
  have hqx : qx ∉ square a u := by
    change ¬ (qx ∈ Finset.Icc _ _ ×ˢ Finset.Icc _ _)
    rw [Finset.mem_product]
    simp only [Finset.mem_Icc]
    by_cases hs : 0 ≤ dx <;> simp [qx, hs, Finset.mem_Icc] <;> omega
  have hqy : qy ∉ square a u := by
    change ¬ (qy ∈ Finset.Icc _ _ ×ˢ Finset.Icc _ _)
    rw [Finset.mem_product]
    simp only [Finset.mem_Icc]
    by_cases hs : 0 ≤ dy <;> simp [qy, hs, Finset.mem_Icc] <;> omega
  have hdistx : supDist x qx = ((u : ℤ) + 1 - |dx|).toNat := by
    by_cases hs : 0 ≤ dx
    · have hp : 0 ≤ (u : ℤ) + 1 - dx := by omega
      have hval : x.1 - qx.1 = -((u : ℤ) + 1 - dx) := by simp [qx, dx, hs]; omega
      have hn : (x.1 - qx.1).natAbs = ((u : ℤ) + 1 - dx).toNat := by
        rw [hval, Int.natAbs_neg]
        have hc : (((u : ℤ) + 1 - dx).natAbs : ℤ) = (((u : ℤ) + 1 - dx).toNat : ℤ) := by
          rw [Int.natAbs_of_nonneg hp, Int.toNat_of_nonneg hp]
        exact_mod_cast hc
      have hzero : (x.2 - qx.2).natAbs = 0 := by simp [qx]
      have habs : |dx| = dx := abs_of_nonneg hs
      have hsecond : (x.2 - qx.2).natAbs ≤ (x.1 - qx.1).natAbs := by rw [hzero]; exact Nat.zero_le _
      have hn' : (x.1 - qx.1).natAbs = ((u : ℤ) + 1 - |dx|).toNat := by
        simpa [qx, dx, hs, habs] using hn
      unfold supDist
      rw [max_eq_left hsecond]
      exact hn'
    · have hs' : dx < 0 := lt_of_not_ge hs
      have hp : 0 ≤ (u : ℤ) + 1 + dx := by omega
      have hval : x.1 - qx.1 = (u : ℤ) + 1 + dx := by simp [qx, dx, hs]; omega
      have hn : (x.1 - qx.1).natAbs = ((u : ℤ) + 1 + dx).toNat := by
        rw [hval]
        have hc : (((u : ℤ) + 1 + dx).natAbs : ℤ) = (((u : ℤ) + 1 + dx).toNat : ℤ) := by
          rw [Int.natAbs_of_nonneg hp, Int.toNat_of_nonneg hp]
        exact_mod_cast hc
      have hzero : (x.2 - qx.2).natAbs = 0 := by simp [qx]
      have habs : |dx| = -dx := abs_of_neg hs'
      have hsecond : (x.2 - qx.2).natAbs ≤ (x.1 - qx.1).natAbs := by rw [hzero]; exact Nat.zero_le _
      have hn' : (x.1 - qx.1).natAbs = ((u : ℤ) + 1 - |dx|).toNat := by
        have harg : (u : ℤ) + 1 + dx = (u : ℤ) + 1 - (a.1 - x.1) := by dsimp [dx]; omega
        rw [habs]
        simp only [Int.sub_neg]
        simpa [qx, dx, hs] using hn
      unfold supDist
      rw [max_eq_left hsecond]
      exact hn'
  have hdisty : supDist x qy = ((u : ℤ) + 1 - |dy|).toNat := by
    by_cases hs : 0 ≤ dy
    · have hp : 0 ≤ (u : ℤ) + 1 - dy := by omega
      have hval : x.2 - qy.2 = -((u : ℤ) + 1 - dy) := by simp [qy, dy, hs]; omega
      have hn : (x.2 - qy.2).natAbs = ((u : ℤ) + 1 - dy).toNat := by
        rw [hval, Int.natAbs_neg]
        have hc : (((u : ℤ) + 1 - dy).natAbs : ℤ) = (((u : ℤ) + 1 - dy).toNat : ℤ) := by
          rw [Int.natAbs_of_nonneg hp, Int.toNat_of_nonneg hp]
        exact_mod_cast hc
      have hzero : (x.1 - qy.1).natAbs = 0 := by simp [qy]
      have habs : |dy| = dy := abs_of_nonneg hs
      have hsecond : (x.1 - qy.1).natAbs ≤ (x.2 - qy.2).natAbs := by rw [hzero]; exact Nat.zero_le _
      have hn' : (x.2 - qy.2).natAbs = ((u : ℤ) + 1 - |dy|).toNat := by
        simpa [qy, dy, hs, habs] using hn
      unfold supDist
      rw [max_eq_right hsecond]
      exact hn'
    · have hs' : dy < 0 := lt_of_not_ge hs
      have hp : 0 ≤ (u : ℤ) + 1 + dy := by omega
      have hval : x.2 - qy.2 = (u : ℤ) + 1 + dy := by simp [qy, dy, hs]; omega
      have hn : (x.2 - qy.2).natAbs = ((u : ℤ) + 1 + dy).toNat := by
        rw [hval]
        have hc : (((u : ℤ) + 1 + dy).natAbs : ℤ) = (((u : ℤ) + 1 + dy).toNat : ℤ) := by
          rw [Int.natAbs_of_nonneg hp, Int.toNat_of_nonneg hp]
        exact_mod_cast hc
      have hzero : (x.1 - qy.1).natAbs = 0 := by simp [qy]
      have habs : |dy| = -dy := abs_of_neg hs'
      have hsecond : (x.1 - qy.1).natAbs ≤ (x.2 - qy.2).natAbs := by rw [hzero]; exact Nat.zero_le _
      have hn' : (x.2 - qy.2).natAbs = ((u : ℤ) + 1 - |dy|).toNat := by
        have harg : (u : ℤ) + 1 + dy = (u : ℤ) + 1 - (a.2 - x.2) := by dsimp [dy]; omega
        rw [habs]
        simp only [Int.sub_neg]
        simpa [qy, dy, hs] using hn
      unfold supDist
      rw [max_eq_right hsecond]
      exact hn'
  have hdist : setDistance supDist x {z | z ∉ square a u} ≤
      (↑(if |x.1 - a.1| ≥ |x.2 - a.2| then supDist x qx else supDist x qy) : ℕ∞) := by
    change (⨅ z : {z // z ∉ square a u}, (supDist x z.val : ℕ∞)) ≤ _
    by_cases hc : |x.1 - a.1| ≥ |x.2 - a.2|
    · simpa [hc] using (iInf_le (fun z : {z // z ∉ square a u} => (supDist x z.val : ℕ∞)) ⟨qx, hqx⟩)
    · simpa [hc] using (iInf_le (fun z : {z // z ∉ square a u} => (supDist x z.val : ℕ∞)) ⟨qy, hqy⟩)
  have hformula : (if |x.1 - a.1| ≥ |x.2 - a.2| then supDist x qx else supDist x qy) =
      (squareDepth a u x).toNat := by
    have hsdp : (supDist x a : ℤ) = max |x.1 - a.1| |x.2 - a.2| := by
      unfold supDist
      rw [Nat.cast_max]
      simp [Int.natCast_natAbs]
    by_cases hc : |x.1 - a.1| ≥ |x.2 - a.2|
    · rw [if_pos hc, hdistx, hdepth]
      rw [hsdp, max_eq_left hc]
    · have hc' : |x.2 - a.2| ≥ |x.1 - a.1| := le_of_not_ge hc
      rw [if_neg hc, hdisty, hdepth]
      rw [hsdp, max_eq_right hc']
  by_cases hc : |x.1 - a.1| ≥ |x.2 - a.2|
  · have hdistx' : setDistance supDist x {z | z ∉ square a u} ≤ (supDist x qx : ℕ∞) := by
      change (⨅ z : {z // z ∉ square a u}, (supDist x z.val : ℕ∞)) ≤ _
      exact iInf_le (fun z : {z // z ∉ square a u} => (supDist x z.val : ℕ∞)) ⟨qx, hqx⟩
    have hsel : (supDist x qx : ℕ∞) ≤ (squareDepth a u x).toNat := by
      have heq := hformula
      simp [hc] at heq
      rw [heq]
    exact hdistx'.trans hsel
  · have hdisty' : setDistance supDist x {z | z ∉ square a u} ≤ (supDist x qy : ℕ∞) := by
      change (⨅ z : {z // z ∉ square a u}, (supDist x z.val : ℕ∞)) ≤ _
      exact iInf_le (fun z : {z // z ∉ square a u} => (supDist x z.val : ℕ∞)) ⟨qy, hqy⟩
    have hsel : (supDist x qy : ℕ∞) ≤ (squareDepth a u x).toNat := by
      have heq := hformula
      simp [hc] at heq
      rw [heq]
    exact hdisty'.trans hsel

private lemma window_depth {a y z : Plane} {u : ℕ} {i : ℤ}
    (hz : z ∈ window a y u 64 i) : 65 ≤ squareDepth a u z := by
  have hw : z ∈ shell a y u i ∧ z ∉ nearShell a y u 64 i := by
    simpa only [window, Finset.mem_sdiff] using hz
  rcases hw with ⟨hshell, hnot⟩
  have hshell' : z ∈ square a u ∧ (supDist z y : ℤ) = shellRadius u i := by
    simpa only [shell, Finset.mem_filter] using hshell
  rcases hshell' with ⟨hsquare, _⟩
  have hnotdist : ¬ setDistance supDist z {w | w ∉ square a u} ≤ (↑(64 : ℕ) : ℕ∞) := by
    have hnot' : ¬ (z ∈ shell a y u i ∧
        setDistance supDist z {w | w ∉ square a u} ≤ (↑(64 : ℕ) : ℕ∞)) := by
      simpa only [nearShell, Finset.mem_filter] using hnot
    intro hd
    exact hnot' ⟨hshell, hd⟩
  have hdepthNonneg : 0 ≤ squareDepth a u z := by
    rw [squareDepth_le_formula hsquare]
    have hdist : supDist z a ≤ u := supDist_le_of_square hsquare
    omega
  have hdepthNat : 65 ≤ (squareDepth a u z).toNat := by
    by_contra h
    have hle : (squareDepth a u z).toNat ≤ 64 := by omega
    apply hnotdist
    exact (distance_le_depth hsquare).trans (by exact_mod_cast hle)
  rw [← Int.toNat_of_nonneg hdepthNonneg]
  exact_mod_cast hdepthNat

private lemma window_neighbor_taper {a y z w : Plane} {u : ℕ} {i : ℤ}
    (hspacing : 390 ≤ shellSpacing u) (hz : z ∈ window a y u 64 i)
    (hadj : Adjacent z w) : w ∈ taper a y u i := by
  have hdepthZ : 65 ≤ squareDepth a u z := window_depth hz
  have hclose : supDist z w ≤ 1 := supDist_adj_le_one hadj
  have hdepthW : 64 ≤ squareDepth a u w := by
    have hh := depth_close (a := a) (u := u) (x := z) (z := w) hclose
    omega
  have hwSquare : w ∈ square a u := square_of_positive_depth (by omega)
  have hdata : z ∈ square a u ∧ (supDist z y : ℤ) = shellRadius u i := by
    have hshell : z ∈ shell a y u i := (Finset.mem_sdiff.mp hz).1
    simpa only [shell, Finset.mem_filter] using hshell
  have hclose' : supDist w z ≤ 1 := by simpa [supDist_comm] using hclose
  have hupper : supDist w y ≤ supDist z y + 1 := by
    calc
      supDist w y ≤ supDist w z + supDist z y := supDist_triangle w z y
      _ ≤ 1 + supDist z y := Nat.add_le_add_right hclose' _
      _ = supDist z y + 1 := Nat.add_comm _ _
  have hlower : supDist z y ≤ supDist w y + 1 := by
    calc
      supDist z y ≤ supDist z w + supDist w y := supDist_triangle z w y
      _ ≤ 1 + supDist w y := Nat.add_le_add_right hclose _
      _ = supDist w y + 1 := Nat.add_comm _ _
  have hrad : |(supDist w y : ℤ) - shellRadius u i| ≤ 1 := by
    rw [← hdata.2]
    apply abs_le.mpr
    constructor
    · have h := show (supDist w y : ℤ) ≤ (supDist z y : ℤ) + 1 by exact_mod_cast hupper
      omega
    · have h := show (supDist z y : ℤ) ≤ (supDist w y : ℤ) + 1 by exact_mod_cast hlower
      omega
  have hradInt : (radialOffset y u i w : ℤ) ≤ 1 := by
    change (((supDist w y : ℤ) - shellRadius u i).natAbs : ℤ) ≤ 1
    rw [Int.natCast_natAbs]
    exact hrad
  have hradReal : (radialOffset y u i w : ℝ) ≤ 1 := by exact_mod_cast hradInt
  simp only [taper, Finset.mem_filter]
  refine ⟨hwSquare, ?_, ?_⟩
  · nlinarith [hspacing, hradReal]
  · omega

theorem main : AKLT.Blueprint.Win.WindowBufferStatement := by
  intro a y u i hsetup
  rcases hsetup with ⟨⟨_, hu, _⟩, _, _, _⟩
  have hspacing : 390 ≤ shellSpacing u := spacing_ge_390 hu
  have hWindowTaper : window a y u 64 i ⊆ taper a y u i := by
    intro z hz
    have hdepth : 65 ≤ squareDepth a u z := window_depth hz
    have hdata : z ∈ square a u ∧ (supDist z y : ℤ) = shellRadius u i := by
      have hshell : z ∈ shell a y u i := (Finset.mem_sdiff.mp hz).1
      simpa only [shell, Finset.mem_filter] using hshell
    have hradzero : radialOffset y u i z = 0 := by
      simp [radialOffset, hdata.2]
    simp only [taper, Finset.mem_filter]
    refine ⟨hdata.1, ?_, ?_⟩
    · rw [hradzero]
      linarith [hspacing]
    · rw [hradzero]
      omega
  have hTaperFar : taper a y u i ⊆ farVolume a y u i := by
    intro z hz
    exact far_of_close_taper hspacing hz (by simp [supDist])
  have hNeighbor : ∀ z ∈ window a y u 64 i, ∀ w, Adjacent z w → w ∈ taper a y u i := by
    intro z hz w hadj
    exact window_neighbor_taper hspacing hz hadj
  have hNoBond : NoBond (↑(taper a y u i)) {z | z ∉ farVolume a y u i} := by
    intro z hz w hw hadj
    have hz' : z ∈ taper a y u i := by simpa using hz
    have hwfar := far_of_close_taper hspacing hz' (supDist_adj_le_one hadj)
    exact hw hwfar
  have hRaw : cutRaw a y u i ⊆ cutVolume a y u i := by
    intro x hx
    have hx' : x ∈ rawBoundary (taper a y u i) := by simpa [cutRaw] using hx
    rw [rawBoundary, Finset.mem_sdiff] at hx'
    rcases hx' with ⟨hbi, hnotTaper⟩
    obtain ⟨z, hz, hball⟩ := Finset.mem_biUnion.mp hbi
    have hclose := supDist_starBall_le_one hball
    have hclose' : supDist z x ≤ 1 := by simpa [supDist_comm] using hclose
    have hfar := far_of_close_taper (a := a) (y := y) (z := z) (w := x)
      hspacing hz hclose'
    have hnotWindow : x ∉ window a y u 64 i := by
      intro hxw
      exact hnotTaper (hWindowTaper hxw)
    change x ∈ farVolume a y u i \ window a y u 64 i
    exact Finset.mem_sdiff.mpr ⟨hfar, hnotWindow⟩
  exact ⟨hWindowTaper, hTaperFar, hNeighbor, hNoBond, hRaw⟩

end AKLT.W.WIN036
