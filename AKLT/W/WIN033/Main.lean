import AKLT.Blueprint.Win.NodesTaper

noncomputable section
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN033

private lemma natAbs_cast_of_nonpos {d : ℤ} (hd : d ≤ 0) :
    (d.natAbs : ℤ) = -d := by
  rw [← Int.natAbs_neg d]
  exact Int.natAbs_of_nonneg (by omega)

private def inwardDelta (d : ℤ) : ℤ := if 0 < d then -1 else if d < 0 then 1 else 0
private def outwardDelta (d : ℤ) : ℤ := if 0 ≤ d then 1 else -1

private def inwardStep (z y : Plane) : Plane :=
  (z.1 + (if (z.1 - y.1).natAbs = supDist z y then inwardDelta (z.1-y.1) else 0),
   z.2 + (if (z.2 - y.2).natAbs = supDist z y then inwardDelta (z.2-y.2) else 0))

private def outwardStep (z y : Plane) : Plane :=
  if (z.1-y.1).natAbs = supDist z y then
    (z.1 + outwardDelta (z.1-y.1), z.2)
  else (z.1, z.2 + outwardDelta (z.2-y.2))

private lemma natAbs_inwardDelta (d : ℤ) (hd : 0 < d.natAbs) :
    (d + inwardDelta d).natAbs + 1 = d.natAbs := by
  unfold inwardDelta
  by_cases hp : 0 < d
  · have hd1 : 0 ≤ d - 1 := by omega
    have hd2 : 0 ≤ d := le_of_lt hp
    simp [hp, Int.natAbs_of_nonneg hd1, Int.natAbs_of_nonneg hd2]
    omega
  · have hn : d < 0 := by
      by_contra h
      have : d = 0 := by omega
      subst d
      simp at hd
    rw [if_neg hp, if_pos hn]
    have hcast : (((d + 1).natAbs : ℤ) + 1) = (d.natAbs : ℤ) := by
      rw [natAbs_cast_of_nonpos (by omega : d + 1 ≤ 0), natAbs_cast_of_nonpos (by omega : d ≤ 0)]
      omega
    exact_mod_cast hcast

private lemma natAbs_outwardDelta (d : ℤ) :
    (d + outwardDelta d).natAbs = d.natAbs + 1 := by
  unfold outwardDelta
  by_cases hp : 0 ≤ d
  · have h1 : 0 ≤ d + 1 := by omega
    simp [hp, Int.natAbs_of_nonneg h1, Int.natAbs_of_nonneg hp]
    omega
  · have hn : d < 0 := by omega
    rw [if_neg hp]
    have hcast : ((d - 1).natAbs : ℤ) = (d.natAbs : ℤ) + 1 := by
      rw [natAbs_cast_of_nonpos (by omega : d - 1 ≤ 0), natAbs_cast_of_nonpos (by omega : d ≤ 0)]
      omega
    exact_mod_cast hcast

private lemma inwardDelta_abs_le_one (d : ℤ) : (inwardDelta d).natAbs ≤ 1 := by
  unfold inwardDelta
  split_ifs <;> simp <;> omega

private lemma outwardDelta_abs (d : ℤ) : (outwardDelta d).natAbs = 1 := by
  unfold outwardDelta
  split_ifs <;> simp

private lemma inwardStep_radius {z y : Plane} (hρ : 0 < supDist z y) :
    supDist (inwardStep z y) y = supDist z y - 1 := by
  let ρ := supDist z y
  let dx := z.1 - y.1
  let dy := z.2 - y.2
  have hρ' : 0 < ρ := hρ
  have hdxle : dx.natAbs ≤ ρ := by
    dsimp [ρ, dx]
    exact le_max_left _ _
  have hdyle : dy.natAbs ≤ ρ := by
    dsimp [ρ, dy]
    exact le_max_right _ _
  have hsome : dx.natAbs = ρ ∨ dy.natAbs = ρ := by
    dsimp [ρ]
    by_cases hxy : dx.natAbs ≤ dy.natAbs
    · right
      exact (max_eq_right hxy).symm
    · left
      have hyx : dy.natAbs ≤ dx.natAbs := by omega
      exact (max_eq_left hyx).symm
  have hx : (inwardStep z y).1 - y.1 =
      dx + (if dx.natAbs = ρ then inwardDelta dx else 0) := by
    dsimp [inwardStep, dx, ρ]
    split_ifs <;> omega
  have hy : (inwardStep z y).2 - y.2 =
      dy + (if dy.natAbs = ρ then inwardDelta dy else 0) := by
    dsimp [inwardStep, dy, ρ]
    split_ifs <;> omega
  have hxabs : ((inwardStep z y).1 - y.1).natAbs =
      if dx.natAbs = ρ then ρ - 1 else dx.natAbs := by
    rw [hx]
    by_cases hs : dx.natAbs = ρ
    · simp only [if_pos hs]
      have hdxpos : 0 < dx.natAbs := by omega
      have h := natAbs_inwardDelta dx hdxpos
      omega
    · simp only [if_neg hs]
      simp
  have hyabs : ((inwardStep z y).2 - y.2).natAbs =
      if dy.natAbs = ρ then ρ - 1 else dy.natAbs := by
    rw [hy]
    by_cases hs : dy.natAbs = ρ
    · simp only [if_pos hs]
      have hdypos : 0 < dy.natAbs := by omega
      have h := natAbs_inwardDelta dy hdypos
      omega
    · simp only [if_neg hs]
      simp
  rw [supDist, hxabs, hyabs]
  change max (if dx.natAbs = ρ then ρ - 1 else dx.natAbs)
      (if dy.natAbs = ρ then ρ - 1 else dy.natAbs) = ρ - 1
  rcases hsome with hs | hs
  · have hybound : (if dy.natAbs = ρ then ρ - 1 else dy.natAbs) ≤ ρ - 1 := by
      split_ifs with hdy <;> omega
    rw [if_pos hs]
    exact max_eq_left hybound
  · have hxbnd : (if dx.natAbs = ρ then ρ - 1 else dx.natAbs) ≤ ρ - 1 := by
      split_ifs with hdx <;> omega
    rw [if_pos hs]
    exact max_eq_right hxbnd

private lemma outwardStep_radius {z y : Plane} :
    supDist (outwardStep z y) y = supDist z y + 1 := by
  let ρ := supDist z y
  let dx := z.1 - y.1
  let dy := z.2 - y.2
  have hdxle : dx.natAbs ≤ ρ := by dsimp [ρ, dx]; exact le_max_left _ _
  have hdyle : dy.natAbs ≤ ρ := by dsimp [ρ, dy]; exact le_max_right _ _
  have hsome : dx.natAbs = ρ ∨ dy.natAbs = ρ := by
    dsimp [ρ]
    by_cases hxy : dx.natAbs ≤ dy.natAbs
    · right
      exact (max_eq_right hxy).symm
    · left
      have hyx : dy.natAbs ≤ dx.natAbs := by omega
      exact (max_eq_left hyx).symm
  have hx : (outwardStep z y).1 - y.1 =
      if dx.natAbs = ρ then dx + outwardDelta dx else dx := by
    dsimp [outwardStep, dx, ρ]
    split_ifs <;> omega
  have hy : (outwardStep z y).2 - y.2 =
      if dx.natAbs = ρ then dy else dy + outwardDelta dy := by
    dsimp [outwardStep, dx, dy, ρ]
    split_ifs <;> omega
  have hxabs : ((outwardStep z y).1-y.1).natAbs =
      if dx.natAbs = ρ then ρ + 1 else dx.natAbs := by
    rw [hx]
    by_cases hs : dx.natAbs = ρ
    · simp only [if_pos hs]
      rw [natAbs_outwardDelta]
      omega
    · simp only [if_neg hs]
  have hyabs : ((outwardStep z y).2-y.2).natAbs =
      if dx.natAbs = ρ then dy.natAbs else dy.natAbs + 1 := by
    rw [hy]
    by_cases hs : dx.natAbs = ρ
    · simp only [if_pos hs]
    · simp only [if_neg hs]
      rw [natAbs_outwardDelta]
  rw [supDist, hxabs, hyabs]
  change max (if dx.natAbs = ρ then ρ + 1 else dx.natAbs)
      (if dx.natAbs = ρ then dy.natAbs else dy.natAbs + 1) = ρ + 1
  by_cases hs : dx.natAbs = ρ
  · rw [if_pos hs]
    simp only [if_pos hs]
    exact max_eq_left (show dy.natAbs ≤ ρ + 1 by omega)
  · have hdy : dy.natAbs = ρ := hsome.resolve_left hs
    rw [if_neg hs, if_neg hs]
    rw [hdy]
    exact max_eq_right (by omega)

private lemma inwardDelta_abs_eq_one {d : ℤ} (hd : 0 < d.natAbs) :
    (inwardDelta d).natAbs = 1 := by
  unfold inwardDelta
  by_cases hp : 0 < d
  · simp [hp]
  · have hn : d < 0 := by
      by_contra h
      have : d = 0 := by omega
      subst d
      simp at hd
    simp [hp, hn]

private lemma inwardStep_star {z y : Plane} (hρ : 0 < supDist z y) :
    supDist (inwardStep z y) z = 1 := by
  let ρ := supDist z y
  let dx := z.1 - y.1
  let dy := z.2 - y.2
  have hx : (inwardStep z y).1 - z.1 =
      if dx.natAbs = ρ then inwardDelta dx else 0 := by
    dsimp [inwardStep, dx, ρ]
    split_ifs <;> omega
  have hy : (inwardStep z y).2 - z.2 =
      if dy.natAbs = ρ then inwardDelta dy else 0 := by
    dsimp [inwardStep, dy, ρ]
    split_ifs <;> omega
  have hsome : dx.natAbs = ρ ∨ dy.natAbs = ρ := by
    dsimp [ρ]
    by_cases hxy : dx.natAbs ≤ dy.natAbs
    · right
      exact (max_eq_right hxy).symm
    · left
      have hyx : dy.natAbs ≤ dx.natAbs := by omega
      exact (max_eq_left hyx).symm
  have hρpos : 0 < ρ := hρ
  have hxabs_le : ((inwardStep z y).1-z.1).natAbs ≤ 1 := by
    rw [hx]
    split_ifs <;> [exact inwardDelta_abs_le_one _; simp]
  have hyabs_le : ((inwardStep z y).2-z.2).natAbs ≤ 1 := by
    rw [hy]
    split_ifs <;> [exact inwardDelta_abs_le_one _; simp]
  have hmaxge : 1 ≤ max ((inwardStep z y).1-z.1).natAbs
      ((inwardStep z y).2-z.2).natAbs := by
    rcases hsome with hs | hs
    · have hd : 0 < dx.natAbs := by omega
      have heq : ((inwardStep z y).1-z.1).natAbs = 1 := by
        rw [hx, if_pos hs]
        exact inwardDelta_abs_eq_one hd
      rw [heq]
      exact Nat.le_max_left _ _
    · have hd : 0 < dy.natAbs := by omega
      have heq : ((inwardStep z y).2-z.2).natAbs = 1 := by
        rw [hy, if_pos hs]
        exact inwardDelta_abs_eq_one hd
      rw [heq]
      exact Nat.le_max_right _ _
  have hmaxle : max ((inwardStep z y).1-z.1).natAbs
      ((inwardStep z y).2-z.2).natAbs ≤ 1 := max_le_iff.mpr ⟨hxabs_le, hyabs_le⟩
  unfold supDist
  exact Nat.le_antisymm hmaxle hmaxge

private lemma outwardStep_star {z y : Plane} : supDist (outwardStep z y) z = 1 := by
  let dx := z.1-y.1
  let dy := z.2-y.2
  let ρ := supDist z y
  have hx : (outwardStep z y).1-z.1 =
      if dx.natAbs = ρ then outwardDelta dx else 0 := by
    dsimp [outwardStep, dx, ρ]
    split_ifs <;> omega
  have hy : (outwardStep z y).2-z.2 =
      if dx.natAbs = ρ then 0 else outwardDelta dy := by
    dsimp [outwardStep, dx, dy, ρ]
    split_ifs <;> omega
  have hxle : ((outwardStep z y).1-z.1).natAbs ≤ 1 := by
    rw [hx]
    split_ifs <;> simp [outwardDelta_abs]
  have hyle : ((outwardStep z y).2-z.2).natAbs ≤ 1 := by
    rw [hy]
    split_ifs <;> simp [outwardDelta_abs]
  have hge : 1 ≤ max ((outwardStep z y).1-z.1).natAbs
      ((outwardStep z y).2-z.2).natAbs := by
    by_cases hs : dx.natAbs = ρ
    · have heq : ((outwardStep z y).1-z.1).natAbs = 1 := by
        rw [hx, if_pos hs]
        exact outwardDelta_abs _
      rw [heq]
      exact Nat.le_max_left _ _
    · have heq : ((outwardStep z y).2-z.2).natAbs = 1 := by
        rw [hy, if_neg hs]
        exact outwardDelta_abs _
      rw [heq]
      exact Nat.le_max_right _ _
  unfold supDist
  exact Nat.le_antisymm (max_le_iff.mpr ⟨hxle, hyle⟩) hge

private lemma supDist_step_le {x x' a : Plane} (h : supDist x' x ≤ 1) :
    supDist x' a ≤ supDist x a + 1 := by
  have hx1 : ((x'.1-x.1).natAbs) ≤ 1 := by
    have := Nat.le_max_left ((x'.1-x.1).natAbs) ((x'.2-x.2).natAbs)
    exact this.trans (by simpa [supDist] using h)
  have hx2 : ((x'.2-x.2).natAbs) ≤ 1 := by
    have := Nat.le_max_right ((x'.1-x.1).natAbs) ((x'.2-x.2).natAbs)
    exact this.trans (by simpa [supDist] using h)
  have hcoord1 : (x'.1-a.1).natAbs ≤ (x.1-a.1).natAbs + 1 := by
    have heq : x'.1-a.1 = (x'.1-x.1)+(x.1-a.1) := by omega
    rw [heq]
    calc
      _ ≤ (x'.1-x.1).natAbs + (x.1-a.1).natAbs := Int.natAbs_add_le _ _
      _ ≤ 1 + (x.1-a.1).natAbs := Nat.add_le_add_right hx1 _
      _ = _ := by omega
  have hcoord2 : (x'.2-a.2).natAbs ≤ (x.2-a.2).natAbs + 1 := by
    have heq : x'.2-a.2 = (x'.2-x.2)+(x.2-a.2) := by omega
    rw [heq]
    calc
      _ ≤ (x'.2-x.2).natAbs + (x.2-a.2).natAbs := Int.natAbs_add_le _ _
      _ ≤ 1 + (x.2-a.2).natAbs := Nat.add_le_add_right hx2 _
      _ = _ := by omega
  unfold supDist
  have h1 : (x'.1-a.1).natAbs ≤ max (x.1-a.1).natAbs (x.2-a.2).natAbs + 1 :=
    hcoord1.trans (Nat.add_le_add_right (Nat.le_max_left _ _) 1)
  have h2 : (x'.2-a.2).natAbs ≤ max (x.1-a.1).natAbs (x.2-a.2).natAbs + 1 :=
    hcoord2.trans (Nat.add_le_add_right (Nat.le_max_right _ _) 1)
  exact max_le_iff.mpr ⟨h1, h2⟩

private lemma squareDepth_step_lower {a : Plane} {u : ℕ} {x x' : Plane}
    (hstep : supDist x' x ≤ 1) : squareDepth a u x ≤ squareDepth a u x' + 1 := by
  have hdist := supDist_step_le (a := a) hstep
  have hdist' : (supDist x' a : ℤ) ≤ (supDist x a : ℤ) + 1 := by exact_mod_cast hdist
  unfold squareDepth
  omega

private lemma depth_mem_square {a : Plane} {u : ℕ} {x : Plane}
    (h : 32 ≤ squareDepth a u x) : x ∈ square a u := by
  have hraw : 32 ≤ (u : ℤ) + 1 - (supDist x a : ℤ) := by
    let q := (u : ℤ) + 1 - (supDist x a : ℤ)
    change 32 ≤ max 0 q at h
    by_cases hq : 0 ≤ q
    · simpa [q, max_eq_right hq] using h
    · have hm : max 0 q = 0 := max_eq_left (le_of_not_ge hq)
      rw [hm] at h
      omega
  have hd : supDist x a ≤ u := by omega
  have hdx : (x.1-a.1).natAbs ≤ u := by
    have := Nat.le_max_left ((x.1-a.1).natAbs) ((x.2-a.2).natAbs)
    exact this.trans (by simpa [supDist] using hd)
  have hdy : (x.2-a.2).natAbs ≤ u := by
    have := Nat.le_max_right ((x.1-a.1).natAbs) ((x.2-a.2).natAbs)
    exact this.trans (by simpa [supDist] using hd)
  have hdx' : |(x.1-a.1 : ℤ)| ≤ (u : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hdx
  have hdy' : |(x.2-a.2 : ℤ)| ≤ (u : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hdy
  unfold square
  change x ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + u) ×ˢ
    Finset.Icc (a.2 - (u : ℤ)) (a.2 + u)
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  constructor <;> omega

private lemma offset_inward {k : ℤ} {r : ℕ} (hk : 0 ≤ k) (hr : (r : ℤ) > k) :
    ((((r-1 : ℕ) : ℤ) - k).natAbs) + 1 = (((r : ℤ) - k).natAbs) := by
  have hrpos : 1 ≤ r := by omega
  have hsub : ((r-1 : ℕ) : ℤ) = (r : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have hnew : 0 ≤ ((r-1 : ℕ) : ℤ) - k := by rw [hsub]; omega
  have hold : 0 ≤ (r : ℤ) - k := by omega
  have hcast : ((((r-1 : ℕ) : ℤ) - k).natAbs : ℤ) + 1 = (((r : ℤ) - k).natAbs : ℤ) := by
    rw [Int.natAbs_of_nonneg hnew, Int.natAbs_of_nonneg hold]
    omega
  exact_mod_cast hcast

private lemma offset_outward {k : ℤ} {r : ℕ} (hr : (r : ℤ) < k) :
    ((((r+1 : ℕ) : ℤ) - k).natAbs) + 1 = (((r : ℤ) - k).natAbs) := by
  have hnew : ((r+1 : ℕ) : ℤ) - k ≤ 0 := by simp; omega
  have hold : (r : ℤ) - k ≤ 0 := by omega
  have hcast : ((((r+1 : ℕ) : ℤ) - k).natAbs : ℤ) + 1 = (((r : ℤ) - k).natAbs : ℤ) := by
    rw [natAbs_cast_of_nonpos hnew, natAbs_cast_of_nonpos hold]
    omega
  exact_mod_cast hcast

private lemma supDist_comm (x y : Plane) : supDist x y = supDist y x := by
  have hx : y.1 - x.1 = -(x.1 - y.1) := by omega
  have hy : y.2 - x.2 = -(x.2 - y.2) := by omega
  unfold supDist
  rw [hx, hy]
  simp only [Int.natAbs_neg]

private theorem radialRoute {a y : Plane} {u : ℕ} {i : ℤ}
    (hk : 0 ≤ shellRadius u i) :
    ∀ {z : Plane}, z ∈ taper a y u i →
      ∃ w ∈ core a y u i,
        JoinedIn StarAdjacent (↑(taper a y u i)) z w := by
  let U := taper a y u i
  let k := shellRadius u i
  have aux : ∀ n : ℕ, ∀ z : Plane, radialOffset y u i z = n → z ∈ U →
      ∃ w ∈ core a y u i, JoinedIn StarAdjacent (↑U) z w := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro z hn hz
      have hzmem : z ∈ taper a y u i := by simpa [U] using hz
      simp only [taper, Finset.mem_filter] at hzmem
      rcases hzmem with ⟨hzsq, hconds⟩
      rcases hconds with ⟨hbound, hdepth⟩
      by_cases hn0 : n = 0
      · have hzeroNat : radialOffset y u i z = 0 := by simpa [hn0] using hn
        have hzero : ((supDist z y : ℤ) - k).natAbs = 0 := by
          simpa [radialOffset, k] using hzeroNat
        have hdiff : (supDist z y : ℤ) - k = 0 := Int.natAbs_eq_zero.mp hzero
        refine ⟨z, ?_, Relation.ReflTransGen.refl⟩
        simp only [core, Finset.mem_filter]
        refine ⟨hzsq, ?_⟩
        constructor
        · omega
        · have hdepth0 : 32 ≤ squareDepth a u z := by
            rw [hzeroNat] at hdepth
            omega
          exact hdepth0
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        let ρ := supDist z y
        have hdiff : (ρ : ℤ) - k ≠ 0 := by
          intro h
          have hrad : radialOffset y u i z = 0 := by
            simp [radialOffset, k, ρ, h]
          omega
        have hcase : (ρ : ℤ) < k ∨ k < (ρ : ℤ) := by omega
        rcases hcase with hbelow | habove
        · let z' := outwardStep z y
          have hradius : supDist z' y = ρ + 1 := by
            dsimp [z', ρ]
            exact outwardStep_radius
          have hoff : radialOffset y u i z' + 1 = radialOffset y u i z := by
            dsimp [radialOffset, z', k]
            rw [hradius]
            exact offset_outward (k := shellRadius u i) (r := ρ) hbelow
          have hless : radialOffset y u i z' < n := by omega
          have hstep : supDist z' z ≤ 1 := by
            have hs := outwardStep_star (z := z) (y := y)
            change supDist (outwardStep z y) z ≤ 1
            exact le_of_eq hs
          have hdepth' : (radialOffset y u i z' : ℤ) + 32 ≤ squareDepth a u z' := by
            have hdepthStep := squareDepth_step_lower (a := a) (u := u) hstep
            omega
          have hbound' : (radialOffset y u i z' : ℝ) ≤ shellSpacing u / 12 := by
            have hradle : radialOffset y u i z' ≤ radialOffset y u i z := by omega
            have hradleR : (radialOffset y u i z' : ℝ) ≤ (radialOffset y u i z : ℝ) := by
              exact_mod_cast hradle
            exact hradleR.trans hbound
          have hz'sq : z' ∈ square a u := depth_mem_square (by omega)
          have hz' : z' ∈ U := by
            simp only [U, taper, Finset.mem_filter]
            exact ⟨hz'sq, hbound', hdepth'⟩
          have hadj : StarAdjacent z z' := by
            dsimp [StarAdjacent, z']
            rw [supDist_comm]
            exact outwardStep_star
          obtain ⟨w, hw, hpath⟩ := ih (radialOffset y u i z') hless z' rfl hz'
          refine ⟨w, hw, ?_⟩
          exact Relation.ReflTransGen.trans
            (Relation.ReflTransGen.single ⟨hz, hz', hadj⟩) hpath
        · let z' := inwardStep z y
          have hρpos : 0 < ρ := by omega
          have hradius : supDist z' y = ρ - 1 := by
            dsimp [z', ρ]
            exact inwardStep_radius hρpos
          have hoff : radialOffset y u i z' + 1 = radialOffset y u i z := by
            dsimp [radialOffset, z', k]
            rw [hradius]
            exact offset_inward (k := shellRadius u i) hk habove
          have hless : radialOffset y u i z' < n := by omega
          have hstep : supDist z' z ≤ 1 := by
            have hs := inwardStep_star (z := z) (y := y) hρpos
            change supDist (inwardStep z y) z ≤ 1
            exact le_of_eq hs
          have hdepth' : (radialOffset y u i z' : ℤ) + 32 ≤ squareDepth a u z' := by
            have hdepthStep := squareDepth_step_lower (a := a) (u := u) hstep
            omega
          have hbound' : (radialOffset y u i z' : ℝ) ≤ shellSpacing u / 12 := by
            have hradle : radialOffset y u i z' ≤ radialOffset y u i z := by omega
            have hradleR : (radialOffset y u i z' : ℝ) ≤ (radialOffset y u i z : ℝ) := by
              exact_mod_cast hradle
            exact hradleR.trans hbound
          have hz'sq : z' ∈ square a u := depth_mem_square (by omega)
          have hz' : z' ∈ U := by
            simp only [U, taper, Finset.mem_filter]
            exact ⟨hz'sq, hbound', hdepth'⟩
          have hadj : StarAdjacent z z' := by
            dsimp [StarAdjacent, z']
            rw [supDist_comm]
            exact inwardStep_star hρpos
          obtain ⟨w, hw, hpath⟩ := ih (radialOffset y u i z') hless z' rfl hz'
          refine ⟨w, hw, ?_⟩
          exact Relation.ReflTransGen.trans
            (Relation.ReflTransGen.single ⟨hz, hz', hadj⟩) hpath
  intro z hz
  exact aux (radialOffset y u i z) z rfl (by simpa [U] using hz)

/-- Radially move a taper site to its shell while retaining the square-depth margin. -/
theorem main : AKLT.Blueprint.Win.RadialPathsStatement := by
  intro a y u i hsetup z hz
  have hspacing : 0 ≤ shellSpacing u := Real.sqrt_nonneg _
  have hi : 0 ≤ (i : ℝ) := by
    have hi' : (2 : ℤ) ≤ i := hsetup.2.1
    exact_mod_cast (show (0 : ℤ) ≤ i by omega)
  have hprod : 0 ≤ (i : ℝ) * shellSpacing u := mul_nonneg hi hspacing
  have hk : 0 ≤ shellRadius u i := Int.floor_nonneg.mpr hprod
  exact radialRoute hk hz

end AKLT.W.WIN033
