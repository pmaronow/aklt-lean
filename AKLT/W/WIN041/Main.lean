module
public import AKLT.Blueprint.Win.NodesTaper

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN041

private theorem square_coord_bounds (a z : Plane) (u : ℕ)
    (hz : z ∈ square a u) (axis : Fin 2) :
    coord axis a - (u : ℤ) ≤ coord axis z ∧
      coord axis z ≤ coord axis a + (u : ℤ) := by
  rcases Finset.mem_product.mp hz with ⟨hx, hy⟩
  have hx' := Finset.mem_Icc.mp hx
  have hy' := Finset.mem_Icc.mp hy
  fin_cases axis <;> simp [coord] <;> omega

private theorem coord_diff_le_supDist (x y : Plane) (axis : Fin 2) :
    (coord axis x - coord axis y).natAbs ≤ supDist x y := by
  fin_cases axis <;> simp [coord, supDist]

private theorem natAbs_ge_two {n : ℤ} (hn : 2 ≤ n) : 2 ≤ n.natAbs := by
  have hn' : (2 : ℤ) ≤ (n.natAbs : ℤ) := by
    rw [Int.natAbs_of_nonneg (by omega)]
    exact hn
  exact_mod_cast hn'

private theorem expanded_box (a y : Plane) (u : ℕ)
    (hd : setDistance supDist y (↑(square a u) : Set Plane) = 1) :
    ∀ axis : Fin 2,
      coord axis a - (u : ℤ) - 1 ≤ coord axis y ∧
      coord axis y ≤ coord axis a + (u : ℤ) + 1 := by
  intro axis
  have hlower : coord axis a - (u : ℤ) - 1 ≤ coord axis y := by
    by_contra hnot
    have hy : coord axis y ≤ coord axis a - (u : ℤ) - 2 := by omega
    have htwo : (2 : ℕ∞) ≤ setDistance supDist y (↑(square a u) : Set Plane) := by
      unfold setDistance
      apply le_iInf
      intro z
      have hz := square_coord_bounds a z.val u z.property axis
      have hdif : 2 ≤ (coord axis z.val - coord axis y).natAbs :=
        natAbs_ge_two (by omega)
      have hflip : coord axis z.val - coord axis y =
          -(coord axis y - coord axis z.val) := by omega
      rw [hflip, Int.natAbs_neg] at hdif
      have hsup : 2 ≤ supDist y z.val :=
        le_trans hdif (coord_diff_le_supDist y z.val axis)
      exact_mod_cast hsup
    rw [hd] at htwo
    norm_num at htwo
  have hupper : coord axis y ≤ coord axis a + (u : ℤ) + 1 := by
    by_contra hnot
    have hy : coord axis a + (u : ℤ) + 2 ≤ coord axis y := by omega
    have htwo : (2 : ℕ∞) ≤ setDistance supDist y (↑(square a u) : Set Plane) := by
      unfold setDistance
      apply le_iInf
      intro z
      have hz := square_coord_bounds a z.val u z.property axis
      have hdif : 2 ≤ (coord axis y - coord axis z.val).natAbs :=
        natAbs_ge_two (by omega)
      have hsup : 2 ≤ supDist y z.val :=
        le_trans hdif (coord_diff_le_supDist y z.val axis)
      exact_mod_cast hsup
    rw [hd] at htwo
    norm_num at htwo
  exact ⟨hlower, hupper⟩

private theorem side_witness (a y : Plane) (u : ℕ) (axis : Fin 2)
    (q : ℤ) (ε k : ℤ)
    (hbox : ∀ axis : Fin 2,
      coord axis a - (u : ℤ) - 1 ≤ coord axis y ∧
      coord axis y ≤ coord axis a + (u : ℤ) + 1)
    (hq : coord axis a - (u : ℤ) ≤ q ∧ q ≤ coord axis a + (u : ℤ))
    (hqeq : q = coord axis y + ε * k)
    (heps : ε = 1 ∨ ε = -1) (hkpos : 0 < k) (hku : k ≤ (u : ℤ)) :
    ∃ z ∈ square a u, coord axis z = q ∧ (supDist z y : ℤ) = k := by
  have hkone : 1 ≤ k := by omega
  fin_cases axis
  · have hy := hbox 1
    have hq' := hq
    simp [coord] at hq'
    have hyL : a.2 - (u : ℤ) - 1 ≤ y.2 := by simpa [coord] using hy.1
    have hyU : y.2 ≤ a.2 + (u : ℤ) + 1 := by simpa [coord] using hy.2
    have hv : ∃ v : ℤ,
        a.2 - (u : ℤ) ≤ v ∧ v ≤ a.2 + (u : ℤ) ∧
          (v = y.2 + k ∨ v = y.2 - k) := by
      by_cases hp : y.2 + k ≤ a.2 + (u : ℤ)
      · exact ⟨y.2 + k, by omega, hp, Or.inl rfl⟩
      · exact ⟨y.2 - k, by omega, by omega, Or.inr rfl⟩
    obtain ⟨v, hvL, hvU, hvEq⟩ := hv
    have hqDiff : q - y.1 = ε * k := by
      rw [hqeq]
      simp [coord]
    have hqAbs : (q - y.1).natAbs = k.natAbs := by
      rw [hqDiff]
      rcases heps with he | he
      · rw [he]
        simp
      · rw [he]
        simp [Int.natAbs_neg]
    have hvAbs : (v - y.2).natAbs = k.natAbs := by
      rcases hvEq with hvEq | hvEq
      · rw [hvEq]
        simp
      · rw [hvEq]
        simp [Int.natAbs_neg]
    refine ⟨(q, v), ?_, ?_, ?_⟩
    · apply Finset.mem_product.mpr
      have hqIcc : a.1 - (u : ℤ) ≤ q ∧ q ≤ a.1 + (u : ℤ) := by omega
      exact ⟨Finset.mem_Icc.mpr hqIcc, Finset.mem_Icc.mpr ⟨hvL, hvU⟩⟩
    · simp [coord]
    · change ((max (q - y.1).natAbs (v - y.2).natAbs : ℕ) : ℤ) = k
      rw [hqAbs, hvAbs]
      simp only [max_self]
      exact Int.natAbs_of_nonneg hkpos.le
  · have hy := hbox 0
    have hq' := hq
    simp [coord] at hq'
    have hyL : a.1 - (u : ℤ) - 1 ≤ y.1 := by simpa [coord] using hy.1
    have hyU : y.1 ≤ a.1 + (u : ℤ) + 1 := by simpa [coord] using hy.2
    have hv : ∃ v : ℤ,
        a.1 - (u : ℤ) ≤ v ∧ v ≤ a.1 + (u : ℤ) ∧
          (v = y.1 + k ∨ v = y.1 - k) := by
      by_cases hp : y.1 + k ≤ a.1 + (u : ℤ)
      · exact ⟨y.1 + k, by omega, hp, Or.inl rfl⟩
      · exact ⟨y.1 - k, by omega, by omega, Or.inr rfl⟩
    obtain ⟨v, hvL, hvU, hvEq⟩ := hv
    have hqDiff : q - y.2 = ε * k := by
      rw [hqeq]
      simp [coord]
    have hqAbs : (q - y.2).natAbs = k.natAbs := by
      rw [hqDiff]
      rcases heps with he | he
      · rw [he]
        simp
      · rw [he]
        simp [Int.natAbs_neg]
    have hvAbs : (v - y.1).natAbs = k.natAbs := by
      rcases hvEq with hvEq | hvEq
      · rw [hvEq]
        simp
      · rw [hvEq]
        simp [Int.natAbs_neg]
    refine ⟨(v, q), ?_, ?_, ?_⟩
    · apply Finset.mem_product.mpr
      have hqIcc : a.2 - (u : ℤ) ≤ q ∧ q ≤ a.2 + (u : ℤ) := by omega
      exact ⟨Finset.mem_Icc.mpr ⟨hvL, hvU⟩, Finset.mem_Icc.mpr hqIcc⟩
    · simp [coord]
    · change ((max (v - y.1).natAbs (q - y.2).natAbs : ℕ) : ℤ) = k
      rw [hqAbs, hvAbs]
      simp only [max_self]
      exact Int.natAbs_of_nonneg hkpos.le

theorem main : AKLT.Blueprint.Win.SignedSideExclusionStatement := by
  intro a y u i hsetup hclear
  intro j hj h hlow hhigh r hr axis ε δ heps hdelta
  let s : ℝ := shellSpacing u
  let k : ℤ := shellRadius u i
  let q : ℤ := coord axis y + ε * k
  let d₀ : ℤ := (u : ℤ) + 1 - δ * (q - coord axis a)
  let q' : ℤ := coord axis y + ε * r
  let d₁ : ℤ := (u : ℤ) + 1 - δ * (q' - coord axis a)
  have huN : 390 ^ 4 ≤ u := by
    have := hsetup.1.2.1
    norm_num [geometryThreshold] at this
    exact this
  have huR : (390 : ℝ) ^ 4 ≤ (u : ℝ) := by exact_mod_cast huN
  have hs0 : 0 ≤ s := by simp [s, shellSpacing]
  have hs4 : s ^ 4 = (u : ℝ) := by
    dsimp [s, shellSpacing]
    calc
      (Real.sqrt (Real.sqrt (u : ℝ))) ^ 4 =
          ((Real.sqrt (Real.sqrt (u : ℝ))) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (u : ℝ)) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
      _ = (u : ℝ) := Real.sq_sqrt (Nat.cast_nonneg u)
  have hs390 : (390 : ℝ) ≤ s := by
    by_contra hn
    have hslt : s < 390 := lt_of_not_ge hn
    have hs2lt : s ^ 2 < (390 : ℝ) ^ 2 :=
      (sq_lt_sq₀ hs0 (by norm_num : (0 : ℝ) ≤ 390)).2 hslt
    have hs4aux : (s ^ 2) ^ 2 < ((390 : ℝ) ^ 2) ^ 2 :=
      (sq_lt_sq₀ (sq_nonneg s) (by norm_num : (0 : ℝ) ≤ (390 : ℝ) ^ 2)).2 hs2lt
    have hs4lt : s ^ 4 < (390 : ℝ) ^ 4 := by nlinarith [hs4aux]
    rw [hs4] at hs4lt
    linarith
  have hs1 : 1 ≤ s := by linarith
  have hs2ge : 1 ≤ s ^ 2 := by nlinarith [sq_nonneg (s - 1)]
  have hs2le : s ^ 2 ≤ s ^ 4 := by
    have hp : 0 ≤ (s ^ 2 - 1) * s ^ 2 :=
      mul_nonneg (by linarith [hs2ge]) (sq_nonneg s)
    nlinarith [hp]
  have hsu : s ≤ (u : ℝ) := by rw [← hs4]; nlinarith
  have hjR : (j : ℝ) ≤ s / 12 := by exact_mod_cast hj
  have hjRu : (j : ℝ) ≤ (u : ℝ) / 12 := by nlinarith
  have hfirstBound : s / 3 - (j : ℝ) > 32 + (j : ℝ) := by
    nlinarith [hs390, hjR]
  have hsecondBoundR : (32 : ℝ) + (j : ℝ) <
      2 * (u : ℝ) + 2 - (j : ℝ) := by nlinarith [huR, hjRu]
  have hsecondBound : (32 : ℤ) + (j : ℤ) <
      2 * (u : ℤ) + 2 - (j : ℤ) := by exact_mod_cast hsecondBoundR
  have hkLower : 2 * s - 1 ≤ (k : ℝ) := by
    have hfloor := Int.lt_floor_add_one ((i : ℝ) * s)
    have hi : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hsetup.2.1
    have hmul : 2 * s ≤ (i : ℝ) * s := by
      exact mul_le_mul_of_nonneg_right hi hs0
    dsimp [k]
    change (2 : ℝ) * s - 1 ≤ (⌊(i : ℝ) * shellSpacing u⌋ : ℤ) at ⊢
    have hlt : (i : ℝ) * s < ((⌊(i : ℝ) * s⌋ : ℤ) : ℝ) + 1 := hfloor
    have : (⌊(i : ℝ) * s⌋ : ℝ) = ((⌊(i : ℝ) * s⌋ : ℤ) : ℝ) := rfl
    nlinarith
  have hkpos : 0 < k := by
    have h : (1 : ℝ) ≤ (k : ℝ) := by linarith [hkLower, hs390]
    exact_mod_cast h
  have hkUpperR : (k : ℝ) ≤ (u : ℝ) := by
    have hi : (i : ℝ) ≤ s := hsetup.2.2.1
    have hfloor : (k : ℝ) ≤ (i : ℝ) * s := by
      dsimp [k]
      unfold shellRadius
      exact Int.floor_le _
    have hmul : (i : ℝ) * s ≤ s ^ 2 := by
      calc
        (i : ℝ) * s ≤ s * s := mul_le_mul_of_nonneg_right hi hs0
        _ = s ^ 2 := by ring
    calc
      (k : ℝ) ≤ (i : ℝ) * s := hfloor
      _ ≤ s ^ 2 := hmul
      _ ≤ s ^ 4 := hs2le
      _ = (u : ℝ) := hs4
  have hku : k ≤ (u : ℤ) := by exact_mod_cast hkUpperR
  have hbox := expanded_box a y u hsetup.1.2.2
  have hdBounds : d₀ - (j : ℤ) ≤ d₁ ∧ d₁ ≤ d₀ + (j : ℤ) := by
    have hr' : r = k - (j : ℤ) ∨ r = k + (j : ℤ) := by simpa [k] using hr
    rcases hr' with hr' | hr'
    · subst r
      rcases heps with he | he <;> rcases hdelta with hd | hd <;>
        subst ε <;> subst δ <;> simp only [d₀, d₁, q, q'] <;>
        constructor <;> ring_nf <;> omega
    · subst r
      rcases heps with he | he <;> rcases hdelta with hd | hd <;>
        subst ε <;> subst δ <;> simp only [d₀, d₁, q, q'] <;>
        constructor <;> ring_nf <;> omega
  by_contra heq
  have hdepthEq : d₁ = h := by
    dsimp [d₁, q']
    rw [heq]
    rcases hdelta with hd | hd <;> subst δ <;> simp
  by_cases hselected : d₀ ≤ 0
  · have h₁ : d₁ ≤ (j : ℤ) := by omega
    omega
  by_cases hopposite : 2 * (u : ℤ) + 2 ≤ d₀
  · have h₁ : 2 * (u : ℤ) + 2 - (j : ℤ) ≤ d₁ := by omega
    omega
  have hd₀low : 0 < d₀ := by omega
  have hd₀high : d₀ < 2 * (u : ℤ) + 2 := by omega
  have hqBox : coord axis a - (u : ℤ) ≤ q ∧
      q ≤ coord axis a + (u : ℤ) := by
    rcases hdelta with hd | hd
    · subst δ
      dsimp [d₀, q] at hd₀low hd₀high
      constructor <;> omega
    · subst δ
      dsimp [d₀, q] at hd₀low hd₀high
      constructor <;> omega
  have hside : ∃ z ∈ square a u, coord axis z = q ∧
      (supDist z y : ℤ) = k := by
    apply side_witness a y u axis q ε k hbox hqBox ?_ heps hkpos hku
    rfl
  have hd₀clear : s / 3 ≤ (d₀ : ℝ) := by
    have hc := hclear axis ε δ heps hdelta hside
    simpa [s, d₀, q, k, coord] using hc
  have hd₁lowR : s / 3 - (j : ℝ) ≤ (d₁ : ℝ) := by
    have hb : (d₀ : ℝ) - (j : ℝ) ≤ (d₁ : ℝ) := by exact_mod_cast hdBounds.1
    linarith [hd₀clear]
  have hdepthEqR : (d₁ : ℝ) = (h : ℝ) := by exact_mod_cast hdepthEq
  have hhighR : (h : ℝ) < 32 + (j : ℝ) := by exact_mod_cast hhigh
  linarith [hfirstBound]

end AKLT.W.WIN041
