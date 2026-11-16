import AKLT.Blueprint.Win.NodesShell

noncomputable section
open AKLT.Defs

namespace AKLT.W.WIN006

private lemma square_mem_iff (a : Plane) (u : ℕ) (z : Plane) :
    z ∈ square a u ↔ a.1 - (u : ℤ) ≤ z.1 ∧ z.1 ≤ a.1 + u ∧
      a.2 - (u : ℤ) ≤ z.2 ∧ z.2 ≤ a.2 + u := by
  simp [square, Finset.mem_product, Finset.mem_Icc]
  omega

private lemma dist_lower_of_setDistance (a y : Plane) (u : ℕ)
    (h : setDistance supDist y (↑(square a u) : Set Plane) = 1)
    (z : Plane) (hz : z ∈ square a u) : 1 ≤ supDist y z := by
  have hi : (1 : ℕ∞) ≤ setDistance supDist y (↑(square a u) : Set Plane) := by
    rw [h]
  have hv : setDistance supDist y (↑(square a u) : Set Plane) ≤ (supDist y z : ℕ∞) := by
    unfold setDistance
    exact iInf_le (fun w : {q // q ∈ (↑(square a u) : Set Plane)} => (supDist y w.val : ℕ∞)) ⟨z, hz⟩
  have hv' : (1 : ℕ∞) ≤ (supDist y z : ℕ∞) := hi.trans hv
  exact_mod_cast hv'

private lemma dist_lower_all (a y : Plane) (u : ℕ) (n : ℕ)
    (h : ∀ z, z ∈ square a u → n ≤ supDist y z) :
    (n : ℕ∞) ≤ setDistance supDist y (↑(square a u) : Set Plane) := by
  unfold setDistance
  apply le_iInf
  intro z
  exact_mod_cast h z.val z.property

private lemma shellScale (l u : ℕ) (_hl : 1 ≤ l)
    (hu : geometryThreshold l ≤ u) :
    16 ≤ shellSpacing u ∧ shellSpacing u ^ 4 = (u : ℝ) ∧
      shellSpacing u ^ 2 + shellSpacing u < (u : ℝ) / 2 := by
  let s := shellSpacing u
  have hthreshold : (16 : ℕ) ^ 4 ≤ u := by
    have hmax : 16 ≤ max 16 (6 * (l + 1)) := le_max_left _ _
    have hp : (16 : ℕ) ^ 4 ≤ (max 16 (6 * (l + 1))) ^ 4 := Nat.pow_le_pow_left hmax 4
    exact le_trans hp hu
  have huR : (16 : ℝ) ^ 4 ≤ (u : ℝ) := by exact_mod_cast hthreshold
  have hs2 : (s ^ 2) = Real.sqrt (u : ℝ) := by
    dsimp [s, shellSpacing]
    rw [Real.sq_sqrt (Real.sqrt_nonneg (u : ℝ))]
  have hs4 : s ^ 4 = (u : ℝ) := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (u : ℝ)) ^ 2 := by rw [hs2]
      _ = (u : ℝ) := Real.sq_sqrt (Nat.cast_nonneg u)
  have hsqrt256 : (256 : ℝ) ≤ Real.sqrt (u : ℝ) := by
    apply (Real.le_sqrt (by norm_num) (Nat.cast_nonneg u)).2
    nlinarith
  have hs16 : (16 : ℝ) ≤ s := by
    dsimp [s, shellSpacing]
    apply (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg (u : ℝ))).2
    nlinarith
  have hsp : 0 ≤ s := by dsimp [s, shellSpacing]; positivity
  have hsq : (256 : ℝ) ≤ s ^ 2 := by nlinarith
  have hs3 : (0 : ℝ) ≤ s ^ 2 - s - 1 := by nlinarith
  have hmain : s ^ 2 + s < s ^ 4 / 2 := by
    nlinarith [mul_nonneg (sq_nonneg (s ^ 2 - 2)) (sq_nonneg (s ^ 2 + 2))]
  refine ⟨?_, hs4, ?_⟩
  · exact_mod_cast hs16
  · change s ^ 2 + s < (u : ℝ) / 2
    rw [← hs4]
    exact hmain

private lemma shellRadius_bounds (u : ℕ) (i : ℤ)
    (hs : 16 ≤ shellSpacing u) (hi : 2 ≤ i)
    (hiLast : i ≤ lastShellIndex u) :
    2 * shellSpacing u - 1 < (shellRadius u i : ℝ) ∧
      (shellRadius u i : ℝ) ≤ shellSpacing u ^ 2 + shellSpacing u := by
  let s := shellSpacing u
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (show 0 ≤ i by omega)
  have hfloorL : ((⌊(i : ℝ) * s⌋ : ℤ) : ℝ) > (i : ℝ) * s - 1 := by
    have h := Int.lt_floor_add_one ((i : ℝ) * s)
    have h' : (i : ℝ) * s < ((⌊(i : ℝ) * s⌋ : ℤ) : ℝ) + 1 := by exact_mod_cast h
    linarith
  have hfloorU : ((⌊(i : ℝ) * s⌋ : ℤ) : ℝ) ≤ (i : ℝ) * s := by
    exact_mod_cast Int.floor_le ((i : ℝ) * s)
  have hiBound : (i : ℝ) ≤ s + 1 := by
    have hlast : i ≤ ⌊s⌋ + 1 := by simpa [lastShellIndex, s] using hiLast
    have hlastR : (i : ℝ) ≤ (⌊s⌋ : ℤ) + 1 := by exact_mod_cast hlast
    have hfl : (⌊s⌋ : ℤ) ≤ s := Int.floor_le s
    have hflR : ((⌊s⌋ : ℤ) : ℝ) ≤ s := by exact_mod_cast hfl
    linarith
  constructor
  · have hi2 : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    have := mul_le_mul_of_nonneg_right hi2 hs0
    dsimp [s, shellRadius]
    nlinarith
  · dsimp [s, shellRadius] at *
    calc
      ((⌊(i : ℝ) * shellSpacing u⌋ : ℤ) : ℝ) ≤ (i : ℝ) * shellSpacing u := hfloorU
      _ ≤ (shellSpacing u + 1) * shellSpacing u := by
        exact mul_le_mul_of_nonneg_right (by simpa [s] using hiBound) hs0
      _ = shellSpacing u ^ 2 + shellSpacing u := by ring

private lemma exterior_side (a y : Plane) (u : ℕ)
    (hy : setDistance supDist y (↑(square a u) : Set Plane) = 1) :
    y.1 = a.1 + (u : ℤ) + 1 ∨ y.1 = a.1 - (u : ℤ) - 1 ∨
    y.2 = a.2 + (u : ℤ) + 1 ∨ y.2 = a.2 - (u : ℤ) - 1 := by
  have hnot : y ∉ square a u := by
    intro h
    have hh := dist_lower_of_setDistance a y u hy y h
    simp [supDist] at hh
  have hboundRight1 : y.1 ≤ a.1 + (u : ℤ) + 1 := by
    by_contra hn
    have hd : ∀ z, z ∈ square a u → y.1 - z.1 ≥ 2 := by
      intro z hz
      have hz' := (square_mem_iff a u z).mp hz
      omega
    have hd' : (2 : ℕ∞) ≤ setDistance supDist y (↑(square a u) : Set Plane) := by
      apply dist_lower_all a y u 2
      intro z hz
      have hdif := hd z hz
      have habsZ : (2 : ℤ) ≤ (y.1 - z.1).natAbs := by
        rw [Int.natAbs_of_nonneg (by omega : 0 ≤ y.1 - z.1)]
        exact_mod_cast hdif
      have habs : 2 ≤ (y.1 - z.1).natAbs := by exact_mod_cast habsZ
      unfold supDist
      exact le_trans habs (Nat.le_max_left _ _)
    rw [hy] at hd'
    norm_num at hd'
  have hboundLeft1 : a.1 - (u : ℤ) - 1 ≤ y.1 := by
    by_contra hn
    have hd : ∀ z, z ∈ square a u → z.1 - y.1 ≥ 2 := by
      intro z hz
      have hz' := (square_mem_iff a u z).mp hz
      omega
    have hd' : (2 : ℕ∞) ≤ setDistance supDist y (↑(square a u) : Set Plane) := by
      apply dist_lower_all a y u 2
      intro z hz
      have hdif := hd z hz
      have habsZ : (2 : ℤ) ≤ (y.1 - z.1).natAbs := by
        rw [show y.1 - z.1 = -(z.1 - y.1) by omega, Int.natAbs_neg,
          Int.natAbs_of_nonneg (by omega : 0 ≤ z.1 - y.1)]
        exact_mod_cast hdif
      have habs : 2 ≤ (y.1 - z.1).natAbs := by exact_mod_cast habsZ
      unfold supDist
      exact le_trans habs (Nat.le_max_left _ _)
    rw [hy] at hd'
    norm_num at hd'
  have hboundRight2 : y.2 ≤ a.2 + (u : ℤ) + 1 := by
    by_contra hn
    have hd : ∀ z, z ∈ square a u → y.2 - z.2 ≥ 2 := by
      intro z hz
      have hz' := (square_mem_iff a u z).mp hz
      omega
    have hd' : (2 : ℕ∞) ≤ setDistance supDist y (↑(square a u) : Set Plane) := by
      apply dist_lower_all a y u 2
      intro z hz
      have hdif := hd z hz
      have habsZ : (2 : ℤ) ≤ (y.2 - z.2).natAbs := by
        rw [Int.natAbs_of_nonneg (by omega : 0 ≤ y.2 - z.2)]
        exact_mod_cast hdif
      have habs : 2 ≤ (y.2 - z.2).natAbs := by exact_mod_cast habsZ
      unfold supDist
      exact le_trans habs (Nat.le_max_right _ _)
    rw [hy] at hd'
    norm_num at hd'
  have hboundLeft2 : a.2 - (u : ℤ) - 1 ≤ y.2 := by
    by_contra hn
    have hd : ∀ z, z ∈ square a u → z.2 - y.2 ≥ 2 := by
      intro z hz
      have hz' := (square_mem_iff a u z).mp hz
      omega
    have hd' : (2 : ℕ∞) ≤ setDistance supDist y (↑(square a u) : Set Plane) := by
      apply dist_lower_all a y u 2
      intro z hz
      have hdif := hd z hz
      have habsZ : (2 : ℤ) ≤ (y.2 - z.2).natAbs := by
        rw [show y.2 - z.2 = -(z.2 - y.2) by omega, Int.natAbs_neg,
          Int.natAbs_of_nonneg (by omega : 0 ≤ z.2 - y.2)]
        exact_mod_cast hdif
      have habs : 2 ≤ (y.2 - z.2).natAbs := by exact_mod_cast habsZ
      unfold supDist
      exact le_trans habs (Nat.le_max_right _ _)
    rw [hy] at hd'
    norm_num at hd'
  have houtside : y.1 > a.1 + (u : ℤ) ∨ y.1 < a.1 - (u : ℤ) ∨
      y.2 > a.2 + (u : ℤ) ∨ y.2 < a.2 - (u : ℤ) := by
    by_contra hn
    push Not at hn
    exact hnot ((square_mem_iff a u y).2 (by omega))
  rcases houtside with h | h | h | h <;> omega

private def coord (axis : Fin 2) (z : Plane) : ℤ := if axis = 0 then z.1 else z.2

private def otherAxis (axis : Fin 2) : Fin 2 := if axis = 0 then 1 else 0

private def mkPoint (axis : Fin 2) (v w : ℤ) : Plane :=
  if axis = 0 then (v, w) else (w, v)

private lemma coord_square_bounds (axis : Fin 2) (a z : Plane) (u : ℕ)
    (hz : z ∈ square a u) :
    coord axis a - (u : ℤ) ≤ coord axis z ∧
      coord axis z ≤ coord axis a + u := by
  fin_cases axis <;> simp [coord, square_mem_iff] at hz ⊢ <;> omega

private lemma coord_mkPoint (axis : Fin 2) (v w : ℤ) :
    coord axis (mkPoint axis v w) = v := by
  fin_cases axis <;> simp [coord, mkPoint]

private lemma coord_other_mkPoint (axis : Fin 2) (v w : ℤ) :
    coord (otherAxis axis) (mkPoint axis v w) = w := by
  fin_cases axis <;> simp [coord, otherAxis, mkPoint]

private lemma mkPoint_eta (axis : Fin 2) (z : Plane) :
    mkPoint axis (coord axis z) (coord (otherAxis axis) z) = z := by
  fin_cases axis <;> simp [coord, otherAxis, mkPoint]

private lemma supDist_mkPoint (axis : Fin 2) (v w v' w' : ℤ) :
    supDist (mkPoint axis v w) (mkPoint axis v' w') =
      max (v - v').natAbs (w - w').natAbs := by
  fin_cases axis <;> simp [mkPoint, supDist, max_comm]

private lemma natAbs_unit_mul (r ε : ℤ) (hr : 0 ≤ r)
    (hε : ε = 1 ∨ ε = -1) : (ε * r).natAbs = r.toNat := by
  have hbase : r.natAbs = r.toNat := by
    exact_mod_cast (Int.natAbs_of_nonneg hr).trans (Int.toNat_of_nonneg hr).symm
  rcases hε with hε | hε
  · subst ε
    simpa using hbase
  · subst ε
    norm_num
    simpa [Int.natAbs_neg] using hbase

private lemma clearance_failure_extract (a y : Plane) (u : ℕ) (i : ℤ)
    (hn : ¬ ParallelClearance a y u i) :
    ∃ axis : Fin 2, ∃ ε δ : ℤ,
      (ε = 1 ∨ ε = -1) ∧ (δ = 1 ∨ δ = -1) ∧
      ∃ z : Plane, z ∈ square a u ∧
        coord axis z = coord axis y + ε * shellRadius u i ∧
        (supDist z y : ℤ) = shellRadius u i ∧
        ((u : ℤ) + 1 - δ *
          ((coord axis y + ε * shellRadius u i) - coord axis a) : ℤ) <
          shellSpacing u / 3 := by
  dsimp [ParallelClearance] at hn
  push Not at hn
  rcases hn with ⟨axis, ε, δ, hε, hδ, hex, hbad⟩
  rcases hex with ⟨z, hz, hcoord, hrad⟩
  refine ⟨axis, ε, δ, hε, hδ, z, hz, ?_, ?_, ?_⟩
  · simpa [coord] using hcoord
  · exact hrad
  · simpa [coord] using hbad

private lemma badClearance_exceptional (a y : Plane) (u : ℕ) (i : ℤ)
    (s : ℝ) (hsEq : s = shellSpacing u) (hs : 16 ≤ s) (hs4 : s ^ 4 = (u : ℝ))
    (hsScale : s ^ 2 + s < (u : ℝ) / 2)
    (hRLower : 2 * s - 1 < (shellRadius u i : ℝ))
    (hRUpper : (shellRadius u i : ℝ) ≤ s ^ 2 + s)
    (hi : 2 ≤ i) (hiLast : i ≤ lastShellIndex u)
    (extAxis : Fin 2) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (hExt : coord extAxis y = coord extAxis a + σ * ((u : ℤ) + 1))
    (axis : Fin 2) (ε δ : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hδ : δ = 1 ∨ δ = -1) (z : Plane) (hz : z ∈ square a u)
    (hSide : coord axis z = coord axis y + ε * shellRadius u i)
    (hBad : (((u : ℤ) + 1 - δ *
      ((coord axis y + ε * shellRadius u i) - coord axis a) : ℤ) : ℝ) < s / 3) :
    i ∈ exceptionalIndices a y u := by
  rcases hσ with hsigma | hsigma
  all_goals
    let r : ℝ := (shellRadius u i : ℝ)
    have hrPos : (0 : ℝ) ≤ r := by linarith [hRLower]
    have hrOne : (1 : ℝ) ≤ r := by linarith [hs]
    have hrThird : s / 3 ≤ r := by linarith
    have hrUpper : r < (u : ℝ) / 2 := lt_of_le_of_lt hRUpper hsScale
    have hrInt : 0 ≤ shellRadius u i := by
      have hp : (0 : ℝ) ≤ (shellRadius u i : ℝ) := by dsimp [r] at hrPos; exact hrPos
      exact_mod_cast hp
    have hrIntOne : 1 ≤ shellRadius u i := by
      have hp : (1 : ℝ) ≤ (shellRadius u i : ℝ) := by dsimp [r] at hrOne; exact hrOne
      exact_mod_cast hp
    have hsLeU : s ≤ (u : ℝ) := by
      rw [← hs4]
      nlinarith [sq_nonneg (s ^ 2 - 1)]
    have hOppThird : s / 3 ≤ 2 * (u : ℝ) + 2 - r := by linarith
    by_cases hSame : axis = extAxis
    · subst axis
      have hzBounds := coord_square_bounds extAxis a z u hz
      rw [hSide] at hzBounds
      have heps : ε = -σ := by
        rcases hε with hε | hε
        · have hExt' := hExt
          rw [hsigma] at hExt'
          rw [hExt', hε] at hzBounds
          omega
        · have hExt' := hExt
          rw [hsigma] at hExt'
          rw [hExt', hε] at hzBounds
          omega
      have hclearInt : (u : ℤ) + 1 - δ *
          ((coord extAxis y + ε * shellRadius u i) - coord extAxis a) =
          if δ = σ then shellRadius u i else 2 * (u : ℤ) + 2 - shellRadius u i := by
        rcases hδ with hδ | hδ <;> simp [hδ, hExt, heps, hsigma] <;> omega
      have hclearReal : (((u : ℤ) + 1 - δ *
          ((coord extAxis y + ε * shellRadius u i) - coord extAxis a) : ℤ) : ℝ) =
          if δ = σ then r else 2 * (u : ℝ) + 2 - r := by
        rw [hclearInt]
        by_cases hd : δ = σ <;> simp [hd, r]
      have hclearLower : s / 3 ≤ (((u : ℤ) + 1 - δ *
          ((coord extAxis y + ε * shellRadius u i) - coord extAxis a) : ℤ) : ℝ) := by
        rw [hclearReal]
        by_cases hd : δ = σ <;> simp [hd] <;> linarith
      exact False.elim ((not_lt_of_ge hclearLower) hBad)
    · have hAxisOther : axis = otherAxis extAxis := by
        fin_cases extAxis <;> fin_cases axis <;> simp_all [otherAxis]
      let b : ℤ := coord axis y + ε * shellRadius u i
      let x : Plane := mkPoint extAxis (coord extAxis a + σ * (u : ℤ)) b
      let c : Plane := mkPoint extAxis
        (coord extAxis a + σ * (u : ℤ))
        (coord (otherAxis extAxis) a + δ * (u : ℤ))
      have hbBounds : coord (otherAxis extAxis) a - (u : ℤ) ≤ b ∧
          b ≤ coord (otherAxis extAxis) a + u := by
        have hh := coord_square_bounds axis a z u hz
        rw [hSide] at hh
        simpa [hAxisOther, b] using hh
      have hxExtBounds : coord extAxis a - (u : ℤ) ≤ coord extAxis x ∧
          coord extAxis x ≤ coord extAxis a + u := by
        rw [coord_mkPoint]
        rw [hsigma]
        omega
      have hxOtherBounds : coord (otherAxis extAxis) a - (u : ℤ) ≤
          coord (otherAxis extAxis) x ∧ coord (otherAxis extAxis) x ≤
          coord (otherAxis extAxis) a + u := by
        rw [coord_other_mkPoint]
        exact hbBounds
      have hxSquare : x ∈ square a u := by
        rw [square_mem_iff]
        fin_cases extAxis
        · have h1 : a.1 - (u : ℤ) ≤ x.1 ∧ x.1 ≤ a.1 + u := by
            simpa [coord, x, mkPoint] using hxExtBounds
          have h2 : a.2 - (u : ℤ) ≤ x.2 ∧ x.2 ≤ a.2 + u := by
            simpa [coord, otherAxis, x, mkPoint] using hxOtherBounds
          exact ⟨h1.1, h1.2, h2.1, h2.2⟩
        · have h1 : a.1 - (u : ℤ) ≤ x.1 ∧ x.1 ≤ a.1 + u := by
            simpa [coord, otherAxis, x, mkPoint] using hxOtherBounds
          have h2 : a.2 - (u : ℤ) ≤ x.2 ∧ x.2 ≤ a.2 + u := by
            simpa [coord, x, mkPoint] using hxExtBounds
          exact ⟨h1.1, h1.2, h2.1, h2.2⟩
      have hcCorner : c ∈ squareCorners a u := by
        rcases hδ with hd | hd <;> fin_cases extAxis <;>
          simp [c, mkPoint, coord, otherAxis, squareCorners, hd, hsigma] <;> omega
      have hrNatOne : 1 ≤ (shellRadius u i).toNat := by omega
      have hyRep : y = mkPoint extAxis (coord extAxis y)
          (coord (otherAxis extAxis) y) := (mkPoint_eta extAxis y).symm
      have hradX : supDist x y = (shellRadius u i).toNat := by
        rw [hyRep, supDist_mkPoint]
        have heDist :
            (coord extAxis a + σ * (u : ℤ) -
              coord extAxis y).natAbs = 1 := by
          have hdiff : coord extAxis a + σ * (u : ℤ) - coord extAxis y = -σ := by
            rw [hExt]
            ring
          rw [hdiff, hsigma]
          norm_num [Int.natAbs_neg]
        have hoDist : (b - coord (otherAxis extAxis) y).natAbs =
            (shellRadius u i).toNat := by
          have hbo : b - coord (otherAxis extAxis) y = ε * shellRadius u i := by
            dsimp [b]
            rw [hAxisOther]
            ring
          rw [hbo]
          exact natAbs_unit_mul _ _ hrInt hε
        rw [heDist, hoDist]
        simp [Nat.max_eq_right hrNatOne]
      have hradXInt : (supDist x y : ℤ) = shellRadius u i := by
        rw [hradX]
        exact Int.toNat_of_nonneg hrInt
      have hcornerDist :
          (supDist x c : ℝ) < s / 3 := by
        have hclearInt : (u : ℤ) + 1 - δ * (b - coord (otherAxis extAxis) a) <
            (s / 3) := by
          have hBadOther := hBad
          rw [hAxisOther] at hBadOther
          simpa [b, hAxisOther] using hBadOther
        have htLow : -(u : ℤ) ≤ b - coord (otherAxis extAxis) a := by omega
        have htHigh : b - coord (otherAxis extAxis) a ≤ (u : ℤ) := by omega
        have hcornerAbs :
            (b - (coord (otherAxis extAxis) a + δ * (u : ℤ))).natAbs =
              (u : ℤ) - δ * (b - coord (otherAxis extAxis) a) := by
          rcases hδ with hd | hd
          · rw [hd]
            have hp : 0 ≤ (u : ℤ) - (b - coord (otherAxis extAxis) a) := by omega
            have hdiff : b - (coord (otherAxis extAxis) a + 1 * (u : ℤ)) =
                -((u : ℤ) - (b - coord (otherAxis extAxis) a)) := by omega
            rw [hdiff, Int.natAbs_neg, Int.natAbs_of_nonneg hp]
            omega
          · rw [hd]
            have hp : 0 ≤ b - coord (otherAxis extAxis) a + (u : ℤ) := by omega
            have hdiff : b - (coord (otherAxis extAxis) a + (-1) * (u : ℤ)) =
                b - coord (otherAxis extAxis) a + (u : ℤ) := by ring
            rw [hdiff]
            rw [Int.natAbs_of_nonneg hp]
            ring
        have hsup : supDist x c =
            (b - (coord (otherAxis extAxis) a + δ * (u : ℤ))).natAbs := by
          fin_cases extAxis <;> simp [supDist, x, c, mkPoint, coord, otherAxis]
        have hNatAbs :
            ((supDist x c : ℕ) : ℝ) =
              (((u : ℤ) + 1 - δ * (b - coord (otherAxis extAxis) a) : ℤ) : ℝ) - 1 := by
          have hdist : (supDist x c : ℤ) =
              (u : ℤ) + 1 - δ * (b - coord (otherAxis extAxis) a) - 1 := by
            rw [show (supDist x c : ℤ) =
              (b - (coord (otherAxis extAxis) a + δ * (u : ℤ))).natAbs by exact_mod_cast hsup]
            rw [hcornerAbs]
            ring
          exact_mod_cast hdist
        rw [hNatAbs]
        push_cast at hclearInt ⊢
        linarith [hclearInt]
      have hradShell : x ∈ shell a y u i := by
        simp [shell, hxSquare, hradXInt]
      have hcornerDist' : (supDist x c : ℝ) < shellSpacing u / 3 := by
        simpa [hsEq] using hcornerDist
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi, hiLast⟩,
        ⟨x, hradShell, c, hcCorner, hcornerDist'⟩⟩

theorem main : AKLT.Blueprint.Win.SideCornerWitnessStatement := by
  intro l a y u hsetup i hi hiLast hnot
  rcases hsetup with ⟨hl, hu, hy⟩
  let s := shellSpacing u
  have hsEq : s = shellSpacing u := rfl
  have hsBounds := shellScale l u hl hu
  have hs16 : 16 ≤ s := by simpa [s] using hsBounds.1
  have hs4 : s ^ 4 = (u : ℝ) := by simpa [s] using hsBounds.2.1
  have hsScale : s ^ 2 + s < (u : ℝ) / 2 := by simpa [s] using hsBounds.2.2
  have hRBounds := shellRadius_bounds u i hs16 hi hiLast
  obtain ⟨hRLower, hRUpper⟩ := hRBounds
  obtain ⟨axis, ε, δ, hε, hδ, z, hz, hSide, _hRad, hBad⟩ :=
    clearance_failure_extract a y u i hnot
  have hext := exterior_side a y u hy
  rcases hext with h | h | h | h
  · have hExt : coord 0 y = coord 0 a + 1 * ((u : ℤ) + 1) := by
      simp [coord]
      omega
    exact badClearance_exceptional a y u i s hsEq hs16 hs4 hsScale
      hRLower hRUpper hi hiLast 0 1 (by norm_num) hExt axis ε δ hε hδ z hz hSide hBad
  · have hExt : coord 0 y = coord 0 a + (-1) * ((u : ℤ) + 1) := by
      simp [coord]
      omega
    exact badClearance_exceptional a y u i s hsEq hs16 hs4 hsScale
      hRLower hRUpper hi hiLast 0 (-1) (by norm_num) hExt axis ε δ hε hδ z hz hSide hBad
  · have hExt : coord 1 y = coord 1 a + 1 * ((u : ℤ) + 1) := by
      simp [coord]
      omega
    exact badClearance_exceptional a y u i s hsEq hs16 hs4 hsScale
      hRLower hRUpper hi hiLast 1 1 (by norm_num) hExt axis ε δ hε hδ z hz hSide hBad
  · have hExt : coord 1 y = coord 1 a + (-1) * ((u : ℤ) + 1) := by
      simp [coord]
      omega
    exact badClearance_exceptional a y u i s hsEq hs16 hs4 hsScale
      hRLower hRUpper hi hiLast 1 (-1) (by norm_num) hExt axis ε δ hε hδ z hz hSide hBad

end AKLT.W.WIN006

#print axioms AKLT.W.WIN006.main
