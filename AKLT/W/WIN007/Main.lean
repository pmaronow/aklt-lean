import AKLT.Blueprint.Win.NodesShell

noncomputable section

open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN007

private def otherAxis (a : Fin 2) : Fin 2 := ⟨1 - a.val, by omega⟩

private def sideSign (b : Bool) : ℤ := if b then 1 else -1

private def band (a y : Plane) (u l : ℕ) (i : ℤ)
    (j : Fin 2 × Bool × Bool) : Finset Plane := by
  classical
  exact (shell a y u i).filter fun x =>
    coord (otherAxis j.1) x = coord (otherAxis j.1) y +
        sideSign j.2.2 * shellRadius u i ∧
      (u : ℤ) + 1 - sideSign j.2.1 * (coord j.1 x - coord j.1 a) ≤ l

private def bands (a y : Plane) (u l : ℕ) (i : ℤ) : Finset Plane := by
  classical
  exact Finset.univ.biUnion (band a y u l i)

private theorem spacing_gt_third (l u : ℕ)
    (hu : geometryThreshold l ≤ u) :
    (l : ℝ) < shellSpacing u / 3 := by
  let n : ℕ := max 16 (6 * (l + 1))
  have hn : 6 * (l + 1) ≤ n := Nat.le_max_right _ _
  have hpow : n ^ 4 ≤ u := by
    dsimp [n, geometryThreshold] at hu ⊢
    exact hu
  have hnreal : (n : ℝ) ≤ Real.sqrt (Real.sqrt u) := by
    have huR : (n : ℝ) ^ 4 ≤ (u : ℝ) := by exact_mod_cast hpow
    have h1 : (n : ℝ) ^ 2 ≤ Real.sqrt (u : ℝ) := by
      apply (Real.le_sqrt (sq_nonneg (n : ℝ)) (by positivity)).2
      nlinarith [Real.sq_sqrt (show 0 ≤ (u : ℝ) by positivity)]
    exact (Real.le_sqrt (by positivity) (Real.sqrt_nonneg _)).2 h1
  have hnreal' : 6 * ((l : ℝ) + 1) ≤ shellSpacing u := by
    dsimp [shellSpacing]
    calc
      6 * ((l : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hn
      _ ≤ Real.sqrt (Real.sqrt (u : ℝ)) := hnreal
  have hl0 : 0 ≤ (l : ℝ) := Nat.cast_nonneg _
  nlinarith [hnreal']

private theorem exists_exterior_witness (a x : Plane) (u l : ℕ)
    (h : setDistance supDist x {z | z ∉ square a u} ≤ (l : ℕ∞)) :
    ∃ z, z ∉ square a u ∧ supDist x z ≤ l := by
  have hlt : setDistance supDist x {z | z ∉ square a u} < ((l + 1 : ℕ) : ℕ∞) := by
    apply lt_of_le_of_lt h
    exact_mod_cast Nat.lt_succ_self l
  rw [setDistance, iInf_lt_iff] at hlt
  obtain ⟨z, hz⟩ := hlt
  refine ⟨z.val, z.property, ?_⟩
  have hz' : supDist x z.val < l + 1 := by exact_mod_cast hz
  omega

private theorem near_side (a x : Plane) (u l : ℕ)
    (hx : x ∈ square a u)
    (hd : setDistance supDist x {z | z ∉ square a u} ≤ (l : ℕ∞)) :
    ∃ α : Fin 2, ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧
      (u : ℤ) + 1 - δ * (coord α x - coord α a) ≤ l := by
  obtain ⟨z, hzout, hdist⟩ := exists_exterior_witness a x u l hd
  have hx' : (a.1 - (u : ℤ) ≤ x.1 ∧ x.1 ≤ a.1 + u) ∧
      (a.2 - (u : ℤ) ≤ x.2 ∧ x.2 ≤ a.2 + u) := by
    simpa [square, Finset.mem_product, Finset.mem_Icc] using hx
  have hx1 : a.1 - (u : ℤ) ≤ x.1 ∧ x.1 ≤ a.1 + u := by omega
  have hx2 : a.2 - (u : ℤ) ≤ x.2 ∧ x.2 ≤ a.2 + u := by omega
  have hzout' : ¬ ((a.1 - (u : ℤ) ≤ z.1 ∧ z.1 ≤ a.1 + u) ∧
      (a.2 - (u : ℤ) ≤ z.2 ∧ z.2 ≤ a.2 + u)) := by
    simpa [square, Finset.mem_product, Finset.mem_Icc] using hzout
  have hz' : z.1 < a.1 - (u : ℤ) ∨ a.1 + u < z.1 ∨
      z.2 < a.2 - (u : ℤ) ∨ a.2 + u < z.2 := by
    push Not at hzout'
    omega
  have hdx : |x.1 - z.1| ≤ l := by
    have hh : (x.1 - z.1).natAbs ≤ l := (max_le_iff.mp hdist).1
    have hh' : ((x.1 - z.1).natAbs : ℤ) ≤ l := by exact_mod_cast hh
    simpa [Int.natCast_natAbs] using hh'
  have hdy : |x.2 - z.2| ≤ l := by
    have hh : (x.2 - z.2).natAbs ≤ l := (max_le_iff.mp hdist).2
    have hh' : ((x.2 - z.2).natAbs : ℤ) ≤ l := by exact_mod_cast hh
    simpa [Int.natCast_natAbs] using hh'
  rcases hz' with hleft | hright | hbottom | htop
  · refine ⟨0, -1, by norm_num, ?_⟩
    have hp : 0 ≤ x.1 - z.1 := by omega
    rw [abs_of_nonneg hp] at hdx
    dsimp [coord]
    nlinarith
  · refine ⟨0, 1, by norm_num, ?_⟩
    have hp : 0 ≤ z.1 - x.1 := by omega
    have hh : |z.1 - x.1| ≤ l := by simpa [abs_sub_comm] using hdx
    rw [abs_of_nonneg hp] at hh
    dsimp [coord]
    nlinarith
  · refine ⟨1, -1, by norm_num, ?_⟩
    have hp : 0 ≤ x.2 - z.2 := by omega
    rw [abs_of_nonneg hp] at hdy
    dsimp [coord]
    nlinarith
  · refine ⟨1, 1, by norm_num, ?_⟩
    have hp : 0 ≤ z.2 - x.2 := by omega
    have hh : |z.2 - x.2| ≤ l := by simpa [abs_sub_comm] using hdy
    rw [abs_of_nonneg hp] at hh
    dsimp [coord]
    nlinarith

private theorem shell_side (x y : Plane) (k : ℤ)
    (hk : (supDist x y : ℤ) = k) :
    ∃ β : Fin 2, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      coord β x = coord β y + ε * k := by
  have hkabs : max |x.1 - y.1| |x.2 - y.2| = k := by
    simpa [supDist, Int.natCast_natAbs] using hk
  have hk0 : 0 ≤ k := by
    have hnonneg : (0 : ℤ) ≤ (supDist x y : ℤ) := by positivity
    omega
  have h1 : |x.1 - y.1| ≤ k := by
    have := le_max_left |x.1 - y.1| |x.2 - y.2|
    rw [hkabs] at this
    exact this
  have h2 : |x.2 - y.2| ≤ k := by
    have := le_max_right |x.1 - y.1| |x.2 - y.2|
    rw [hkabs] at this
    exact this
  by_cases heq : |x.1 - y.1| = k
  · rcases (abs_eq hk0).mp heq with h | h
    · refine ⟨0, 1, by norm_num, ?_⟩
      dsimp [coord]
      omega
    · refine ⟨0, -1, by norm_num, ?_⟩
      dsimp [coord]
      omega
  · have hlt : |x.1 - y.1| < k := lt_of_le_of_ne h1 heq
    have heq2 : |x.2 - y.2| = k := by
      by_contra hn
      have hlt2 : |x.2 - y.2| < k := lt_of_le_of_ne h2 hn
      have hm : max |x.1 - y.1| |x.2 - y.2| < k := max_lt hlt hlt2
      rw [hkabs] at hm
      exact (lt_irrefl k hm)
    rcases (abs_eq hk0).mp heq2 with h | h
    · refine ⟨1, 1, by norm_num, ?_⟩
      dsimp [coord]
      omega
    · refine ⟨1, -1, by norm_num, ?_⟩
      dsimp [coord]
      omega

private theorem otherAxis_ne (α : Fin 2) : otherAxis α ≠ α := by
  intro h
  have hv := congrArg Fin.val h
  simp [otherAxis] at hv
  omega

private theorem square_coord_bounds (a x : Plane) (u : ℕ) (α : Fin 2)
    (hx : x ∈ square a u) :
    coord α a - u ≤ coord α x ∧ coord α x ≤ coord α a + u := by
  by_cases hα : α = 0
  · subst α
    have hh : (a.1 ≤ x.1 + u ∧ x.1 ≤ a.1 + u) ∧
        (a.2 ≤ x.2 + u ∧ x.2 ≤ a.2 + u) := by
      simpa [square, Finset.mem_product, Finset.mem_Icc] using hx
    dsimp [coord]
    omega
  · have hα1 : α = 1 := by
      apply Fin.ext
      have hv := α.isLt
      have hne : α.val ≠ 0 := by intro h; apply hα; exact Fin.ext h
      omega
    subst α
    have hh : (a.1 ≤ x.1 + u ∧ x.1 ≤ a.1 + u) ∧
        (a.2 ≤ x.2 + u ∧ x.2 ≤ a.2 + u) := by
      simpa [square, Finset.mem_product, Finset.mem_Icc] using hx
    dsimp [coord]
    omega

private theorem coord_pair_inj {α β : Fin 2} (hab : α ≠ β) {x z : Plane}
    (hα : coord α x = coord α z) (hβ : coord β x = coord β z) : x = z := by
  by_cases hα0 : α = 0
  · subst α
    have hβ1 : β = 1 := by
      apply Fin.ext
      have hv := β.isLt
      have hb0 : β.val ≠ 0 := by intro h; apply hab; exact Fin.ext h.symm
      omega
    subst β
    dsimp [coord] at hα hβ
    exact Prod.ext hα hβ
  · have hα1 : α = 1 := by
      apply Fin.ext
      have hv := α.isLt
      have hne : α.val ≠ 0 := by intro h; apply hα0; exact Fin.ext h
      omega
    subst α
    have hβ0 : β = 0 := by
      apply Fin.ext
      have hv := β.isLt
      have hne : β.val ≠ 1 := by intro h; apply hab; apply Fin.ext; omega
      omega
    subst β
    dsimp [coord] at hα hβ
    exact Prod.ext hβ hα

private theorem band_card_le (a y : Plane) (u l : ℕ) (i : ℤ)
    (j : Fin 2 × Bool × Bool) : (band a y u l i j).card ≤ l := by
  classical
  let α := j.1
  let β := otherAxis α
  let δ := sideSign j.2.1
  let ε := sideSign j.2.2
  have hαβ : α ≠ β := by
    dsimp [β]
    exact (otherAxis_ne α).symm
  have hδε : δ = 1 ∨ δ = -1 := by
    dsimp [δ, sideSign]
    cases j.2.1 <;> simp
  have hsign : ε = 1 ∨ ε = -1 := by
    dsimp [ε, sideSign]
    cases j.2.2 <;> simp
  let lo : ℤ := if δ = 1 then coord j.1 a + u + 1 - l else coord j.1 a - u
  let hi : ℤ := if δ = 1 then coord j.1 a + u else coord j.1 a - u + l - 1
  have hmem : ∀ x ∈ band a y u l i j, coord α x ∈ Finset.Icc lo hi := by
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).1
    have hb := (Finset.mem_filter.mp hx).2
    have hsquare : x ∈ square a u := (Finset.mem_filter.mp hx').1
    have hsquare' := square_coord_bounds a x u j.1 hsquare
    have hδ := hb.2
    have hδ' : (u : ℤ) + 1 - sideSign j.2.1 *
        (coord j.1 x - coord j.1 a) ≤ l := hδ
    have hval : coord α x ∈ Finset.Icc lo hi := by
      change coord j.1 x ∈ Finset.Icc lo hi
      simp only [Finset.mem_Icc, lo, hi]
      rcases hδε with h | h
      · have hd : sideSign j.2.1 = 1 := by simpa [δ] using h
        simp only [hd] at hδ'
        constructor <;> omega
      · have hd : sideSign j.2.1 = -1 := by simpa [δ] using h
        simp only [hd] at hδ'
        constructor <;> omega
    exact hval
  have hinj : Set.InjOn (coord α) (↑(band a y u l i j)) := by
    intro x hx z hz heq
    have hx' := (Finset.mem_filter.mp hx).2.1
    have hz' := (Finset.mem_filter.mp hz).2.1
    have hβ : coord β x = coord β z := by rw [hx', hz']
    have hα : coord α x = coord α z := heq
    exact coord_pair_inj hαβ heq hβ
  have hcard : (band a y u l i j).card ≤ (Finset.Icc lo hi).card :=
    Finset.card_le_card_of_injOn (coord α) hmem hinj
  have hinterval : (Finset.Icc lo hi).card = l := by
    rcases hδε with h | h
    · have hd : sideSign j.2.1 = 1 := by simpa [δ] using h
      have hlen : hi + 1 - lo = (l : ℤ) := by
        dsimp [lo, hi]
        simp [δ, h]
      rw [Int.card_Icc, hlen]
      simp
    · have hd : sideSign j.2.1 = -1 := by simpa [δ] using h
      have hlen : hi + 1 - lo = (l : ℤ) := by
        dsimp [lo, hi]
        simp [δ, h]
      rw [Int.card_Icc, hlen]
      simp
  omega

private theorem near_subset_bands (a y : Plane) (u l : ℕ) (i : ℤ)
    (hclear : ParallelClearance a y u i)
    (hnear : (l : ℝ) < shellSpacing u / 3) : nearShell a y u l i ⊆ bands a y u l i := by
  classical
  intro x hx
  have hx' : x ∈ shell a y u i ∧
      setDistance supDist x {z | z ∉ square a u} ≤ (l : ℕ∞) := by
    simpa [nearShell, Finset.mem_filter] using hx
  have hxShell := Finset.mem_filter.mp hx'.1
  obtain ⟨α, δ, hδ, hstrip⟩ := near_side a x u l hxShell.1 hx'.2
  obtain ⟨β, ε, hε, hside⟩ := shell_side x y (shellRadius u i) hxShell.2
  have hperp : α ≠ β := by
    intro heq
    subst β
    have hmeet : ∃ z ∈ square a u,
        coord α z = coord α y + ε * shellRadius u i ∧
          (supDist z y : ℤ) = shellRadius u i :=
      ⟨x, hxShell.1, hside, hxShell.2⟩
    have hc := hclear α ε δ hε hδ hmeet
    have hc' : shellSpacing u / 3 ≤
        (u : ℝ) + 1 - (δ : ℝ) * ((coord α x : ℝ) - (coord α a : ℝ)) := by
      have hsideR : (coord α x : ℝ) = (coord α y : ℝ) +
          (ε : ℝ) * (shellRadius u i : ℝ) := by exact_mod_cast hside
      have hc0 := hc
      push_cast at hc0
      have hsideR' : (if α = 0 then (x.1 : ℝ) else (x.2 : ℝ)) =
          (if α = 0 then (y.1 : ℝ) else (y.2 : ℝ)) +
            (ε : ℝ) * (shellRadius u i : ℝ) := by
        simpa [coord] using hsideR
      rw [← hsideR'] at hc0
      simpa [coord] using hc0
    have hs : (l : ℝ) < shellSpacing u / 3 := hnear
    have hstripR : (u : ℝ) + 1 - (δ : ℝ) * ((coord α x : ℝ) - (coord α a : ℝ)) ≤ (l : ℝ) := by
      exact_mod_cast hstrip
    exact (not_le_of_gt hs) (hc'.trans hstripR)
  have hβ : β = otherAxis α := by
    by_cases hα : α = 0
    · subst α
      have hβ1 : β = 1 := by
        apply Fin.ext
        have hv := β.isLt
        have hb0 : β.val ≠ 0 := by intro h; apply hperp; exact Fin.ext h.symm
        omega
      subst β
      simp [otherAxis]
    · have hα1 : α = 1 := by
        apply Fin.ext
        have hv := α.isLt
        have hne : α.val ≠ 0 := by intro h; apply hα; exact Fin.ext h
        omega
      subst α
      have hβ0 : β = 0 := by
        apply Fin.ext
        have hv := β.isLt
        have hne : β.val ≠ 1 := by intro h; apply hperp; apply Fin.ext; omega
        omega
      subst β
      simp [otherAxis]
  have hxband : x ∈ band a y u l i (α, (δ = 1), (ε = 1)) := by
    have hδ' : δ = sideSign (δ = 1) := by rcases hδ with h | h <;> simp [sideSign, h]
    have hε' : ε = sideSign (ε = 1) := by rcases hε with h | h <;> simp [sideSign, h]
    apply Finset.mem_filter.mpr
    refine ⟨hx'.1, ?_⟩
    constructor
    · have hside' : coord (otherAxis α) x =
          coord (otherAxis α) y + sideSign (ε = 1) * shellRadius u i := by
        have hh := hside
        rw [hβ, hε'] at hh
        exact hh
      exact hside'
    · rw [← hδ']
      exact hstrip
  exact Finset.mem_biUnion.mpr ⟨(α, (δ = 1), (ε = 1)), Finset.mem_univ _, hxband⟩

theorem main : AKLT.Blueprint.Win.NearShellCountStatement := by
  intro l a y u hsetup i hi hlast hclear
  rcases hsetup with ⟨_, hu, _⟩
  have hscale := spacing_gt_third l u hu
  have hsub : nearShell a y u l i ⊆ bands a y u l i :=
    near_subset_bands a y u l i hclear hscale
  have hcard : (bands a y u l i).card ≤ 8 * l := by
    calc
      (bands a y u l i).card ≤ ∑ j ∈ (Finset.univ : Finset (Fin 2 × Bool × Bool)),
          (band a y u l i j).card := Finset.card_biUnion_le
      _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin 2 × Bool × Bool)), l := by
        apply Finset.sum_le_sum
        intro j hj
        exact band_card_le a y u l i j
      _ = 8 * l := by simp
  exact le_trans (Finset.card_le_card hsub) hcard

end AKLT.W.WIN007

#print axioms AKLT.W.WIN007.main
