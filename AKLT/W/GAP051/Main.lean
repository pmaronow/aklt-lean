import AKLT.Blueprint.Gap.NodesShell

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap

namespace AKLT.W.GAP051

private lemma tv_le_offdiag {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (p q : Weight Ω) (c : Coupling p q) :
    totalVariation p q ≤ ∑ x, ∑ y, if x = y then 0 else c.mass x y := by
  classical
  have htotal : (∑ x, p x) = ∑ x, ∑ y, c.mass x y :=
    Finset.sum_congr rfl (fun x _ => (c.first_marginal x).symm)
  have htotal' : (∑ x, q x) = ∑ x, ∑ y, c.mass x y :=
    Eq.trans (Finset.sum_congr rfl (fun y _ => (c.second_marginal y).symm)) Finset.sum_comm
  have hmin x : c.mass x x ≤ min (p x) (q x) := by
    apply le_min
    · rw [← c.first_marginal x]
      exact Finset.single_le_sum (fun y _ => c.nonnegative x y) (Finset.mem_univ x)
    · rw [← c.second_marginal x]
      exact Finset.single_le_sum (fun y _ => c.nonnegative y x) (Finset.mem_univ x)
  have hdiag : (∑ x, c.mass x x) ≤ ∑ x, min (p x) (q x) :=
    Finset.sum_le_sum fun x _ => hmin x
  have hpoint x : |p x - q x| = p x + q x - 2 * min (p x) (q x) := by
    by_cases h : p x ≤ q x
    · rw [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]
      ring
    · have h' : q x ≤ p x := le_of_not_ge h
      rw [abs_of_nonneg (sub_nonneg.mpr h'), min_eq_right h']
      ring
  have htv : totalVariation p q = (∑ x, p x) - ∑ x, min (p x) (q x) := by
    unfold totalVariation
    rw [Finset.sum_congr rfl (fun x _ => hpoint x)]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have heq : (∑ x, p x) = ∑ x, q x := Eq.trans htotal htotal'.symm
    nlinarith
  have hsplit (x y : Ω) : c.mass x y =
      (if x = y then c.mass x y else 0) + (if x = y then 0 else c.mass x y) := by
    by_cases h : x = y <;> simp [h]
  have hrow (x : Ω) : ∑ y, c.mass x y =
      c.mass x x + ∑ y, if x = y then 0 else c.mass x y := by
    rw [show c.mass x x = ∑ y, if x = y then c.mass x y else 0 by simp,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    exact hsplit x y
  have hsplitSum : (∑ x, ∑ y, c.mass x y) =
      (∑ x, c.mass x x) + ∑ x, ∑ y, if x = y then 0 else c.mass x y := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => hrow x)
  nlinarith [htv, htotal, hsplitSum, hdiag]

private def pushCoupling {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] [DecidableEq Ω]
    [DecidableEq Ξ] (p q : Weight Ω) (c : Coupling p q) (r : Ω → Ξ) :
    Coupling (marginal p r) (marginal q r) where
  mass a b := ∑ x, ∑ y, if r x = a ∧ r y = b then c.mass x y else 0
  nonnegative := by
    intro a b
    apply Finset.sum_nonneg
    intro x _
    apply Finset.sum_nonneg
    intro y _
    split_ifs with h
    · exact c.nonnegative x y
    · exact le_of_eq rfl
  first_marginal := by
    intro a
    classical
    simp only [marginal]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext x
      rw [Finset.sum_comm]
    have hcollapse (x y : Ω) :
        (∑ b : Ξ, if r x = a ∧ r y = b then c.mass x y else 0) =
          if r x = a then c.mass x y else 0 := by
      by_cases hx : r x = a <;> simp [hx]
    simp_rw [hcollapse]
    simp only [Finset.sum_ite_irrel]
    simp_rw [c.first_marginal]
    simp
  second_marginal := by
    intro b
    classical
    simp only [marginal]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext x
      rw [Finset.sum_comm]
    have hcollapse (x y : Ω) :
        (∑ a : Ξ, if r x = a ∧ r y = b then c.mass x y else 0) =
          if r y = b then c.mass x y else 0 := by
      by_cases hy : r y = b <;> simp [hy, eq_comm]
    simp_rw [hcollapse]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_irrel]
    simp_rw [c.second_marginal]
    simp

private lemma pushCoupling_offdiag {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    [DecidableEq Ω] [DecidableEq Ξ] (p q : Weight Ω) (c : Coupling p q) (r : Ω → Ξ) :
    (∑ a, ∑ b, if a = b then 0 else (pushCoupling p q c r).mass a b) =
      ∑ x, ∑ y, if r x = r y then 0 else c.mass x y := by
  classical
  simp only [pushCoupling]
  have hdistribute (a b : Ξ) :
      (if a = b then 0 else ∑ x, ∑ y,
        if r x = a ∧ r y = b then c.mass x y else 0) =
      ∑ x, ∑ y, if a = b then 0 else
        if r x = a ∧ r y = b then c.mass x y else 0 := by
    by_cases h : a = b <;> simp [h]
  simp_rw [hdistribute]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext a
    arg 2
    ext x
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext x
    rw [Finset.sum_comm]
  have hcollapse (x y : Ω) :
      (∑ a : Ξ, ∑ b : Ξ,
        if a = b then 0 else if r x = a ∧ r y = b then c.mass x y else 0) =
      if r x = r y then 0 else c.mass x y := by
    rw [← Fintype.sum_prod_type']
    rw [Finset.sum_eq_single (r x, r y)]
    · simp
    · intro z _ hz
      by_cases hdiag : z.1 = z.2
      · simp [hdiag]
      · by_cases hmap : r x = z.1 ∧ r y = z.2
        · have hz' : z = (r x, r y) := by
            rcases hmap with ⟨h₁, h₂⟩
            exact Prod.ext h₁.symm h₂.symm
          exact (hz hz').elim
        · simp [hdiag, hmap]
    · simp
  simp_rw [hcollapse]

theorem main : AKLT.Blueprint.Gap.TerminalRadiusStatement := by
  classical
  intro P l p Mstar α hα hα1 hp hp1 hStopped a u hu y hy η ξ hηξ
  let s : ℝ := shellSpacing u
  let h : ℕ := ⌊s⌋₊
  let W := square a u
  let V : Finset Plane := W.filter fun x => Real.sqrt u < (supDist x y : ℝ)
  let U : Finset (square a u) := farSites a y u ((h : ℝ) * s)
  have hgeom : geometryThreshold l ≤ u := (le_max_right Mstar (geometryThreshold l)).trans hu
  have hM16 : (16 : ℝ) ≤ (max 16 (6 * (l + 1)) : ℕ) := by
    exact_mod_cast (Nat.le_max_left 16 (6 * (l + 1)))
  have hM4 : ((max 16 (6 * (l + 1)) : ℕ) : ℝ) ^ 4 ≤ (u : ℝ) := by
    have hn : (max 16 (6 * (l + 1))) ^ 4 ≤ u := by
      simpa [geometryThreshold] using hgeom
    exact_mod_cast hn
  have hM2 : ((max 16 (6 * (l + 1)) : ℕ) : ℝ) ^ 2 ≤ Real.sqrt (u : ℝ) := by
    apply (Real.le_sqrt (sq_nonneg ((max 16 (6 * (l + 1)) : ℕ) : ℝ))
      (Nat.cast_nonneg u)).2
    nlinarith [hM4]
  have hMle : (max 16 (6 * (l + 1)) : ℕ) ≤ shellSpacing u := by
    dsimp [shellSpacing]
    exact (Real.le_sqrt (Nat.cast_nonneg (max 16 (6 * (l + 1))))
      (Real.sqrt_nonneg (u : ℝ))).2 hM2
  have hs16 : 16 ≤ s := by
    dsimp [s]
    exact le_trans (by exact_mod_cast (Nat.le_max_left 16 (6 * (l + 1)))) hMle
  have hs0 : 0 ≤ s := by dsimp [s]; exact Real.sqrt_nonneg _
  have hh4 : 4 ≤ h := by
    apply Nat.le_floor
    dsimp [s]
    linarith
  have hfloor : (h : ℝ) ≤ s := by
    dsimp [h]
    exact Nat.floor_le hs0
  have hfloorUpper : s < (h : ℝ) + 1 := by
    dsimp [h]
    exact Nat.lt_floor_add_one s
  have hsSq : s ^ 2 = Real.sqrt (u : ℝ) := by
    dsimp [s, shellSpacing]
    exact Real.sq_sqrt (Real.sqrt_nonneg (u : ℝ))
  have hhs : (h : ℝ) * s ≤ Real.sqrt (u : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hfloor hs0]
  have hexp : s - 4 ≤ ((h - 3 : ℕ) : ℝ) := by
    have hcast : ((h - 3 : ℕ) : ℝ) = (h : ℝ) - 3 := by
      rw [Nat.cast_sub (by omega : 3 ≤ h)]
      norm_num
    rw [hcast]
    linarith
  have hsExpPos : 0 < s - 4 := by linarith
  have hVW : V ⊆ W := Finset.filter_subset _ _
  obtain ⟨c, hc⟩ := hStopped a u hu y hy η ξ hηξ h hh4 hfloor
  let r : PlaneConfig P W → PlaneConfig P V := fun σ x => σ ⟨x.val, hVW x.property⟩
  have hfill (b : Config P.Letter) :
      (fun σ : PlaneConfig P W => restrict V (fill P W b σ)) = r := by
    funext σ x
    change (fill P W b σ) x.val = σ ⟨x.val, hVW x.property⟩
    simp [fill, hVW x.property]
  have hspec (b : Config P.Letter) :
      specMarginal P W V b = marginal (P.law W b) r := by
    unfold specMarginal
    rw [hfill b]
  have hU (x : V) : (⟨x.val, hVW x.property⟩ : square a u) ∈ U := by
    simp only [U, farSites, Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_of_le_of_lt hhs (Finset.mem_filter.mp x.property).2
  have hrAgree : ∀ σ τ : PlaneConfig P W, AgreeOn U σ τ → r σ = r τ := by
    intro σ τ hag
    funext x
    exact hag ⟨x.val, hVW x.property⟩ (hU x)
  let d := pushCoupling (P.law W η) (P.law W ξ) c r
  have hTV : totalVariation (marginal (P.law W η) r) (marginal (P.law W ξ) r) ≤
      disagreement c U := by
    calc
      totalVariation (marginal (P.law W η) r) (marginal (P.law W ξ) r) ≤
          ∑ σ, ∑ τ, if σ = τ then 0 else d.mass σ τ := tv_le_offdiag _ _ d
      _ = ∑ σ, ∑ τ, if r σ = r τ then 0 else c.mass σ τ :=
        pushCoupling_offdiag (P.law W η) (P.law W ξ) c r
      _ ≤ disagreement c U := by
        unfold disagreement
        apply Finset.sum_le_sum
        intro σ _
        apply Finset.sum_le_sum
        intro τ _
        by_cases hag : AgreeOn U σ τ
        · have hr : r σ = r τ := hrAgree σ τ hag
          simp [hag, hr]
        · by_cases hr : r σ = r τ <;> simp [hag, hr, c.nonnegative]
  let δ : ℝ := p * α ^ (16 * l)
  let b : ℝ := 1 - δ
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact mul_pos hp (pow_pos hα _)
  have hαpow : α ^ (16 * l) ≤ 1 := pow_le_one₀ hα.le hα1
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    calc
      p * α ^ (16 * l) ≤ 1 * 1 :=
        mul_le_mul hp1 hαpow (pow_nonneg hα.le _) (by norm_num)
      _ = 1 := by norm_num
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have hTVStop : totalVariation
      (specMarginal P W V η) (specMarginal P W V ξ) ≤ b ^ (h - 3 : ℕ) := by
    rw [hspec η, hspec ξ]
    exact hTV.trans hc
  by_cases hbzero : b = 0
  · have hNatZero : b ^ (h - 3 : ℕ) = 0 := by
      rw [hbzero]
      exact zero_pow (by omega)
    have hRealZero : b ^ (s - 4 : ℝ) = 0 := by
      rw [hbzero]
      exact Real.zero_rpow (ne_of_gt hsExpPos)
    rw [hRealZero]
    calc
      totalVariation (specMarginal P W V η) (specMarginal P W V ξ) ≤
          b ^ (h - 3 : ℕ) := hTVStop
      _ = 0 := hNatZero
  · have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hbzero)
    have hPow : b ^ (h - 3 : ℕ) ≤ b ^ (s - 4 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hbpos hb1 hexp
    exact hTVStop.trans hPow

end AKLT.W.GAP051
