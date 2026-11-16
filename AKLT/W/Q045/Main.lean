import AKLT.Blueprint.Q.NodesQuantum

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.W.Q045

variable {L N : Size}
variable (κ : Site L N → Fin 3) (x : Site L N)

private abbrev Outside (x : Site L N) := {y : Site L N // y ≠ x} → IcoLetter

private def fibreConfig (x : Site L N) (a : IcoLetter) (ω : Outside x) :
    TorusConfiguration L N := fun y => if h : y = x then a else ω ⟨y, h⟩

private def configEquiv (x : Site L N) : TorusConfiguration L N ≃ IcoLetter × Outside x where
  toFun σ := (σ x, fun y => σ y.1)
  invFun p := fibreConfig x p.1 p.2
  left_inv σ := by
    funext y
    by_cases h : y = x
    · subst y
      simp [fibreConfig]
    · simp [fibreConfig, h]
  right_inv p := by
    rcases p with ⟨a, ω⟩
    apply Prod.ext
    · simp [fibreConfig]
    · funext y
      simp [fibreConfig, y.2]

private lemma card_icoLetter : Fintype.card IcoLetter = 12 := by
  norm_num [IcoLetter, Fintype.card_prod]

private lemma sum_update_fibre (g : TorusConfiguration L N → ℝ) :
    ∑ σ, ∑ a : IcoLetter, g (Function.update σ x a) =
      (Fintype.card IcoLetter : ℝ) * ∑ σ, g σ := by
  classical
  let e := configEquiv (L := L) (N := N) x
  have hleft : (∑ σ, ∑ a : IcoLetter, g (Function.update σ x a)) =
      ∑ p : IcoLetter × Outside x, ∑ a : IcoLetter,
        g (fibreConfig x a p.2) := by
    apply Fintype.sum_equiv e
    intro σ
    apply Finset.sum_congr rfl
    intro a _
    have hcfg : Function.update σ x a =
        fibreConfig x a (fun y : {y : Site L N // y ≠ x} => σ y.1) := by
      funext y
      by_cases hy : y = x
      · subst y
        simp [fibreConfig]
      · simp [fibreConfig, hy]
    simpa [e, configEquiv] using congrArg g hcfg
  have hright : (∑ σ, g σ) =
      ∑ p : IcoLetter × Outside x, g (fibreConfig x p.1 p.2) := by
    apply Fintype.sum_equiv e
    intro σ
    have hcfg := (configEquiv (L := L) (N := N) x).left_inv σ
    simpa [e, configEquiv] using congrArg g hcfg.symm
  rw [hleft, hright]
  let F : IcoLetter → Outside x → ℝ := fun a ω => g (fibreConfig x a ω)
  conv_lhs => rw [Fintype.sum_prod_type]
  conv_rhs => arg 2; rw [Fintype.sum_prod_type]
  change (∑ b : IcoLetter, ∑ ω : Outside x, ∑ a : IcoLetter, F a ω) =
    (Fintype.card IcoLetter : ℝ) * ∑ b : IcoLetter, ∑ ω : Outside x, F b ω
  calc
    (∑ b : IcoLetter, ∑ ω : Outside x, ∑ a : IcoLetter, F a ω) =
        ∑ ω : Outside x, ∑ a : IcoLetter, ∑ b : IcoLetter, F a ω := by
      rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
      apply Finset.sum_congr rfl
      intro ω _
      rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    _ = (Fintype.card IcoLetter : ℝ) * ∑ b : IcoLetter, ∑ ω : Outside x, F b ω := by
      calc
        (∑ ω : Outside x, ∑ a : IcoLetter, ∑ b : IcoLetter, F a ω) =
            ∑ ω : Outside x, ∑ a : IcoLetter,
              (Fintype.card IcoLetter : ℝ) * F a ω := by
          apply Finset.sum_congr rfl
          intro ω _
          apply Finset.sum_congr rfl
          intro a _
          simp
        _ = (Fintype.card IcoLetter : ℝ) * ∑ ω : Outside x, ∑ a : IcoLetter, F a ω := by
          simp_rw [← Finset.mul_sum]
        _ = (Fintype.card IcoLetter : ℝ) * ∑ b : IcoLetter, ∑ ω : Outside x, F b ω := by
          congr 1
          exact Finset.sum_comm

private def fibreNumerator (κ : Site L N → Fin 3) (x : Site L N)
    (h : TorusConfiguration L N → ℂ) (σ : TorusConfiguration L N) : ℂ :=
  ∑ a : IcoLetter, (5 / 12 : ℂ) *
    star (AKLT.Blueprint.Q.beta κ x (Function.update σ x a)) *
      h (Function.update σ x a)

private lemma fibreDenominator_pos (hβ : ∀ σ, AKLT.Blueprint.Q.beta κ x σ ≠ 0)
    (σ : TorusConfiguration L N) : 0 < AKLT.Blueprint.Q.fibreDenominator κ x σ := by
  unfold AKLT.Blueprint.Q.fibreDenominator
  apply Finset.sum_pos (fun a ha =>
    mul_pos (by norm_num) (Complex.normSq_pos.mpr (hβ (Function.update σ x a))))
  exact ⟨(0, 0, 0), by simp⟩

private lemma numerator_update (h : TorusConfiguration L N → ℂ) (σ : TorusConfiguration L N)
    (a : IcoLetter) : fibreNumerator κ x h (Function.update σ x a) =
      fibreNumerator κ x h σ := by
  simp [fibreNumerator, Function.update_idem]

private lemma denominator_update (σ : TorusConfiguration L N) (a : IcoLetter) :
    AKLT.Blueprint.Q.fibreDenominator κ x (Function.update σ x a) =
      AKLT.Blueprint.Q.fibreDenominator κ x σ := by
  simp [AKLT.Blueprint.Q.fibreDenominator, Function.update_idem]

private lemma projection_fibre_formula (h : TorusConfiguration L N → ℂ)
    (σ : TorusConfiguration L N) (a : IcoLetter) :
    AKLT.Blueprint.Q.fibreProjection κ x h (Function.update σ x a) =
      AKLT.Blueprint.Q.beta κ x (Function.update σ x a) *
        (fibreNumerator κ x h σ /
          (AKLT.Blueprint.Q.fibreDenominator κ x σ : ℂ)) := by
  change (AKLT.Blueprint.Q.beta κ x (Function.update σ x a) *
      fibreNumerator κ x h (Function.update σ x a)) /
      (AKLT.Blueprint.Q.fibreDenominator κ x (Function.update σ x a) : ℂ) = _
  rw [denominator_update, numerator_update (κ := κ) (x := x)]
  rw [mul_div_assoc]

private lemma fibre_span_projection (h : TorusConfiguration L N → ℂ) :
    AKLT.Blueprint.Q.inFibreSpan κ x (AKLT.Blueprint.Q.fibreProjection κ x h) := by
  intro σ
  refine ⟨fibreNumerator κ x h σ /
    (AKLT.Blueprint.Q.fibreDenominator κ x σ : ℂ), ?_⟩
  intro a
  rw [projection_fibre_formula κ x h σ a]
  ring

private lemma projection_fixed (hβ : ∀ σ, AKLT.Blueprint.Q.beta κ x σ ≠ 0)
    (h : TorusConfiguration L N → ℂ)
    (hk : AKLT.Blueprint.Q.inFibreSpan κ x h) :
    AKLT.Blueprint.Q.fibreProjection κ x h = h := by
  funext σ
  obtain ⟨c, hc⟩ := hk σ
  have hden := fibreDenominator_pos κ x hβ σ
  have hdenC : (AKLT.Blueprint.Q.fibreDenominator κ x σ : ℂ) ≠ 0 :=
    (Complex.ofReal_ne_zero.mpr hden.ne')
  have hnum : fibreNumerator κ x h σ = c *
      (AKLT.Blueprint.Q.fibreDenominator κ x σ : ℂ) := by
    unfold fibreNumerator AKLT.Blueprint.Q.fibreDenominator
    rw [Complex.ofReal_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hc a]
    simp only [Complex.ofReal_mul]
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [starRingEnd_apply]
    ring_nf
    norm_num
  have hval : h σ = c * AKLT.Blueprint.Q.beta κ x σ := by
    simpa using hc (σ x)
  change (AKLT.Blueprint.Q.beta κ x σ * fibreNumerator κ x h σ) /
      (AKLT.Blueprint.Q.fibreDenominator κ x σ : ℂ) = h σ
  rw [hnum]
  field_simp
  rw [hval]
  ring

private def localDenominator (b : IcoLetter → ℂ) : ℝ :=
  ∑ a : IcoLetter, (5 / 12 : ℝ) * Complex.normSq (b a)

private def localNumerator (b h : IcoLetter → ℂ) : ℂ :=
  ∑ a : IcoLetter, ((5 / 12 : ℝ) : ℂ) * star (b a) * h a

private def localCost (b h : IcoLetter → ℂ) (c : ℂ) : ℝ :=
  ∑ a : IcoLetter, (5 / 12 : ℝ) * Complex.normSq (h a - c * b a)

private lemma local_cross_formula (b h : IcoLetter → ℂ) (c : ℂ) :
    ∑ a : IcoLetter, (5 / 12 : ℝ) * (h a * star (c * b a)).re =
      (star c * localNumerator b h).re := by
  have hcoef : (5 / 12 : ℂ) = ((5 / 12 : ℝ) : ℂ) := by norm_num
  calc
    (∑ a : IcoLetter, (5 / 12 : ℝ) * (h a * star (c * b a)).re) =
        (∑ a : IcoLetter, (5 / 12 : ℂ) * (h a * star (c * b a))).re := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [hcoef, Complex.re_ofReal_mul]
    _ = (star c * localNumerator b h).re := by
      congr 1
      unfold localNumerator
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [hcoef]
      simp only [star_mul]
      ring

private lemma localCost_formula (b h : IcoLetter → ℂ) (c : ℂ) :
    localCost b h c =
      (∑ a : IcoLetter, (5 / 12 : ℝ) * Complex.normSq (h a)) +
        localDenominator b * Complex.normSq c -
          2 * (star c * localNumerator b h).re := by
  unfold localCost
  calc
    (∑ a : IcoLetter, (5 / 12 : ℝ) * Complex.normSq (h a - c * b a)) =
        ∑ a : IcoLetter, (5 / 12 : ℝ) *
          (Complex.normSq (h a) + Complex.normSq (c * b a) -
            2 * (h a * star (c * b a)).re) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Complex.normSq_sub]
      rw [Complex.normSq_mul]
      simp only [starRingEnd_apply]
    _ = (∑ a : IcoLetter, (5 / 12 : ℝ) * Complex.normSq (h a)) +
          (∑ a : IcoLetter, (5 / 12 : ℝ) * Complex.normSq (c * b a)) -
            2 * (∑ a : IcoLetter, (5 / 12 : ℝ) * (h a * star (c * b a)).re) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = (∑ a : IcoLetter, (5 / 12 : ℝ) * Complex.normSq (h a)) +
          localDenominator b * Complex.normSq c -
            2 * (star c * localNumerator b h).re := by
      rw [local_cross_formula]
      have hprod : (∑ a : IcoLetter, (5 / 12 : ℝ) * Complex.normSq (c * b a)) =
          ∑ a : IcoLetter, (5 / 12 : ℝ) *
            (Complex.normSq c * Complex.normSq (b a)) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact congrArg (fun r : ℝ => (5 / 12 : ℝ) * r) (Complex.normSq_mul c (b a))
      rw [hprod]
      have hsum : (∑ a : IcoLetter, (5 / 12 : ℝ) *
          (Complex.normSq c * Complex.normSq (b a))) =
          localDenominator b * Complex.normSq c := by
        calc
          (∑ a : IcoLetter, (5 / 12 : ℝ) *
              (Complex.normSq c * Complex.normSq (b a))) =
              ∑ a : IcoLetter, Complex.normSq c *
                ((5 / 12 : ℝ) * Complex.normSq (b a)) := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
          _ = Complex.normSq c * localDenominator b := by
            rw [← Finset.mul_sum]
            rfl
          _ = localDenominator b * Complex.normSq c := by ring
      rw [hsum]

private lemma localCost_pythagorean (b h : IcoLetter → ℂ) (c : ℂ)
    (hD : 0 < localDenominator b) :
    localCost b h c =
      localCost b h (localNumerator b h / (localDenominator b : ℂ)) +
        localDenominator b * Complex.normSq
          (c - localNumerator b h / (localDenominator b : ℂ)) := by
  let α : ℂ := localNumerator b h / (localDenominator b : ℂ)
  have hDne : (localDenominator b : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hD.ne'
  have hN : localNumerator b h = (localDenominator b : ℂ) * α := by
    dsimp [α]
    field_simp
  have hcancel : (localDenominator b : ℂ) * α /
      (localDenominator b : ℂ) = α := by
    field_simp
  have hnorm (z : ℂ) : (Complex.normSq z : ℂ) = star z * z := by
    exact Complex.normSq_eq_conj_mul_self
  have hnormRe (z : ℂ) : (star z * z).re = Complex.normSq z := by
    have hz := congrArg Complex.re (hnorm z)
    simpa using hz.symm
  have hrealCross : (star c * α).re = (c * star α).re := by
    calc
      (star c * α).re = (star (star c * α)).re := by
        symm
        exact Complex.conj_re (star c * α)
      _ = (c * star α).re := by simp [star_mul, mul_comm]
  rw [localCost_formula, localCost_formula]
  change _ = _
  rw [hN, Complex.normSq_sub]
  rw [hcancel]
  rw [show star c * ((localDenominator b : ℂ) * α) =
      (localDenominator b : ℂ) * (star c * α) by ring]
  rw [show star α * ((localDenominator b : ℂ) * α) =
      (localDenominator b : ℂ) * (star α * α) by ring]
  rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  simp only [starRingEnd_apply]
  rw [hnormRe α, hrealCross]
  ring

private lemma localCost_le (b h : IcoLetter → ℂ) (c : ℂ)
    (hD : 0 < localDenominator b) :
    localCost b h (localNumerator b h / (localDenominator b : ℂ)) ≤ localCost b h c := by
  rw [localCost_pythagorean b h c hD]
  exact le_add_of_nonneg_right
    (mul_nonneg (le_of_lt hD) (Complex.normSq_nonneg _))

private lemma weightedNorm_fibreSum (f : TorusConfiguration L N → ℂ) :
    AKLT.Blueprint.Q.weightedNorm (torusReference L N) f =
      ((∏ _y : Site L N, (5 / 12 : ℝ)) / 5) *
        ∑ σ, ∑ a : IcoLetter, (5 / 12 : ℝ) *
          Complex.normSq (f (Function.update σ x a)) := by
  have hsum := sum_update_fibre (L := L) (N := N) x (fun σ => Complex.normSq (f σ))
  rw [card_icoLetter] at hsum
  norm_num at hsum
  have htotal : (∑ σ, ∑ a : IcoLetter, (5 / 12 : ℝ) *
        Complex.normSq (f (Function.update σ x a))) =
      5 * ∑ σ, Complex.normSq (f σ) := by
    calc
      (∑ σ, ∑ a : IcoLetter, (5 / 12 : ℝ) *
          Complex.normSq (f (Function.update σ x a))) =
          (5 / 12 : ℝ) * ∑ σ, ∑ a : IcoLetter,
            Complex.normSq (f (Function.update σ x a)) := by
        calc
          (∑ σ, ∑ a : IcoLetter, (5 / 12 : ℝ) *
              Complex.normSq (f (Function.update σ x a))) =
              ∑ σ, (5 / 12 : ℝ) * ∑ a : IcoLetter,
                Complex.normSq (f (Function.update σ x a)) := by
            apply Finset.sum_congr rfl
            intro σ hσ
            rw [← Finset.mul_sum]
          _ = (5 / 12 : ℝ) * ∑ σ, ∑ a : IcoLetter,
                Complex.normSq (f (Function.update σ x a)) := by
            rw [← Finset.mul_sum]
      _ = (5 / 12 : ℝ) * (12 * ∑ σ, Complex.normSq (f σ)) := by rw [hsum]
      _ = 5 * ∑ σ, Complex.normSq (f σ) := by ring
  rw [AKLT.Blueprint.Q.weightedNorm]
  unfold AKLT.Defs.torusReference
  rw [← Finset.mul_sum, htotal]
  ring

theorem main : AKLT.Blueprint.Q.FibreProjectionStatement := by
  intro L N κ x hβ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ
    exact fibreDenominator_pos κ x hβ σ
  · intro h
    exact fibre_span_projection κ x h
  · intro h hk
    exact projection_fixed κ x hβ h hk
  · intro h k hk
    let P : TorusConfiguration L N → ℂ := AKLT.Blueprint.Q.fibreProjection κ x h
    let r : TorusConfiguration L N → ℂ := h - P
    let q : TorusConfiguration L N → ℂ := h - k
    have hlocal :
        (∑ σ, ∑ a : IcoLetter, (5 / 12 : ℝ) *
          Complex.normSq (r (Function.update σ x a))) ≤
        ∑ σ, ∑ a : IcoLetter, (5 / 12 : ℝ) *
          Complex.normSq (q (Function.update σ x a)) := by
      apply Finset.sum_le_sum
      intro σ hσ
      obtain ⟨c, hc⟩ := hk σ
      let b : IcoLetter → ℂ := fun a =>
        AKLT.Blueprint.Q.beta κ x (Function.update σ x a)
      let g : IcoLetter → ℂ := fun a => h (Function.update σ x a)
      have hD : localDenominator b = AKLT.Blueprint.Q.fibreDenominator κ x σ := by
        rfl
      have hDpos : 0 < localDenominator b := by
        rw [hD]
        exact fibreDenominator_pos κ x hβ σ
      have hN : localNumerator b g = fibreNumerator κ x h σ := by
        unfold localNumerator fibreNumerator b g
        apply Finset.sum_congr rfl
        intro a ha
        norm_num
      have hproj (a : IcoLetter) : P (Function.update σ x a) =
          b a * (localNumerator b g / (localDenominator b : ℂ)) := by
        change AKLT.Blueprint.Q.fibreProjection κ x h (Function.update σ x a) = _
        rw [projection_fibre_formula κ x h σ a]
        rw [hN, hD]
      have hleft : localCost b g
          (localNumerator b g / (localDenominator b : ℂ)) =
          ∑ a : IcoLetter, (5 / 12 : ℝ) *
            Complex.normSq (r (Function.update σ x a)) := by
        unfold localCost
        apply Finset.sum_congr rfl
        intro a ha
        change (5 / 12 : ℝ) * Complex.normSq
            (g a - (localNumerator b g / (localDenominator b : ℂ)) * b a) =
          (5 / 12 : ℝ) * Complex.normSq
            (h (Function.update σ x a) - P (Function.update σ x a))
        rw [hproj a]
        dsimp [g, b]
        congr 2
        ring
      have hright : localCost b g c =
          ∑ a : IcoLetter, (5 / 12 : ℝ) *
            Complex.normSq (q (Function.update σ x a)) := by
        unfold localCost q
        apply Finset.sum_congr rfl
        intro a ha
        rw [Pi.sub_apply, hc a]
      rw [← hleft, ← hright]
      exact localCost_le b g c hDpos
    have hfactor : 0 ≤ ((∏ _y : Site L N, (5 / 12 : ℝ)) / 5) := by positivity
    have hleft := weightedNorm_fibreSum (L := L) (N := N) (x := x) r
    have hright := weightedNorm_fibreSum (L := L) (N := N) (x := x) q
    change AKLT.Blueprint.Q.weightedNorm (torusReference L N) (h - P) ≤
      AKLT.Blueprint.Q.weightedNorm (torusReference L N) (h - k)
    rw [hleft, hright]
    exact mul_le_mul_of_nonneg_left hlocal hfactor

end AKLT.W.Q045
