import AKLT.W.H1C003.Algebra
import AKLT.W.H1M023.Main
import AKLT.W.H1M043.Main

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1C003

private def ySign (k : Fin 3) : ℚ := if k = 1 then -1 else 1

private def localYSign : LocalVariable → ℚ :=
  Sum.elim (fun v => ySign v.2) (fun v => ySign v.2)

private def vectorYSign (v : Fin 20 × Fin 3) : ℚ := ySign v.2

private theorem reflect_formalDot (a b : Fin 3 → LocalVariable)
    (ha : ∀ k, localYSign (a k) = ySign k)
    (hb : ∀ k, localYSign (b k) = ySign k) :
    scaleVariables localYSign (formalDot a b) = formalDot a b := by
  classical
  unfold formalDot
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul, scaleVariables_X, scaleVariables_X, ha k, hb k]
  by_cases hk : k = 1 <;> simp [ySign, hk]

private theorem reducedIntegrand_reflect (π : PatternData) (r : Representation)
    (next : Bool) :
    scaleVariables localYSign (reducedIntegrand π r next) = reducedIntegrand π r next := by
  have hii (x y : Plane) :
      scaleVariables localYSign
        (formalDot (fun k => .inl (x, k)) (fun k => .inl (y, k))) =
          formalDot (fun k => .inl (x, k)) (fun k => .inl (y, k)) :=
    reflect_formalDot _ _ (fun _ => rfl) (fun _ => rfl)
  have hie (x : Plane) (j : Fin 20) :
      scaleVariables localYSign
        (formalDot (fun k => .inl (x, k)) (fun k => .inr (j, k))) =
          formalDot (fun k => .inl (x, k)) (fun k => .inr (j, k)) :=
    reflect_formalDot _ _ (fun _ => rfl) (fun _ => rfl)
  unfold reducedIntegrand
  simp only [map_mul, map_prod, apply_ite, map_one, map_add, scaleVariables_C, hii, hie]

private theorem moment_nonzero_even_y (m : Fin 3 → ℕ) (h : rationalMoment m ≠ 0) :
    Even (m 1) := by
  have hs : (∑ k : Fin 3, m k) = m 0 + m 1 + m 2 := Fin.sum_univ_three m
  unfold rationalMoment at h
  split_ifs at h with h0 h2 h4 he
  · have hz : m 1 = 0 := by omega
    rw [hz]
    exact Even.zero
  · obtain ⟨hs2, i, hi⟩ := h2
    fin_cases i <;> norm_num at hi
    all_goals have hm : m 1 = 0 ∨ m 1 = 2 := by omega
    all_goals rcases hm with hm | hm <;> rw [hm] <;> decide
  · obtain ⟨hs4, i, hi⟩ := h4
    fin_cases i <;> norm_num at hi
    all_goals have hm : m 1 = 0 ∨ m 1 = 4 := by omega
    all_goals rcases hm with hm | hm <;> rw [hm] <;> decide
  · exact he.2 1
  · exact (h rfl).elim

private theorem statusMoment_nonzero_even_y (s : Status) (m : Fin 3 → ℕ)
    (h : rationalStatusMoment s m ≠ 0) : Even (m 1) := by
  apply moment_nonzero_even_y m
  unfold rationalStatusMoment at h
  split_ifs at h
  · exact (mul_ne_zero_iff.mp h).2
  · exact h

private def externalExponent (m : LocalVariable →₀ ℕ) : (Fin 20 × Fin 3) →₀ ℕ :=
  Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn

private theorem localScale_eq_external (V : Finset Plane) (s : Plane → Status)
    (m : LocalVariable →₀ ℕ)
    (hint : ∀ x, x ∉ V → ∀ k : Fin 3, m (.inl (x, k)) = 0)
    (hmom : (∏ x ∈ V, rationalStatusMoment (s x) (fun k => m (.inl (x, k)))) ≠ 0) :
    monomialScale localYSign m = monomialScale vectorYSign (externalExponent m) := by
  classical
  let mi := Finsupp.comapDomain Sum.inl m Sum.inl_injective.injOn
  have hsupp : mi.support ⊆ V ×ˢ (Finset.univ : Finset (Fin 3)) := by
    intro v hv
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    by_contra hv'
    have hz : mi v = 0 := hint v.1 hv' v.2
    exact (Finsupp.mem_support_iff.mp hv) hz
  have hmi : mi.prod (fun v n => ySign v.2 ^ n) = 1 := by
    rw [Finsupp.prod_of_support_subset mi hsupp _ (fun _ _ => pow_zero _),
      Finset.prod_product]
    apply Finset.prod_eq_one
    intro x hx
    have hnonzero : rationalStatusMoment (s x) (fun k => m (.inl (x, k))) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hmom) x hx
    have he := statusMoment_nonzero_even_y (s x) _ hnonzero
    apply Finset.prod_eq_one
    intro k _
    by_cases hk : k = 1
    · subst k
      change (-1 : ℚ) ^ m (.inl (x, 1)) = 1
      exact he.neg_one_pow
    · simp [ySign, hk]
  have hsplit := Finsupp.comapDomain_sumElim_comapDomain m
  calc
    monomialScale localYSign m =
        monomialScale localYSign (mi.sumElim (externalExponent m)) :=
      congrArg (monomialScale localYSign) hsplit.symm
    _ = mi.prod (fun v n => ySign v.2 ^ n) *
        monomialScale vectorYSign (externalExponent m) := by
      exact Finsupp.prod_sumElim _ _ _
    _ = monomialScale vectorYSign (externalExponent m) := by rw [hmi, one_mul]

private theorem contractSpins_reflect (V : Finset Plane) (s : Plane → Status)
    (p : LocalPolynomial)
    (hint : ∀ m ∈ p.support, ∀ x, x ∉ V → ∀ k : Fin 3, m (.inl (x, k)) = 0)
    (hreflect : scaleVariables localYSign p = p) :
    scaleVariables vectorYSign (contractSpins V s p) = contractSpins V s p := by
  classical
  unfold contractSpins
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [scaleVariables_monomial]
  apply congrArg (MvPolynomial.monomial (externalExponent m))
  change (p.coeff m * ∏ x ∈ V, rationalStatusMoment (s x) (fun k => m (.inl (x, k)))) *
      monomialScale vectorYSign (externalExponent m) =
    p.coeff m * ∏ x ∈ V, rationalStatusMoment (s x) (fun k => m (.inl (x, k)))
  have hc := congrArg (fun q : LocalPolynomial => q.coeff m) hreflect
  rw [coeff_scaleVariables] at hc
  by_cases hzero : (∏ x ∈ V,
      rationalStatusMoment (s x) (fun k => m (.inl (x, k)))) = 0
  · simp [hzero]
  · rw [← localScale_eq_external V s m (hint m hm) hzero]
    calc
      (p.coeff m * ∏ x ∈ V, rationalStatusMoment (s x) (fun k => m (.inl (x, k)))) *
          monomialScale localYSign m =
        (p.coeff m * monomialScale localYSign m) *
          ∏ x ∈ V, rationalStatusMoment (s x) (fun k => m (.inl (x, k))) := by ring
      _ = _ := by rw [hc]

private theorem reducedPolynomial_reflect (π : PatternData) (hπ : π.Covered)
    (r : Representation) (next : Bool) :
    scaleVariables vectorYSign (reducedPolynomial π r next) = reducedPolynomial π r next := by
  apply contractSpins_reflect
  · exact (AKLT.W.H1M023.main π hπ r next).1
  · exact reducedIntegrand_reflect π r next

private theorem scales_commute {σ : Type*} (s t : σ → ℚ) :
    (scaleVariables s).comp (scaleVariables t) =
      (scaleVariables t).comp (scaleVariables s) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, scaleVariables_C]
  · intro v
    simp only [RingHom.comp_apply, scaleVariables_X, map_mul, scaleVariables_C]
    ring

private theorem inverted_reducedPolynomial_reflect (π : PatternData) (hπ : π.Covered)
    (r : Representation) (I : Finset (Fin 20)) (next : Bool) :
    scaleVariables vectorYSign (invertPolynomial I (reducedPolynomial π r next)) =
      invertPolynomial I (reducedPolynomial π r next) := by
  rw [invertPolynomial_eq_scaleVariables]
  have hcomm := RingHom.congr_fun (scales_commute vectorYSign (inversionSign I))
    (reducedPolynomial π r next)
  change scaleVariables vectorYSign (scaleVariables (inversionSign I) _) =
    scaleVariables (inversionSign I) (scaleVariables vectorYSign _) at hcomm
  rw [hcomm, reducedPolynomial_reflect π hπ r next]

private theorem exponent_y_count (J : Finset (Fin 20)) (a : J → Fin 4) :
    monomialScale vectorYSign (pauliExponent J a) = (-1 : ℚ) ^ pauliYCount J a := by
  classical
  have hsupp : ((pauliExponent J a).support.filter (fun v => v.2 = 1)) =
      (Finset.univ.filter (fun j : J => a j = 2)).image
        (fun j => (j.val, (1 : Fin 3))) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Finsupp.mem_support_iff]
    simp [pauliExponent, Finsupp.equivFunOnFinite]
    constructor
    · rintro ⟨⟨hJ, hv⟩, hv2⟩
      refine ⟨v.1, ⟨hJ, ?_⟩, Prod.ext rfl hv2.symm⟩
      apply Fin.ext
      simpa [hv2] using hv
    · rintro ⟨j, ⟨hJ, hj⟩, hp⟩
      have hfirst := congrArg Prod.fst hp
      have hsecond := congrArg Prod.snd hp
      have hJv : v.1 ∈ J := by rw [← hfirst]; exact hJ
      have hsub : (⟨v.1, hJv⟩ : J) = ⟨j, hJ⟩ := Subtype.ext hfirst.symm
      refine ⟨⟨hJv, ?_⟩, hsecond.symm⟩
      have hA : a ⟨v.1, hJv⟩ = 2 := by rw [hsub]; exact hj
      change (a (⟨v.1, hJv⟩ : J)).val = v.2.val + 1
      rw [← hsecond]
      simpa using congrArg Fin.val hA
  have hinj : Function.Injective (fun j : J => (j.val, (1 : Fin 3))) := by
    intro j k h
    exact Subtype.ext (congrArg Prod.fst h)
  have hval : ∀ v ∈ (pauliExponent J a).support, (pauliExponent J a) v = 1 := by
    intro v hv
    simp only [Finsupp.mem_support_iff] at hv
    simp [pauliExponent, Finsupp.equivFunOnFinite] at hv ⊢
    split_ifs <;> simp_all
  calc
    monomialScale vectorYSign (pauliExponent J a) =
        ∏ v ∈ (pauliExponent J a).support, if v.2 = 1 then -1 else 1 := by
      apply Finset.prod_congr rfl
      intro v hv
      simp [vectorYSign, ySign, hval v hv]
    _ = (-1 : ℚ) ^ ((pauliExponent J a).support.filter (fun v => v.2 = 1)).card := by
      simp [Finset.prod_ite]
    _ = (-1 : ℚ) ^ pauliYCount J a := by
      rw [hsupp, Finset.card_image_of_injective _ hinj]
      rfl

theorem inverted_reducedPolynomial_real (π : PatternData) (hπ : π.Covered)
    (r : Representation) (I J : Finset (Fin 20)) (next : Bool) (σ τ : J → Fin 2) :
    (pauliOperator J (invertPolynomial I (reducedPolynomial π r next)) σ τ).im = 0 := by
  apply AKLT.W.H1M043.main
  intro a hodd
  have hc := congrArg (fun p : VectorPolynomial => p.coeff (pauliExponent J a))
    (inverted_reducedPolynomial_reflect π hπ r I next)
  rw [coeff_scaleVariables, exponent_y_count, hodd.neg_one_pow] at hc
  linarith

end AKLT.W.H1C003
