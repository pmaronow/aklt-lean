import AKLT.Blueprint.H1.NodesPassage

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.H1

namespace AKLT.W.H1M012

private abbrev InternalExp := (Plane × Fin 3) →₀ ℕ
private abbrev ExternalExp := (Fin 20 × Fin 3) →₀ ℕ

private def internalPart (m : LocalVariable →₀ ℕ) : InternalExp :=
  Finsupp.comapDomain Sum.inl m Sum.inl_injective.injOn

private def externalPart (m : LocalVariable →₀ ℕ) : ExternalExp :=
  Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn

private def internalMonomialValue (a : InternalExp) (n : Plane → Vec3) : ℝ :=
  a.prod fun z e => n z.1 z.2 ^ e

private def externalMonomialValue (a : ExternalExp) (u : Fin 20 → Vec3) : ℝ :=
  a.prod fun z e => u z.1 z.2 ^ e

private theorem exponent_split (m : LocalVariable →₀ ℕ) :
    (internalPart m).sumElim (externalPart m) = m := by
  exact Finsupp.comapDomain_sumElim_comapDomain m

private theorem local_monomial_eval (m : LocalVariable →₀ ℕ)
    (n : Plane → Vec3) (u : Fin 20 → Vec3) :
    MvPolynomial.eval₂ (Rat.castHom ℝ)
      (fun v => match v with
        | .inl (x, k) => n x k
        | .inr (j, k) => u j k)
      (MvPolynomial.monomial m (1 : ℚ)) =
      internalMonomialValue (internalPart m) n * externalMonomialValue (externalPart m) u := by
  rw [MvPolynomial.eval₂_monomial, ← exponent_split m, Finsupp.prod_sumElim]
  have hi : internalPart ((internalPart m).sumElim (externalPart m)) = internalPart m := by
    simp [internalPart]
  have he : externalPart ((internalPart m).sumElim (externalPart m)) = externalPart m := by
    simp [externalPart]
  rw [hi, he]
  simp only [map_one, one_mul]
  congr 1

private theorem local_coeff_monomial_eval (m : LocalVariable →₀ ℕ) (c : ℚ)
    (n : Plane → Vec3) (u : Fin 20 → Vec3) :
    localEvaluation (MvPolynomial.monomial m c) n u =
      (c : ℝ) * internalMonomialValue (internalPart m) n *
        externalMonomialValue (externalPart m) u := by
  unfold localEvaluation
  rw [MvPolynomial.eval₂_monomial, ← exponent_split m, Finsupp.prod_sumElim]
  have hi : internalPart ((internalPart m).sumElim (externalPart m)) = internalPart m := by
    simp [internalPart]
  have he : externalPart ((internalPart m).sumElim (externalPart m)) = externalPart m := by
    simp [externalPart]
  rw [hi, he]
  have hI :
      (internalPart m).prod
        ((fun v e => (match v with
          | .inl (x, k) => n x k
          | .inr (j, k) => u j k) ^ e) ∘ Sum.inl) =
        internalMonomialValue (internalPart m) n := by
    unfold internalMonomialValue Finsupp.prod
    apply Finset.prod_congr rfl
    intro z hz
    rfl
  have hE :
      (externalPart m).prod
        ((fun v e => (match v with
          | .inl (x, k) => n x k
          | .inr (j, k) => u j k) ^ e) ∘ Sum.inr) =
        externalMonomialValue (externalPart m) u := by
    unfold externalMonomialValue Finsupp.prod
    apply Finset.prod_congr rfl
    intro z hz
    rfl
  have hprod :
      ((internalPart m).prod
          ((fun v e => (match v with
            | .inl (x, k) => n x k
            | .inr (j, k) => u j k) ^ e) ∘ Sum.inl)) *
        ((externalPart m).prod
          ((fun v e => (match v with
            | .inl (x, k) => n x k
            | .inr (j, k) => u j k) ^ e) ∘ Sum.inr)) =
      internalMonomialValue (internalPart m) n * externalMonomialValue (externalPart m) u :=
    congrArg₂ (fun a b : ℝ => a * b) hI hE
  calc
    _ = (c : ℝ) * (internalMonomialValue (internalPart m) n *
          externalMonomialValue (externalPart m) u) := congrArg (fun z : ℝ => (c : ℝ) * z) hprod
    _ = _ := by ring

private theorem internal_monomial_value_eq_prod (V : Finset Plane)
    (m : LocalVariable →₀ ℕ)
    (hm : ∀ x ∉ V, ∀ k : Fin 3, (internalPart m) (x, k) = 0)
    (n : V → SpinLetter) :
    internalMonomialValue (internalPart m) (supportSpins V n) =
      ∏ x : V, ∏ k : Fin 3,
        spinVector (n x) k ^ m (.inl (x.1, k)) := by
  classical
  -- The exponent support lies in V × Fin 3; complete the product by unit factors.
  let a := internalPart m
  have hsub : a.support ⊆ V ×ˢ (Finset.univ : Finset (Fin 3)) := by
    intro z hz
    have hz' : a z ≠ 0 := (Finsupp.mem_support_iff.mp hz)
    have hx : z.1 ∈ V := by
      by_contra hnot
      have hzero := hm z.1 hnot z.2
      exact hz' (by simpa [a, internalPart] using hzero)
    exact Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩
  have hprod :
      a.prod (fun z e => (supportSpins V n) z.1 z.2 ^ e) =
        ∏ z ∈ V ×ˢ (Finset.univ : Finset (Fin 3)),
          (supportSpins V n) z.1 z.2 ^ a z := by
    unfold Finsupp.prod
    exact Finset.prod_subset_one_on_sdiff hsub
      (by
        intro z hz
        rcases Finset.mem_sdiff.mp hz with ⟨_, hznot⟩
        have hz0 : a z = 0 := by
          by_contra hn
          exact hznot (Finsupp.mem_support_iff.mpr hn)
        simp [hz0])
      (by intro z hz; rfl)
  rw [internalMonomialValue, hprod, Finset.prod_product]
  calc
    (∏ x ∈ V, ∏ k ∈ (Finset.univ : Finset (Fin 3)),
        supportSpins V n x k ^ a (x, k)) =
      ∏ x : V, ∏ k : Fin 3, supportSpins V n x.1 k ^ a (x.1, k) := by
        rw [Finset.prod_subtype (p := fun x : Plane => x ∈ V) V (by intro x; rfl)]
    _ = ∏ x : V, ∏ k : Fin 3, spinVector (n x) k ^ m (.inl (x.1, k)) := by
      apply Finset.prod_congr rfl
      intro x hx
      apply Finset.prod_congr rfl
      intro k hk
      have hx' : x.1 ∈ V := x.property
      simp [supportSpins, hx', a]
      change spinVector (n x) k ^ m (.inl (x.1, k)) = _
      rfl

private theorem site_monomial_sum (M : AKLT.Blueprint.H1.MonomialMoments)
    (s : Status) (hs : s = .U ∨ s = .D) (e : Fin 3 → ℕ)
    (he : (∑ k, e k) ≤ 4) :
    (∑ a : SpinLetter, spinWeight s a *
      ∏ k : Fin 3, spinVector a k ^ e k) =
      (rationalStatusMoment s e : ℝ) := by
  simpa [siteFunctional] using M e he s hs

private theorem weighted_site_factorization (V : Finset Plane) (s : Plane → Status)
    (φ : V → SpinLetter → ℝ) :
    (∑ n : V → SpinLetter,
      (∏ x : V, spinWeight (s x.1) (n x)) * ∏ x : V, φ x (n x)) =
      ∏ x : V, ∑ a : SpinLetter, spinWeight (s x.1) a * φ x a := by
  classical
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun x a => spinWeight (s x.1) a * φ x a)).symm

private theorem raw_monomial_contraction
    (M : AKLT.Blueprint.H1.MonomialMoments) (V : Finset Plane)
    (s : Plane → Status) (hs : ∀ x ∈ V, s x = .U ∨ s x = .D)
    (m : LocalVariable →₀ ℕ) (c : ℚ)
    (hm0 : ∀ x ∉ V, ∀ k : Fin 3, m (.inl (x, k)) = 0)
    (hm4 : ∀ x, (∑ k : Fin 3, m (.inl (x, k))) ≤ 4)
    (u : Fin 20 → Vec3) :
    (∑ n : V → SpinLetter,
      (∏ x : V, spinWeight (s x.1) (n x)) *
        localEvaluation (MvPolynomial.monomial m c) (supportSpins V n) u) =
      (c : ℝ) * externalMonomialValue (externalPart m) u *
        ∏ x : V, (rationalStatusMoment (s x.1)
          (fun k => m (.inl (x.1, k))) : ℝ) := by
  classical
  let φ : V → SpinLetter → ℝ := fun x a =>
    ∏ k : Fin 3, spinVector a k ^ m (.inl (x.1, k))
  have heval (n : V → SpinLetter) :
      localEvaluation (MvPolynomial.monomial m c) (supportSpins V n) u =
        (c : ℝ) * externalMonomialValue (externalPart m) u *
          ∏ x : V, φ x (n x) := by
    rw [local_coeff_monomial_eval m c (supportSpins V n) u,
      internal_monomial_value_eq_prod V m
      (by intro x hx k; simpa [internalPart] using hm0 x hx k) n]
    simp [φ]
    ring
  calc
    _ = ∑ n : V → SpinLetter,
          (∏ x : V, spinWeight (s x.1) (n x)) *
            ((c : ℝ) * externalMonomialValue (externalPart m) u *
              ∏ x : V, φ x (n x)) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [heval n]
    _ = (c : ℝ) * externalMonomialValue (externalPart m) u *
          ∑ n : V → SpinLetter,
            (∏ x : V, spinWeight (s x.1) (n x)) * ∏ x : V, φ x (n x) := by
          have hterms : ∀ n : V → SpinLetter,
              (∏ x : V, spinWeight (s x.1) (n x)) *
                ((c : ℝ) * externalMonomialValue (externalPart m) u *
                  ∏ x : V, φ x (n x)) =
                ((c : ℝ) * externalMonomialValue (externalPart m) u) *
                  ((∏ x : V, spinWeight (s x.1) (n x)) * ∏ x : V, φ x (n x)) := by
            intro n
            ring
          simp_rw [hterms]
          rw [← Finset.mul_sum]
    _ = (c : ℝ) * externalMonomialValue (externalPart m) u *
          ∏ x : V, ∑ a : SpinLetter, spinWeight (s x.1) a * φ x a := by
          rw [weighted_site_factorization]
    _ = (c : ℝ) * externalMonomialValue (externalPart m) u *
          ∏ x : V, (rationalStatusMoment (s x.1)
            (fun k => m (.inl (x.1, k))) : ℝ) := by
          apply congrArg (fun z : ℝ => (c : ℝ) *
            externalMonomialValue (externalPart m) u * z)
          apply Finset.prod_congr rfl
          intro x hx
          have hdeg := hm4 x.1
          simpa [φ] using site_monomial_sum M (s x.1) (hs x.1 x.property)
            (fun k => m (.inl (x.1, k))) hdeg

private theorem local_eval_sum (p : LocalPolynomial) (n : Plane → Vec3)
    (u : Fin 20 → Vec3) :
    localEvaluation p n u =
      ∑ m ∈ p.support,
        localEvaluation (MvPolynomial.monomial m (p.coeff m)) n u := by
  classical
  unfold localEvaluation
  let f : LocalVariable → ℝ := fun v =>
    match v with
    | .inl (x, k) => n x k
    | .inr (j, k) => u j k
  change MvPolynomial.eval₂ (Rat.castHom ℝ) f p = _
  calc
    _ = MvPolynomial.eval₂ (Rat.castHom ℝ) f
          (∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m)) :=
        congrArg (MvPolynomial.eval₂ (Rat.castHom ℝ) f) p.as_sum
    _ = ∑ m ∈ p.support,
          MvPolynomial.eval₂ (Rat.castHom ℝ) f
            (MvPolynomial.monomial m (p.coeff m)) := MvPolynomial.eval₂_sum _ _ _ _

private theorem evaluateReduced_monomial (a : ExternalExp) (c : ℚ)
    (u : Fin 20 → Vec3) :
    evaluateReduced (MvPolynomial.monomial a c) u =
      (c : ℝ) * externalMonomialValue a u := by
  unfold evaluateReduced externalMonomialValue
  rw [MvPolynomial.eval₂_monomial]
  rfl

private theorem contract_eval_expansion (V : Finset Plane) (s : Plane → Status)
    (p : LocalPolynomial) (u : Fin 20 → Vec3) :
    evaluateReduced (contractSpins V s p) u =
      ∑ m ∈ p.support,
        ((p.coeff m : ℝ) * ∏ x : V,
          (rationalStatusMoment (s x.1) (fun k => m (.inl (x.1, k))) : ℝ)) *
          externalMonomialValue (externalPart m) u := by
  classical
  unfold evaluateReduced contractSpins
  rw [MvPolynomial.eval₂_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MvPolynomial.eval₂_monomial]
  simp only [map_mul, map_prod]
  change ((p.coeff m : ℝ) * ∏ x ∈ V,
      (rationalStatusMoment (s x) (fun k => m (.inl (x, k))) : ℝ)) *
        (externalPart m).prod (fun z e => u z.1 z.2 ^ e) =
    ((p.coeff m : ℝ) * ∏ x : V,
      (rationalStatusMoment (s x.1) (fun k => m (.inl (x.1, k))) : ℝ)) *
        externalMonomialValue (externalPart m) u
  have hmoment :
      (∏ x ∈ V,
        (rationalStatusMoment (s x) (fun k => m (.inl (x, k))) : ℝ)) =
        ∏ x : V,
          (rationalStatusMoment (s x.1) (fun k => m (.inl (x.1, k))) : ℝ) :=
    Finset.prod_subtype V (by intro x; rfl) _
  exact congrArg (fun z : ℝ => ((p.coeff m : ℝ) * z) *
    (externalPart m).prod (fun z e => u z.1 z.2 ^ e)) hmoment

private theorem raw_eval_expansion (V : Finset Plane) (s : Plane → Status)
    (p : LocalPolynomial) (u : Fin 20 → Vec3) :
    rawFunctional V s p u =
      ∑ m ∈ p.support,
        ∑ n : V → SpinLetter,
          (∏ x : V, spinWeight (s x.1) (n x)) *
            localEvaluation (MvPolynomial.monomial m (p.coeff m))
              (supportSpins V n) u := by
  classical
  unfold rawFunctional
  calc
    _ = ∑ n : V → SpinLetter,
          (∏ x : V, spinWeight (s x.1) (n x)) *
            (∑ m ∈ p.support,
              localEvaluation (MvPolynomial.monomial m (p.coeff m))
                (supportSpins V n) u) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [local_eval_sum]
    _ = ∑ m ∈ p.support,
          ∑ n : V → SpinLetter,
            (∏ x : V, spinWeight (s x.1) (n x)) *
              localEvaluation (MvPolynomial.monomial m (p.coeff m))
                (supportSpins V n) u := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]

end AKLT.W.H1M012

theorem AKLT.W.H1M012.main :
    AKLT.Blueprint.H1.MomentContractionStatement := by
  classical
  unfold AKLT.Blueprint.H1.MomentContractionStatement
  intro M V s hs p hadm u
  rcases hadm with ⟨hSupport, hDegree⟩
  calc
    evaluateReduced (contractSpins V s p) u =
        ∑ m ∈ p.support,
          ((p.coeff m : ℝ) * ∏ x : V,
            (rationalStatusMoment (s x.1)
              (fun k => m (.inl (x.1, k))) : ℝ)) *
            externalMonomialValue (externalPart m) u :=
      contract_eval_expansion V s p u
    _ = ∑ m ∈ p.support,
          ∑ n : V → SpinLetter,
            (∏ x : V, spinWeight (s x.1) (n x)) *
              localEvaluation (MvPolynomial.monomial m (p.coeff m))
                (supportSpins V n) u := by
      apply Finset.sum_congr rfl
      intro m hm
      calc
        ((p.coeff m : ℝ) * ∏ x : V,
            (rationalStatusMoment (s x.1)
              (fun k => m (.inl (x.1, k))) : ℝ)) *
            externalMonomialValue (externalPart m) u =
          (p.coeff m : ℝ) * externalMonomialValue (externalPart m) u *
            ∏ x : V, (rationalStatusMoment (s x.1)
              (fun k => m (.inl (x.1, k))) : ℝ) := by ring
        _ = ∑ n : V → SpinLetter,
            (∏ x : V, spinWeight (s x.1) (n x)) *
              localEvaluation (MvPolynomial.monomial m (p.coeff m))
                (supportSpins V n) u := by
          symm
          exact raw_monomial_contraction M V s hs m (p.coeff m)
            (by
              intro x hx k
              exact hSupport m hm x hx k)
            (by intro x; exact hDegree m hm x) u
    _ = rawFunctional V s p u := (raw_eval_expansion V s p u).symm

end
