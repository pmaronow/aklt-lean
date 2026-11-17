module
public import AKLT.Blueprint.H1.NodesPassage

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.H1

namespace AKLT.W.H1M013

private def coordinateMonomial (m : Fin 3 → ℕ) (v : Vec3) : ℝ :=
  ∏ k, v k ^ m k

private def reindex (V : Finset Plane) : V ≃ Fin V.card := by
  classical
  simpa using (Fintype.equivFin V)

private def sourceOf (V : Finset Plane) (e : V ≃ Fin V.card)
    (z : Fin V.card × Fin 3) : Plane × Fin 3 :=
  ((e.symm z.1).val, z.2)

private theorem sourceOf_injective (V : Finset Plane) (e : V ≃ Fin V.card) :
    Function.Injective (sourceOf V e) := by
  intro a b h
  cases a with
  | mk i k =>
    cases b with
    | mk j l =>
      have h' : ((e.symm i).val, k) = ((e.symm j).val, l) := by
        simpa [sourceOf] using h
      have hiVal : (e.symm i).val = (e.symm j).val := congrArg Prod.fst h'
      have hk : k = l := congrArg Prod.snd h'
      have hi : i = j := by
        have hs : e.symm i = e.symm j := Subtype.ext hiVal
        simpa using congrArg e hs
      subst j
      subst l
      rfl

private def internalExponent (V : Finset Plane) (e : V ≃ Fin V.card)
    (m : LocalVariable →₀ ℕ) : (Fin V.card × Fin 3) →₀ ℕ :=
  Finsupp.comapDomain (sourceOf V e)
    (m.comapDomain Sum.inl Sum.inl_injective.injOn) (sourceOf_injective V e).injOn

private def externalExponent (m : LocalVariable →₀ ℕ) : (Fin 20 × Fin 3) →₀ ℕ :=
  Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn

private def externalValue (m : LocalVariable →₀ ℕ) (u : Fin 20 → Vec3) : ℝ :=
  (externalExponent m).prod fun z d => u z.1 z.2 ^ d

private def transferredMonomial (V : Finset Plane) (e : V ≃ Fin V.card)
    (u : Fin 20 → Vec3) (m : LocalVariable →₀ ℕ) (c : ℚ) :
    MvPolynomial (Fin V.card × Fin 3) ℝ :=
  MvPolynomial.monomial (internalExponent V e m)
    ((c : ℝ) * externalValue m u)

private theorem exponent_decomp (V : Finset Plane) (e : V ≃ Fin V.card)
    (m : LocalVariable →₀ ℕ)
    (hout : ∀ x, x ∉ V → ∀ k : Fin 3, m (Sum.inl (x, k)) = 0) :
    m = Finsupp.sumElim
      (Finsupp.mapDomain (sourceOf V e) (internalExponent V e m))
      (externalExponent m) := by
  classical
  have hrange : ((m.comapDomain Sum.inl Sum.inl_injective.injOn).support :
      Set (Plane × Fin 3)) ⊆
      Set.range (sourceOf V e) := by
    intro z hz
    rcases z with ⟨x, k⟩
    by_contra hnot
    have hx : x ∉ V := by
      intro hx
      apply hnot
      refine ⟨(e ⟨x, hx⟩, k), ?_⟩
      simp [sourceOf]
    have hne : (m.comapDomain Sum.inl Sum.inl_injective.injOn) (x, k) ≠ 0 :=
      Finsupp.mem_support_iff.mp hz
    have hmne : m (Sum.inl (x, k)) ≠ 0 := by
      simpa [Finsupp.comapDomain_apply] using hne
    exact hmne (hout x hx k)
  have hInternal : Finsupp.comapDomain Sum.inl m Sum.inl_injective.injOn =
      Finsupp.mapDomain (sourceOf V e) (internalExponent V e m) := by
    symm
    exact Finsupp.mapDomain_comapDomain (sourceOf V e) (sourceOf_injective V e)
      (m.comapDomain Sum.inl Sum.inl_injective.injOn) hrange
  calc
    m = (m.comapDomain Sum.inl Sum.inl_injective.injOn).sumElim
        (m.comapDomain Sum.inr Sum.inr_injective.injOn) :=
      (Finsupp.comapDomain_sumElim_comapDomain m).symm
    _ = _ := by rw [hInternal]; rfl

private theorem local_monomial_eq_transferred (V : Finset Plane)
    (e : V ≃ Fin V.card) (m : LocalVariable →₀ ℕ) (c : ℚ)
    (hout : ∀ x, x ∉ V → ∀ k : Fin 3, m (Sum.inl (x, k)) = 0)
    (n : Plane → Vec3) (u : Fin 20 → Vec3) :
    localEvaluation (MvPolynomial.monomial m c) n u =
      MvPolynomial.eval (fun z => n (e.symm z.1).val z.2)
        (transferredMonomial V e u m c) := by
  classical
  unfold localEvaluation transferredMonomial externalValue internalExponent externalExponent
  have hprod : m.prod (fun v d =>
        (match v with
          | Sum.inl (x, k) => n x k
          | Sum.inr (j, k) => u j k) ^ d) =
      (internalExponent V e m).prod
          (fun z d => n (e.symm z.1).val z.2 ^ d) *
        (externalExponent m).prod (fun z d => u z.1 z.2 ^ d) := by
    have hsplit := exponent_decomp V e m hout
    calc
      _ = (Finsupp.sumElim
          (Finsupp.mapDomain (sourceOf V e) (internalExponent V e m))
          (externalExponent m)).prod (fun v d =>
            (match v with
              | Sum.inl (x, k) => n x k
              | Sum.inr (j, k) => u j k) ^ d) := by
        exact congrArg (fun z : LocalVariable →₀ ℕ => z.prod fun v d =>
          (match v with
            | Sum.inl (x, k) => n x k
            | Sum.inr (j, k) => u j k) ^ d) hsplit
      _ = _ := by
        rw [Finsupp.prod_sumElim,
          Finsupp.prod_mapDomain_index_inj (sourceOf_injective V e)]
        rfl
  change MvPolynomial.eval₂ (Rat.castHom ℝ)
      (fun v => match v with
        | Sum.inl (x, k) => n x k
        | Sum.inr (j, k) => u j k)
      (MvPolynomial.monomial m c) =
    MvPolynomial.eval (fun z => n (e.symm z.1).val z.2)
      (MvPolynomial.monomial (internalExponent V e m)
        ((c : ℝ) * externalValue m u))
  rw [MvPolynomial.eval₂_monomial, MvPolynomial.eval_monomial]
  rw [hprod]
  simp only [externalValue]
  change (c : ℝ) *
      ((internalExponent V e m).prod (fun z d => n (e.symm z.1).val z.2 ^ d) *
        (externalExponent m).prod (fun z d => u z.1 z.2 ^ d)) =
    ((c : ℝ) * (externalExponent m).prod (fun z d => u z.1 z.2 ^ d)) *
      (internalExponent V e m).prod (fun z d => n (e.symm z.1).val z.2 ^ d)
  ring

private def reindexedStatus (V : Finset Plane) (e : V ≃ Fin V.card)
    (s : Plane → Status) : Fin V.card → Status :=
  fun i => s (e.symm i).val

private def configOnV (V : Finset Plane) (e : V ≃ Fin V.card)
    (a : Fin V.card → SpinLetter) : V → SpinLetter :=
  fun x => a (e x)

private noncomputable def configFintype (n : ℕ) : Fintype (Fin n → SpinLetter) :=
  @Pi.instFintype (Fin n) (fun _ => SpinLetter) (Classical.decEq (Fin n))
    (Fin.fintype n) (fun _ => inferInstance)

private noncomputable def configSum (n : ℕ)
    (F : (Fin n → SpinLetter) → ℝ) : ℝ := by
  letI : Fintype (Fin n → SpinLetter) := configFintype n
  exact ∑ a, F a

set_option maxHeartbeats 500000 in
private theorem configSum_factorization (n : ℕ) (s : Fin n → Status)
    (f : Fin n → Vec3 → ℝ) :
    configSum n (fun a =>
      (∏ i, spinWeight (s i) (a i)) * ∏ i, f i (spinVector (a i))) =
      ∏ i, siteFunctional (s i) (f i) := by
  classical
  letI : DecidableEq (Fin n) := Classical.decEq (Fin n)
  letI : Fintype (Fin n → SpinLetter) := configFintype n
  unfold configSum siteFunctional
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum
    (fun i atom => spinWeight (s i) atom * f i (spinVector atom))).symm

private theorem configSum_congr (n : ℕ) (F G : (Fin n → SpinLetter) → ℝ)
    (h : ∀ a, F a = G a) : configSum n F = configSum n G := by
  unfold configSum
  letI : Fintype (Fin n → SpinLetter) := configFintype n
  exact Fintype.sum_congr F G h

private theorem configSum_scale (n : ℕ) (c : ℝ)
    (F : (Fin n → SpinLetter) → ℝ) :
    configSum n (fun a => c * F a) = c * configSum n F := by
  unfold configSum
  letI : Fintype (Fin n → SpinLetter) := configFintype n
  rw [Finset.mul_sum]

private theorem raw_reindex (V : Finset Plane) (e : V ≃ Fin V.card)
    (s : Plane → Status) (F : (V → SpinLetter) → ℝ) :
    (∑ b : V → SpinLetter,
        (∏ x : V, spinWeight (s x.val) (b x)) * F b) =
      configSum V.card (fun a =>
        (∏ i : Fin V.card, spinWeight (reindexedStatus V e s i) (a i)) *
          F (configOnV V e a)) := by
  classical
  letI : Fintype (Fin V.card → SpinLetter) := configFintype V.card
  let E : (Fin V.card → SpinLetter) ≃ (V → SpinLetter) :=
    Equiv.arrowCongr e.symm (Equiv.refl SpinLetter)
  symm
  apply Fintype.sum_equiv E
  intro a
  have hw : (∏ x : V, spinWeight (s x.val) (a (e x))) =
      ∏ i : Fin V.card, spinWeight (reindexedStatus V e s i) (a i) := by
    apply Fintype.prod_equiv e
    intro x
    simp [reindexedStatus]
  change (∏ i : Fin V.card, spinWeight (reindexedStatus V e s i) (a i)) *
      F (fun x => a (e x)) =
    (∏ x : V, spinWeight (s x.val) (a (e x))) * F (fun x => a (e x))
  rw [hw.symm]

private theorem transferredMonomial_degree (V : Finset Plane)
    (e : V ≃ Fin V.card) (p : LocalPolynomial)
    (hdeg : ∀ m ∈ p.support, ∀ x : Plane,
      (∑ k : Fin 3, m (Sum.inl (x, k))) ≤ 4)
    (m : LocalVariable →₀ ℕ) (hm : m ∈ p.support) (u : Fin 20 → Vec3) (c : ℚ) :
    SeparateDegreeFour (transferredMonomial V e u m c) := by
  classical
  intro d hd i
  simp only [transferredMonomial, MvPolynomial.support_monomial] at hd
  split at hd
  · contradiction
  · rcases Finset.mem_singleton.mp hd with rfl
    calc
      (∑ k : Fin 3, internalExponent V e m (i, k)) =
          ∑ k : Fin 3, m (Sum.inl ((e.symm i).val, k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [internalExponent, Finsupp.comapDomain_apply, sourceOf]
      _ ≤ 4 := hdeg m hm (e.symm i).val

set_option maxHeartbeats 500000 in
private theorem monomial_covariance_raw (hCov : ProductMomentCovariance)
    (V : Finset Plane) (e : V ≃ Fin V.card) (s : Plane → Status)
    (hs : ∀ x ∈ V, s x = .U ∨ s x = .D)
    (p : LocalPolynomial)
    (hdeg : ∀ m ∈ p.support, ∀ x : Plane,
      (∑ k : Fin 3, m (Sum.inl (x, k))) ≤ 4)
    (hint : ∀ m ∈ p.support, ∀ x : Plane, x ∉ V → ∀ k : Fin 3,
      m (Sum.inl (x, k)) = 0)
    (m : LocalVariable →₀ ℕ) (hm : m ∈ p.support) (c : ℚ)
    (u : Fin 20 → Vec3) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R.transpose * R = 1) :
    (∑ b : V → SpinLetter,
        (∏ x : V, spinWeight (s x.val) (b x)) *
          localEvaluation (MvPolynomial.monomial m c)
            (fun x => R.transpose.mulVec (supportSpins V b x)) u) =
      (∑ b : V → SpinLetter,
        (∏ x : V, spinWeight (s x.val) (b x)) *
          localEvaluation (MvPolynomial.monomial m c) (supportSpins V b) u) := by
  classical
  let q := transferredMonomial V e u m c
  let s' := reindexedStatus V e s
  have hs' : ∀ i, s' i = .U ∨ s' i = .D := by
    intro i
    exact hs (e.symm i).val (e.symm i).property
  have hRot : (R.transpose).transpose * R.transpose = 1 := by
    rw [Matrix.transpose_transpose]
    exact mul_eq_one_comm.mpr hR
  have hq := hCov V.card s' hs' q (transferredMonomial_degree V e p hdeg m hm u c)
      (fun _ => R.transpose) (fun _ => hRot)
  have hFinLeft :
      configSum V.card (fun a =>
        (∏ i : Fin V.card, spinWeight (s' i) (a i)) *
          MvPolynomial.eval
            (fun z => R.transpose.mulVec (spinVector (a z.1)) z.2) q) =
      configSum V.card (fun a =>
        (∏ i : Fin V.card, spinWeight (s' i) (a i)) *
          localEvaluation (MvPolynomial.monomial m c)
            (fun x => R.transpose.mulVec
              (supportSpins V (configOnV V e a) x)) u) := by
    apply configSum_congr
    intro a
    congr 1
    have hmono := (local_monomial_eq_transferred V e m c (hint m hm)
      (fun x => R.transpose.mulVec (supportSpins V (configOnV V e a) x)) u).symm
    have hargs : (fun z : Fin V.card × Fin 3 =>
        R.transpose.mulVec (spinVector (a z.1)) z.2) =
        (fun z : Fin V.card × Fin 3 => R.transpose.mulVec
          (supportSpins V (configOnV V e a) (e.symm z.1).val) z.2) := by
      funext z
      congr 1
      simp [configOnV, supportSpins]
    rw [hargs]
    exact hmono
  have hLeft : productFunctional s'
      (fun a => MvPolynomial.eval
        (fun z => (R.transpose).mulVec (a z.1) z.2) q) =
      (∑ b : V → SpinLetter,
        (∏ x : V, spinWeight (s x.val) (b x)) *
          localEvaluation (MvPolynomial.monomial m c)
            (fun x => R.transpose.mulVec (supportSpins V b x)) u) := by
    calc
      productFunctional s'
          (fun a => MvPolynomial.eval
            (fun z => R.transpose.mulVec (a z.1) z.2) q) =
        configSum V.card (fun a =>
          (∏ i : Fin V.card, spinWeight (s' i) (a i)) *
            MvPolynomial.eval
              (fun z => R.transpose.mulVec (spinVector (a z.1)) z.2) q) := by
          unfold productFunctional
          unfold configSum
          rfl
      _ = _ := hFinLeft.trans
        (raw_reindex V e s (fun b =>
          localEvaluation (MvPolynomial.monomial m c)
            (fun x => R.transpose.mulVec (supportSpins V b x)) u)).symm
  have hFinRight :
      configSum V.card (fun a =>
        (∏ i : Fin V.card, spinWeight (s' i) (a i)) *
          MvPolynomial.eval (fun z => spinVector (a z.1) z.2) q) =
      configSum V.card (fun a =>
        (∏ i : Fin V.card, spinWeight (s' i) (a i)) *
          localEvaluation (MvPolynomial.monomial m c)
            (supportSpins V (configOnV V e a)) u) := by
    apply configSum_congr
    intro a
    congr 1
    have hmono := (local_monomial_eq_transferred V e m c (hint m hm)
      (supportSpins V (configOnV V e a)) u).symm
    have hargs : (fun z : Fin V.card × Fin 3 => spinVector (a z.1) z.2) =
        (fun z : Fin V.card × Fin 3 =>
          supportSpins V (configOnV V e a) (e.symm z.1).val z.2) := by
      funext z
      simp [configOnV, supportSpins]
    rw [hargs]
    exact hmono
  have hRight : productFunctional s'
      (fun a => MvPolynomial.eval (fun z => a z.1 z.2) q) =
      (∑ b : V → SpinLetter,
        (∏ x : V, spinWeight (s x.val) (b x)) *
          localEvaluation (MvPolynomial.monomial m c) (supportSpins V b) u) := by
    calc
      productFunctional s' (fun a => MvPolynomial.eval (fun z => a z.1 z.2) q) =
        configSum V.card (fun a =>
          (∏ i : Fin V.card, spinWeight (s' i) (a i)) *
            MvPolynomial.eval (fun z => spinVector (a z.1) z.2) q) := by
          unfold productFunctional
          unfold configSum
          rfl
      _ = _ := hFinRight.trans
        (raw_reindex V e s (fun b =>
          localEvaluation (MvPolynomial.monomial m c) (supportSpins V b) u)).symm
  exact hLeft.symm.trans (hq.trans hRight)

private theorem localEvaluation_support_sum (p : LocalPolynomial)
    (n : Plane → Vec3) (u : Fin 20 → Vec3) :
    localEvaluation p n u =
      ∑ m ∈ p.support,
        localEvaluation (MvPolynomial.monomial m (p.coeff m)) n u := by
  classical
  unfold localEvaluation
  have hs := MvPolynomial.as_sum p
  calc
    MvPolynomial.eval₂ (Rat.castHom ℝ)
        (fun v => match v with
          | Sum.inl (x, k) => n x k
          | Sum.inr (j, k) => u j k) p =
      MvPolynomial.eval₂ (Rat.castHom ℝ)
        (fun v => match v with
          | Sum.inl (x, k) => n x k
          | Sum.inr (j, k) => u j k)
        (∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m)) :=
          congrArg (fun q => MvPolynomial.eval₂ (Rat.castHom ℝ)
            (fun v => match v with
              | Sum.inl (x, k) => n x k
              | Sum.inr (j, k) => u j k) q) hs
    _ = _ := by
      rw [MvPolynomial.eval₂_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rfl

private theorem weighted_expand_monomials (V : Finset Plane) (s : Plane → Status)
    (p : LocalPolynomial) (N : (V → SpinLetter) → Plane → Vec3) (u : Fin 20 → Vec3) :
    (∑ b : V → SpinLetter,
        (∏ x : V, spinWeight (s x.val) (b x)) * localEvaluation p (N b) u) =
      ∑ m ∈ p.support,
        ∑ b : V → SpinLetter,
          (∏ x : V, spinWeight (s x.val) (b x)) *
            localEvaluation (MvPolynomial.monomial m (p.coeff m))
              (N b) u := by
  classical
  calc
    _ = ∑ b : V → SpinLetter,
        (∏ x : V, spinWeight (s x.val) (b x)) *
          (∑ m ∈ p.support,
            localEvaluation (MvPolynomial.monomial m (p.coeff m)) (N b) u) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [localEvaluation_support_sum]
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]

private theorem raw_expand_monomials (V : Finset Plane) (s : Plane → Status)
    (p : LocalPolynomial) (u : Fin 20 → Vec3) :
    rawFunctional V s p u =
      ∑ m ∈ p.support,
        ∑ b : V → SpinLetter,
          (∏ x : V, spinWeight (s x.val) (b x)) *
            localEvaluation (MvPolynomial.monomial m (p.coeff m))
              (supportSpins V b) u := by
  unfold rawFunctional
  exact weighted_expand_monomials V s p (supportSpins V) u

set_option maxHeartbeats 500000 in
private theorem raw_monomial_factor (hMom : MonomialMoments)
    (V : Finset Plane) (s : Plane → Status)
    (hs : ∀ x ∈ V, s x = .U ∨ s x = .D)
    (p : LocalPolynomial)
    (hint : ∀ m ∈ p.support, ∀ x : Plane, x ∉ V → ∀ k : Fin 3,
      m (Sum.inl (x, k)) = 0)
    (hdeg : ∀ m ∈ p.support, ∀ x : Plane,
      (∑ k : Fin 3, m (Sum.inl (x, k))) ≤ 4)
    (m : LocalVariable →₀ ℕ) (hm : m ∈ p.support) (c : ℚ)
    (u : Fin 20 → Vec3) :
    (∑ b : V → SpinLetter,
        (∏ x : V, spinWeight (s x.val) (b x)) *
          localEvaluation (MvPolynomial.monomial m c) (supportSpins V b) u) =
      (c : ℝ) * externalValue m u *
        ∏ x : V,
          (rationalStatusMoment (s x.val) (fun k => m (Sum.inl (x.val, k))) : ℝ) := by
  classical
  let e := reindex V
  let s' := reindexedStatus V e s
  let q := transferredMonomial V e u m c
  have hs' : ∀ i, s' i = .U ∨ s' i = .D := by
    intro i
    exact hs (e.symm i).val (e.symm i).property
  have hFinite : configSum V.card (fun a =>
      (∏ i : Fin V.card, spinWeight (s' i) (a i)) *
        localEvaluation (MvPolynomial.monomial m c)
          (supportSpins V (configOnV V e a)) u) =
      productFunctional s' (fun a => MvPolynomial.eval (fun z => a z.1 z.2) q) := by
    calc
      configSum V.card (fun a =>
          (∏ i : Fin V.card, spinWeight (s' i) (a i)) *
            localEvaluation (MvPolynomial.monomial m c)
              (supportSpins V (configOnV V e a)) u) =
        configSum V.card (fun a =>
          (∏ i : Fin V.card, spinWeight (s' i) (a i)) *
            MvPolynomial.eval (fun z => spinVector (a z.1) z.2) q) := by
          apply configSum_congr
          intro a
          congr 1
          have hmono := local_monomial_eq_transferred V e m c (hint m hm)
            (supportSpins V (configOnV V e a)) u
          have hargs : (fun z : Fin V.card × Fin 3 =>
                spinVector (a z.1) z.2) =
              (fun z : Fin V.card × Fin 3 =>
                supportSpins V (configOnV V e a) (e.symm z.1).val z.2) := by
            funext z
            simp [configOnV, supportSpins]
          rw [hargs]
          exact hmono
      _ = productFunctional s' (fun a => MvPolynomial.eval (fun z => a z.1 z.2) q) := by
          unfold configSum productFunctional
          rfl
  have hEval (a : Fin V.card → Vec3) :
      MvPolynomial.eval (fun z => a z.1 z.2) q =
        ((c : ℝ) * externalValue m u) *
          ∏ i : Fin V.card,
            coordinateMonomial
              (fun k => m (Sum.inl ((e.symm i).val, k))) (a i) := by
    unfold q transferredMonomial
    rw [MvPolynomial.eval_monomial]
    have hp : (internalExponent V e m).prod
        (fun z d => a z.1 z.2 ^ d) =
        ∏ z : Fin V.card × Fin 3,
          a z.1 z.2 ^ internalExponent V e m z :=
      Finsupp.prod_fintype (internalExponent V e m)
        (fun z d => a z.1 z.2 ^ d) (by intro z; simp)
    rw [hp, Fintype.prod_prod_type]
    simp [internalExponent, sourceOf, Finsupp.comapDomain_apply,
      externalValue, coordinateMonomial, mul_assoc]
  have hScaleConfig : configSum V.card (fun a =>
      (∏ i : Fin V.card, spinWeight (s' i) (a i)) *
        MvPolynomial.eval (fun z => spinVector (a z.1) z.2) q) =
      ((c : ℝ) * externalValue m u) *
        configSum V.card (fun a =>
          (∏ i : Fin V.card, spinWeight (s' i) (a i)) *
            ∏ i : Fin V.card,
              coordinateMonomial
                (fun k => m (Sum.inl ((e.symm i).val, k))) (spinVector (a i))) := by
    calc
      _ = configSum V.card (fun a =>
          ((c : ℝ) * externalValue m u) *
            ((∏ i : Fin V.card, spinWeight (s' i) (a i)) *
              ∏ i : Fin V.card,
                coordinateMonomial
                  (fun k => m (Sum.inl ((e.symm i).val, k))) (spinVector (a i)))) := by
            apply configSum_congr
            intro a
            have he := hEval (fun i => spinVector (a i))
            rw [he]
            ring
      _ = _ := configSum_scale V.card ((c : ℝ) * externalValue m u) _
  have hFinMoment : configSum V.card (fun a =>
      (∏ i : Fin V.card, spinWeight (s' i) (a i)) *
        ∏ i : Fin V.card, coordinateMonomial
          (fun k => m (Sum.inl ((e.symm i).val, k))) (spinVector (a i))) =
      ∏ i : Fin V.card,
        (rationalStatusMoment (s' i)
          (fun k => m (Sum.inl ((e.symm i).val, k))) : ℝ) := by
    rw [configSum_factorization V.card s'
      (fun i => coordinateMonomial
        (fun k => m (Sum.inl ((e.symm i).val, k))))]
    apply Finset.prod_congr rfl
    intro i hi
    change siteFunctional (s' i)
      (fun v => ∏ k : Fin 3, v k ^ m (Sum.inl ((e.symm i).val, k))) = _
    exact hMom (fun k => m (Sum.inl ((e.symm i).val, k)))
      (hdeg m hm (e.symm i).val) (s' i) (hs' i)
  have hConfigEval : configSum V.card (fun a =>
      (∏ i : Fin V.card, spinWeight (s' i) (a i)) *
        MvPolynomial.eval (fun z => spinVector (a z.1) z.2) q) =
      productFunctional s' (fun a => MvPolynomial.eval (fun z => a z.1 z.2) q) := by
    unfold configSum productFunctional
    rfl
  have hRaw := raw_reindex V e s
    (fun b => localEvaluation (MvPolynomial.monomial m c) (supportSpins V b) u)
  calc
    (∑ b : V → SpinLetter,
        (∏ x : V, spinWeight (s x.val) (b x)) *
          localEvaluation (MvPolynomial.monomial m c) (supportSpins V b) u) =
      configSum V.card (fun a =>
        (∏ i : Fin V.card, spinWeight (s' i) (a i)) *
          localEvaluation (MvPolynomial.monomial m c)
            (supportSpins V (configOnV V e a)) u) := hRaw
    _ = productFunctional s' (fun a => MvPolynomial.eval (fun z => a z.1 z.2) q) := hFinite
    _ = configSum V.card (fun a =>
          (∏ i : Fin V.card, spinWeight (s' i) (a i)) *
            MvPolynomial.eval (fun z => spinVector (a z.1) z.2) q) := hConfigEval.symm
    _ = ((c : ℝ) * externalValue m u) *
          configSum V.card (fun a =>
            (∏ i : Fin V.card, spinWeight (s' i) (a i)) *
              ∏ i : Fin V.card,
                coordinateMonomial
                  (fun k => m (Sum.inl ((e.symm i).val, k))) (spinVector (a i))) := hScaleConfig
    _ = ((c : ℝ) * externalValue m u) *
          ∏ i : Fin V.card,
            (rationalStatusMoment (s' i)
              (fun k => m (Sum.inl ((e.symm i).val, k))) : ℝ) := by
        rw [hFinMoment]
    _ = (c : ℝ) * externalValue m u *
          ∏ x : V,
            (rationalStatusMoment (s x.val)
              (fun k => m (Sum.inl (x.val, k))) : ℝ) := by
        have hprod :
            (∏ i : Fin V.card,
              (rationalStatusMoment (s' i)
                (fun k => m (Sum.inl ((e.symm i).val, k))) : ℝ)) =
              ∏ x : V,
                (rationalStatusMoment (s x.val)
                  (fun k => m (Sum.inl (x.val, k))) : ℝ) := by
          symm
          apply Fintype.prod_equiv e
          intro x
          simp [s', reindexedStatus]
        rw [hprod]

private theorem contract_eval_expansion (V : Finset Plane) (s : Plane → Status)
    (p : LocalPolynomial) (u : Fin 20 → Vec3) :
    evaluateReduced (contractSpins V s p) u =
      ∑ m ∈ p.support,
        ((p.coeff m * ∏ x ∈ V,
          rationalStatusMoment (s x) (fun k => m (Sum.inl (x, k))) : ℚ) : ℝ) *
          externalValue m u := by
  classical
  unfold evaluateReduced contractSpins
  rw [MvPolynomial.eval₂_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MvPolynomial.eval₂_monomial]
  change (Rat.castHom ℝ)
      (p.coeff m * ∏ x ∈ V,
        rationalStatusMoment (s x) (fun k => m (Sum.inl (x, k)))) *
      (externalExponent m).prod (fun z d => u z.1 z.2 ^ d) =
    ((p.coeff m * ∏ x ∈ V,
        rationalStatusMoment (s x) (fun k => m (Sum.inl (x, k))) : ℚ) : ℝ) *
      externalValue m u
  unfold externalValue externalExponent
  rfl

private theorem contract_eval_eq_raw (hMom : MonomialMoments)
    (V : Finset Plane) (s : Plane → Status)
    (hs : ∀ x ∈ V, s x = .U ∨ s x = .D)
    (p : LocalPolynomial)
    (hint : ∀ m ∈ p.support, ∀ x : Plane, x ∉ V → ∀ k : Fin 3,
      m (Sum.inl (x, k)) = 0)
    (hdeg : ∀ m ∈ p.support, ∀ x : Plane,
      (∑ k : Fin 3, m (Sum.inl (x, k))) ≤ 4)
    (u : Fin 20 → Vec3) :
    evaluateReduced (contractSpins V s p) u = rawFunctional V s p u := by
  classical
  have hraw : rawFunctional V s p u =
      ∑ m ∈ p.support,
        (p.coeff m : ℝ) * externalValue m u *
          ∏ x : V,
            (rationalStatusMoment (s x.val)
              (fun k => m (Sum.inl (x.val, k))) : ℝ) := by
    rw [raw_expand_monomials]
    apply Finset.sum_congr rfl
    intro m hm
    exact raw_monomial_factor hMom V s hs p hint hdeg m hm
      (p.coeff m) u
  rw [contract_eval_expansion]
  rw [hraw]
  apply Finset.sum_congr rfl
  intro m hm
  push_cast
  rw [← Finset.prod_coe_sort]
  ring_nf

set_option maxHeartbeats 500000 in
private theorem raw_covariance (hCov : ProductMomentCovariance)
    (V : Finset Plane) (s : Plane → Status)
    (hs : ∀ x ∈ V, s x = .U ∨ s x = .D)
    (p : LocalPolynomial)
    (hInt : ∀ m ∈ p.support, ∀ x : Plane, x ∉ V → ∀ k : Fin 3,
      m (Sum.inl (x, k)) = 0)
    (hdeg : ∀ m ∈ p.support, ∀ x : Plane,
      (∑ k : Fin 3, m (Sum.inl (x, k))) ≤ 4)
    (hInv : IntegrandInvariant p)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R.transpose * R = 1)
    (u : Fin 20 → Vec3) :
    rawFunctional V s p (fun j => R.mulVec (u j)) =
      rawFunctional V s p u := by
  classical
  let e := reindex V
  have hRight : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
  have hPoint (b : V → SpinLetter) :
      localEvaluation p (supportSpins V b) (fun j => R.mulVec (u j)) =
        localEvaluation p (fun x => R.transpose.mulVec (supportSpins V b x)) u := by
    have h := hInv R hR
      (fun x => R.transpose.mulVec (supportSpins V b x)) u
    have hvec : (fun x => R.mulVec (R.transpose.mulVec (supportSpins V b x))) =
        supportSpins V b := by
      funext x
      rw [Matrix.mulVec_mulVec, hRight]
      simp
    simpa only [hvec] using h
  calc
    rawFunctional V s p (fun j => R.mulVec (u j)) =
        ∑ b : V → SpinLetter,
          (∏ x : V, spinWeight (s x.val) (b x)) *
            localEvaluation p
              (fun x => R.transpose.mulVec (supportSpins V b x)) u := by
      unfold rawFunctional
      apply Finset.sum_congr rfl
      intro b hb
      rw [hPoint]
    _ = rawFunctional V s p u := by
      rw [weighted_expand_monomials V s p
        (fun b x => R.transpose.mulVec (supportSpins V b x)) u]
      rw [raw_expand_monomials V s p u]
      apply Finset.sum_congr rfl
      intro m hm
      exact (monomial_covariance_raw hCov V e s hs p hdeg hInt m hm
        (p.coeff m) u R hR)

/-- The contracted polynomial is invariant under simultaneous orthogonal
transformations of its external vector slots. -/
theorem main : AKLT.Blueprint.H1.MomentCovarianceTransferStatement := by
  intro hMom hCov V s hs p hAdmissible hInvariant
  intro R hR u
  have hInternal : ∀ m ∈ p.support, ∀ x : Plane, x ∉ V → ∀ k : Fin 3,
      m (Sum.inl (x, k)) = 0 := hAdmissible.1
  have hDegree : ∀ m ∈ p.support, ∀ x : Plane,
      (∑ k : Fin 3, m (Sum.inl (x, k))) ≤ 4 := hAdmissible.2
  calc
    evaluateReduced (contractSpins V s p) (fun j => R.mulVec (u j)) =
        rawFunctional V s p (fun j => R.mulVec (u j)) :=
      contract_eval_eq_raw hMom V s hs p hInternal hDegree _
    _ = rawFunctional V s p u :=
      raw_covariance hCov V s hs p hInternal hDegree hInvariant R hR u
    _ = evaluateReduced (contractSpins V s p) u :=
      (contract_eval_eq_raw hMom V s hs p hInternal hDegree u).symm

end AKLT.W.H1M013
