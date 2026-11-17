module
public import AKLT.Blueprint.H1.NodesV2Pauli

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.H1

namespace AKLT.W.H1M056

private def labelOfExponent {n : ℕ} (J : Finset (Fin n))
    (m : (Fin n × Fin 3) →₀ ℕ) : J → Fin 4 := fun j =>
  if m (j.val, 0) = 1 then 1 else
  if m (j.val, 1) = 1 then 2 else
  if m (j.val, 2) = 1 then 3 else 0

private theorem label_coord {n : ℕ} (J : Finset (Fin n))
    (p : RealVectorPolynomial n) (m : (Fin n × Fin 3) →₀ ℕ)
    (ha : VectorAffineReal p) (hm : m ∈ p.support) (j : J) (k : Fin 3) :
    m (j.val, k) = if (labelOfExponent J m j).val = k.val + 1 then 1 else 0 := by
  have hs : m (j.val, 0) + m (j.val, 1) + m (j.val, 2) ≤ 1 := by
    have h := ha m hm j.val
    simp [Fin.sum_univ_succ] at h
    omega
  fin_cases k
  all_goals
    by_cases h0 : m (j.val, 0) = 1
    all_goals
      by_cases h1 : m (j.val, 1) = 1
      all_goals
        by_cases h2 : m (j.val, 2) = 1
        all_goals
          dsimp [labelOfExponent]
          simp [h0, h1, h2] <;> omega

private theorem exponent_labelOf {n : ℕ} (J : Finset (Fin n))
    (p : RealVectorPolynomial n) (m : (Fin n × Fin 3) →₀ ℕ)
    (ha : VectorAffineReal p) (hs : SupportedVectorsReal J p)
    (hm : m ∈ p.support) :
    pauliExponentReal J (labelOfExponent J m) = m := by
  classical
  ext v
  by_cases hv : v.1 ∈ J
  · simp [pauliExponentReal, hv, label_coord J p m ha hm ⟨v.1, hv⟩ v.2]
  · have hzero := hs m hm v.1 hv v.2
    simp [pauliExponentReal, hv, hzero]

private theorem label_exponent {n : ℕ} (J : Finset (Fin n)) (a : J → Fin 4) :
    labelOfExponent J (pauliExponentReal J a) = a := by
  classical
  funext j
  generalize hj : a j = x
  fin_cases x
  all_goals
    apply Fin.ext
    simp [labelOfExponent, pauliExponentReal, hj]

private theorem exponent_eval {n : ℕ} (J : Finset (Fin n)) (a : J → Fin 4)
    (u : Fin n → Vec3) :
    MvPolynomial.eval (fun v : Fin n × Fin 3 => u v.1 v.2)
      (MvPolynomial.monomial (pauliExponentReal J a) (1 : ℝ)) =
      ∏ j : J, pauliCoordinate (u j.val) (a j) := by
  classical
  rw [MvPolynomial.eval_monomial]
  simp only [one_mul, Finsupp.prod_pow]
  rw [Fintype.prod_prod_type]
  let f : Fin n → ℝ := fun i => ∏ k : Fin 3,
    u i k ^ pauliExponentReal J a (i, k)
  have hfactor (i : Fin n) : f i = if hi : i ∈ J then
      pauliCoordinate (u i) (a ⟨i, hi⟩) else 1 := by
    by_cases hi : i ∈ J
    ·
      generalize hb : a ⟨i, hi⟩ = b
      fin_cases b
      all_goals
        simp [f, pauliExponentReal, hi, hb, pauliCoordinate, Fin.prod_univ_three]
    · simp [f, pauliExponentReal, hi]
  change (∏ i : Fin n, f i) = ∏ j : J, pauliCoordinate (u j.val) (a j)
  calc
    (∏ i : Fin n, f i) = ∏ i ∈ (Finset.univ : Finset (Fin n)), f i := by simp
    _ = ∏ i ∈ J, f i := (Finset.prod_subset (s₁ := J) (s₂ := Finset.univ) (by simp)
      (fun i hi hnot => by simp [hfactor, hnot])).symm
    _ = ∏ j : J, pauliCoordinate (u j.val) (a j) := by
      rw [← Finset.prod_coe_sort]
      apply Finset.prod_congr rfl
      intro j hj
      simp [hfactor]

theorem main : AKLT.Blueprint.H1.PauliExpansionStatementV2 := by
  intro n J p ha hs u
  classical
  let term (a : J → Fin 4) : ℝ :=
    p.coeff (pauliExponentReal J a) * ∏ j : J, pauliCoordinate (u j.val) (a j)
  let good : Finset (J → Fin 4) :=
    Finset.univ.filter fun a => p.coeff (pauliExponentReal J a) ≠ 0
  have hEval : evaluateRealPolynomial p u =
      ∑ m ∈ p.support, p.coeff m *
        ∏ j : J, pauliCoordinate (u j.val) (labelOfExponent J m j) := by
    rw [evaluateRealPolynomial, MvPolynomial.eval_eq]
    refine Finset.sum_congr rfl ?_
    intro m hm
    have he := exponent_eval J (labelOfExponent J m) u
    have hmon := exponent_labelOf J p m ha hs hm
    have hp : (∏ i ∈ m.support, u i.1 i.2 ^ m i) =
        ∏ j : J, pauliCoordinate (u j.val) (labelOfExponent J m j) := by
      simpa [MvPolynomial.eval_monomial, Finsupp.prod, hmon] using he
    rw [hp]
  have hFilter : (∑ a : J → Fin 4, term a) = ∑ a ∈ good, term a := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a ha hnot
    have hzero : p.coeff (pauliExponentReal J a) = 0 := by
      by_contra hn
      apply hnot
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
    simp [term, hzero]
  have hReindex :
      (∑ m ∈ p.support, p.coeff m *
        ∏ j : J, pauliCoordinate (u j.val) (labelOfExponent J m j)) =
      ∑ a ∈ good, term a := by
    apply Finset.sum_bij (fun m _ => labelOfExponent J m)
    · intro m hm
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [exponent_labelOf J p m ha hs hm] using
        (MvPolynomial.mem_support_iff.mp hm)
    · intro m₁ hm₁ m₂ hm₂ heq
      calc
        m₁ = pauliExponentReal J (labelOfExponent J m₁) :=
          (exponent_labelOf J p m₁ ha hs hm₁).symm
        _ = pauliExponentReal J (labelOfExponent J m₂) := by rw [heq]
        _ = m₂ := exponent_labelOf J p m₂ ha hs hm₂
    · intro a haGood
      have haSupport : pauliExponentReal J a ∈ p.support := by
        rw [MvPolynomial.mem_support_iff]
        exact (Finset.mem_filter.mp haGood).2
      exact ⟨pauliExponentReal J a, haSupport, label_exponent J a⟩
    · intro m hm
      simp [term, exponent_labelOf J p m ha hs hm]
  change evaluateRealPolynomial p u = ∑ a : J → Fin 4, term a
  calc
    evaluateRealPolynomial p u =
        ∑ m ∈ p.support, p.coeff m *
          ∏ j : J, pauliCoordinate (u j.val) (labelOfExponent J m j) := hEval
    _ = ∑ a ∈ good, term a := hReindex
    _ = ∑ a : J → Fin 4, term a := hFilter.symm

end AKLT.W.H1M056
