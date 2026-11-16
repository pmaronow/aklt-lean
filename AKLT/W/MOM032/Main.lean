import AKLT.Blueprint.Mom.NodesExact

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Mom

namespace AKLT.W.MOM032

abbrev Poly (n : ℕ) := MvPolynomial (Fin n × Fin 3) ℝ

def siteDegree {n : ℕ} (m : (Fin n × Fin 3) →₀ ℕ) (x : Fin n) : ℕ :=
  ∑ i : Fin 3, m (x, i)

def bondUses {n : ℕ} (e : Fin n × Fin n) (x : Fin n) : ℕ :=
  (if e.1 = x then 1 else 0) + (if e.2 = x then 1 else 0)

def pinUses {n : ℕ} (q : Fin n × Vec3) (x : Fin n) : ℕ :=
  if q.1 = x then 1 else 0

def bondFactor {n : ℕ} (e : (Fin n × Fin n) × ℝ) : Poly n :=
  1 + MvPolynomial.C e.2 * dotPolynomial e.1

def bondProduct {n : ℕ} (bonds : List ((Fin n × Fin n) × ℝ)) : Poly n :=
  (bonds.map bondFactor).prod

private lemma siteDegree_add {n : ℕ} (a b : (Fin n × Fin 3) →₀ ℕ) (x : Fin n) :
    siteDegree (a + b) x = siteDegree a x + siteDegree b x := by
  simp [siteDegree, Finsupp.add_apply, Finset.sum_add_distrib]

private lemma siteDegree_zero {n : ℕ} (x : Fin n) : siteDegree 0 x = 0 := by
  simp [siteDegree]

private lemma siteDegree_dotMonomial {n : ℕ} (e : Fin n × Fin n) (x : Fin n) (i : Fin 3) :
    siteDegree (Finsupp.single (e.1, i) 1 + Finsupp.single (e.2, i) 1) x = bondUses e x := by
  simp only [siteDegree, bondUses, Finsupp.add_apply, Finsupp.single_apply]
  rw [Finset.sum_add_distrib]
  have hsum : ∀ a : Fin n,
      (∑ j : Fin 3, if (a, i) = (x, j) then 1 else 0) = if a = x then 1 else 0 := by
    intro a
    by_cases h : a = x
    · subst x
      simp
    · simp [h]
  rw [hsum, hsum]

private lemma siteDegree_pinMonomial {n : ℕ} (q : Fin n × Vec3) (x : Fin n) (i : Fin 3) :
    siteDegree (Finsupp.single (q.1, i) 1) x = pinUses q x := by
  simp only [siteDegree, pinUses, Finsupp.single_apply]
  have hsum :
      (∑ j : Fin 3, if (q.1, i) = (x, j) then 1 else 0) = if q.1 = x then 1 else 0 := by
    by_cases h : q.1 = x
    · subst x
      simp
    · simp [h]
  exact hsum

private lemma mul_support_siteDegree {n : ℕ} (p q : Poly n) (x : Fin n) (a b : ℕ)
    (hp : ∀ m ∈ p.support, siteDegree m x ≤ a)
    (hq : ∀ m ∈ q.support, siteDegree m x ≤ b) :
    ∀ m ∈ (p * q).support, siteDegree m x ≤ a + b := by
  classical
  intro m hm
  rcases Finset.mem_add.mp (MvPolynomial.support_mul p q hm) with ⟨u, hu, v, hv, huv⟩
  rw [← huv, siteDegree_add]
  exact Nat.add_le_add (hp u hu) (hq v hv)

private lemma support_C_mul_subset {n : ℕ} (c : ℝ) (p : Poly n) :
    (MvPolynomial.C c * p).support ⊆ p.support := by
  rw [MvPolynomial.C_mul']
  exact MvPolynomial.support_smul

private lemma dot_support_form {n : ℕ} (e : Fin n × Fin n) {m : (Fin n × Fin 3) →₀ ℕ}
    (hm : m ∈ (dotPolynomial e).support) :
    ∃ i : Fin 3, m = Finsupp.single (e.1, i) 1 + Finsupp.single (e.2, i) 1 := by
  classical
  have hsum := MvPolynomial.support_sum
    (s := (Finset.univ : Finset (Fin 3)))
    (f := fun i : Fin 3 =>
      (MvPolynomial.X (e.1, i) : Poly n) * MvPolynomial.X (e.2, i))
  change m ∈ ((∑ i : Fin 3,
    (MvPolynomial.X (e.1, i) : Poly n) * MvPolynomial.X (e.2, i))).support at hm
  have hm' : m ∈ Finset.univ.biUnion (fun i : Fin 3 =>
      ((MvPolynomial.X (e.1, i) : Poly n) * MvPolynomial.X (e.2, i)).support) := hsum hm
  rcases Finset.mem_biUnion.mp hm' with ⟨i, -, hi⟩
  have hi' := MvPolynomial.support_mul
      (MvPolynomial.X (e.1, i) : Poly n) (MvPolynomial.X (e.2, i)) hi
  rcases Finset.mem_add.mp hi' with ⟨u, hu, v, hv, huv⟩
  have hu' : u = Finsupp.single (e.1, i) 1 := by
    simpa only [MvPolynomial.support_X, Finset.mem_singleton] using hu
  have hv' : v = Finsupp.single (e.2, i) 1 := by
    simpa only [MvPolynomial.support_X, Finset.mem_singleton] using hv
  exact ⟨i, huv ▸ congrArg₂ (· + ·) hu' hv'⟩

private lemma pinLinear_support_form {n : ℕ} (q : (Fin n × Vec3) × ℝ)
    {m : (Fin n × Fin 3) →₀ ℕ}
    (hm : m ∈ (∑ i : Fin 3,
      MvPolynomial.C (q.1.2 i) * (MvPolynomial.X (q.1.1, i) : Poly n)).support) :
    ∃ i : Fin 3, m = Finsupp.single (q.1.1, i) 1 := by
  classical
  have hsum := MvPolynomial.support_sum
    (s := (Finset.univ : Finset (Fin 3)))
    (f := fun i : Fin 3 => MvPolynomial.C (q.1.2 i) *
      (MvPolynomial.X (q.1.1, i) : Poly n))
  have hm' : m ∈ Finset.univ.biUnion (fun i : Fin 3 =>
      (MvPolynomial.C (q.1.2 i) *
        (MvPolynomial.X (q.1.1, i) : Poly n)).support) := hsum hm
  rcases Finset.mem_biUnion.mp hm' with ⟨i, -, hi⟩
  have hi' : m ∈ (MvPolynomial.X (q.1.1, i) : Poly n).support :=
    support_C_mul_subset (q.1.2 i) _ hi
  have hsingle : m = Finsupp.single (q.1.1, i) 1 := by
    simpa only [MvPolynomial.support_X, Finset.mem_singleton] using hi'
  exact ⟨i, hsingle⟩

private lemma bondFactor_siteDegree {n : ℕ} (e : (Fin n × Fin n) × ℝ) (x : Fin n) :
    ∀ m ∈ (bondFactor e).support,
      siteDegree m x ≤ bondUses e.1 x := by
  classical
  intro m hm
  change m ∈ (1 + MvPolynomial.C e.2 * dotPolynomial e.1).support at hm
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with hconst | hdot
  · have hm0 : m = 0 := by
      simpa only [MvPolynomial.support_one, Finset.mem_singleton] using hconst
    rw [hm0, siteDegree_zero]
    exact Nat.zero_le _
  · have hdot' : m ∈ (dotPolynomial e.1).support :=
      support_C_mul_subset e.2 _ hdot
    rcases dot_support_form e.1 hdot' with ⟨i, rfl⟩
    rw [siteDegree_dotMonomial]

private lemma pinFactor_siteDegree {n : ℕ} (q : (Fin n × Vec3) × ℝ) (x : Fin n) :
    ∀ m ∈ (pinPolynomial q).support, siteDegree m x ≤ pinUses q.1 x := by
  classical
  intro m hm
  change m ∈ (1 + MvPolynomial.C q.2 *
    (∑ i : Fin 3, MvPolynomial.C (q.1.2 i) *
      (MvPolynomial.X (q.1.1, i) : Poly n))).support at hm
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with hconst | hlin
  · have hm0 : m = 0 := by
      simpa only [MvPolynomial.support_one, Finset.mem_singleton] using hconst
    rw [hm0, siteDegree_zero]
    exact Nat.zero_le _
  · have hlin' : m ∈ (∑ i : Fin 3,
      MvPolynomial.C (q.1.2 i) *
        (MvPolynomial.X (q.1.1, i) : Poly n)).support :=
      support_C_mul_subset q.2 _ hlin
    rcases pinLinear_support_form q hlin' with ⟨i, rfl⟩
    rw [siteDegree_pinMonomial]

private lemma bondList_siteDegree {n : ℕ} (bonds : List ((Fin n × Fin n) × ℝ)) (x : Fin n) :
    ∀ m ∈ (bondProduct bonds).support,
      siteDegree m x ≤
        (bonds.filter fun e => e.1.1 = x).length +
          (bonds.filter fun e => e.1.2 = x).length := by
  classical
  induction bonds with
  | nil =>
      intro m hm
      have hm0 : m = 0 := by
        change m ∈ (1 : Poly n).support at hm
        simpa only [MvPolynomial.support_one, Finset.mem_singleton] using hm
      rw [hm0, siteDegree_zero]
      simp
  | cons e rest ih =>
      intro m hm
      change m ∈ (bondFactor e * bondProduct rest).support at hm
      have hmul := mul_support_siteDegree
        (bondFactor e) (bondProduct rest)
        x (bondUses e.1 x)
        ((rest.filter fun a => a.1.1 = x).length +
          (rest.filter fun a => a.1.2 = x).length)
        (bondFactor_siteDegree e x) ih m hm
      have hcount :
          bondUses e.1 x +
            ((rest.filter fun a => a.1.1 = x).length +
              (rest.filter fun a => a.1.2 = x).length) =
            ((e :: rest).filter fun a => a.1.1 = x).length +
              ((e :: rest).filter fun a => a.1.2 = x).length := by
        have hl : ((e :: rest).filter fun a => a.1.1 = x).length =
            (if e.1.1 = x then 1 else 0) + (rest.filter fun a => a.1.1 = x).length := by
          by_cases h : e.1.1 = x <;> simp [h] <;> omega
        have hr : ((e :: rest).filter fun a => a.1.2 = x).length =
            (if e.1.2 = x then 1 else 0) + (rest.filter fun a => a.1.2 = x).length := by
          by_cases h : e.1.2 = x <;> simp [h] <;> omega
        rw [hl, hr]
        simp [bondUses]
        omega
      omega

private lemma pinList_siteDegree {n : ℕ} (pins : List ((Fin n × Vec3) × ℝ)) (x : Fin n) :
    ∀ m ∈ (pins.map pinPolynomial).prod.support,
      siteDegree m x ≤ (pins.filter fun q => q.1.1 = x).length := by
  classical
  induction pins with
  | nil =>
      intro m hm
      have hm0 : m = 0 := by
        change m ∈ (1 : Poly n).support at hm
        simpa only [MvPolynomial.support_one, Finset.mem_singleton] using hm
      rw [hm0, siteDegree_zero]
      simp
  | cons q rest ih =>
      intro m hm
      change m ∈ (pinPolynomial q * (rest.map pinPolynomial).prod).support at hm
      have hmul := mul_support_siteDegree
        (pinPolynomial q) ((rest.map pinPolynomial).prod) x (pinUses q.1 x)
        ((rest.filter fun a => a.1.1 = x).length)
        (pinFactor_siteDegree q x) ih m hm
      have hcount :
          pinUses q.1 x + (rest.filter fun a => a.1.1 = x).length =
            ((q :: rest).filter fun a => a.1.1 = x).length := by
        by_cases h : q.1.1 = x <;> simp [pinUses, h] <;> omega
      omega

private lemma mul_support_siteDegree_reserved {n : ℕ} (p q : Poly n) (x : Fin n)
    (a b : ℕ)
    (hp : ∀ m ∈ p.support, siteDegree m x + (a + b) ≤ 4)
    (hq : ∀ m ∈ q.support, siteDegree m x ≤ a) :
    ∀ m ∈ (p * q).support, siteDegree m x + b ≤ 4 := by
  classical
  intro m hm
  rcases Finset.mem_add.mp (MvPolynomial.support_mul p q hm) with ⟨u, hu, v, hv, huv⟩
  rw [← huv, siteDegree_add]
  have hpu := hp u hu
  have hqv := hq v hv
  omega

theorem main : AKLT.Blueprint.Mom.InteractionDegreeStatement := by
  classical
  intro n bonds pins p hp
  change ∀ m ∈ (p * (bondProduct bonds) *
    (pins.map pinPolynomial).prod).support, ∀ x : Fin n, siteDegree m x ≤ 4
  intro m hm x
  let bc := (bonds.filter fun e => e.1.1 = x).length +
    (bonds.filter fun e => e.1.2 = x).length
  let pc := (pins.filter fun q => q.1.1 = x).length
  have hobs : ∀ u ∈ p.support, siteDegree u x + (bc + pc) ≤ 4 := by
    intro u hu
    have h := hp u hu x
    simpa [siteDegree, bc, pc, interactionOccurrences] using h
  have hbonds : ∀ v ∈
      (bondProduct bonds).support,
      siteDegree v x ≤ bc := by
    intro v hv
    exact (bondList_siteDegree bonds x v hv).trans_eq (by rfl)
  have hfirst : ∀ u ∈
      (p * bondProduct bonds).support,
      siteDegree u x + pc ≤ 4 := by
    intro u hu
    exact mul_support_siteDegree_reserved p
      (bondProduct bonds)
      x bc pc hobs hbonds u hu
  have hpins : ∀ v ∈ (pins.map pinPolynomial).prod.support,
      siteDegree v x ≤ pc := by
    intro v hv
    exact (pinList_siteDegree pins x v hv).trans_eq (by rfl)
  exact mul_support_siteDegree_reserved
    (p * bondProduct bonds)
    ((pins.map pinPolynomial).prod) x pc 0
    (by simpa using hfirst) hpins m hm

#print axioms main

end AKLT.W.MOM032
