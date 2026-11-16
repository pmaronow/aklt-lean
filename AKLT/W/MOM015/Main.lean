import AKLT.Blueprint.Mom.NodesFinite

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.MOM015

private def siteDegree {n : ℕ} (m : (Fin n × Fin 3) →₀ ℕ) (x : Fin n) : ℕ :=
  ∑ i : Fin 3, m (x, i)

private def endpointCost {n : ℕ} (e : Fin n × Fin n) (x : Fin n) : ℕ :=
  (if e.1 = x then 1 else 0) + (if e.2 = x then 1 else 0)

private def supportBound {n : ℕ} (x : Fin n)
    (p : MvPolynomial (Fin n × Fin 3) ℝ) (cost : ℕ) : Prop :=
  ∀ m ∈ p.support, siteDegree m x ≤ cost

private theorem siteDegree_add {n : ℕ} (m q : (Fin n × Fin 3) →₀ ℕ) (x : Fin n) :
    siteDegree (m + q) x = siteDegree m x + siteDegree q x := by
  simp [siteDegree, Finset.sum_add_distrib]

private theorem supportBound_X {n : ℕ} (x : Fin n) (z : Fin n × Fin 3) :
    supportBound x (MvPolynomial.X z : MvPolynomial (Fin n × Fin 3) ℝ)
      (if z.1 = x then 1 else 0) := by
  rcases z with ⟨zsite, k⟩
  intro m hm
  rw [MvPolynomial.support_X] at hm
  simp only [Finset.mem_singleton] at hm
  subst m
  by_cases hz : zsite = x
  · subst zsite
    simp [siteDegree, Finsupp.single_apply]
  · simp [siteDegree, hz]

private theorem supportBound_one {n : ℕ} (x : Fin n) (cost : ℕ) :
    supportBound x (1 : MvPolynomial (Fin n × Fin 3) ℝ) cost := by
  intro m hm
  rw [MvPolynomial.support_one] at hm
  simp only [Finset.mem_singleton] at hm
  subst m
  simp [siteDegree]

private theorem supportBound_add {n : ℕ} (x : Fin n)
    (p q : MvPolynomial (Fin n × Fin 3) ℝ) (cost : ℕ)
    (hp : supportBound x p cost) (hq : supportBound x q cost) :
    supportBound x (p + q) cost := by
  intro m hm
  have hm' : m ∈ p.support ∪ q.support := MvPolynomial.support_add hm
  rcases Finset.mem_union.mp hm' with hp' | hq'
  · exact hp m hp'
  · exact hq m hq'

private theorem supportBound_mul {n : ℕ} (x : Fin n)
    (p q : MvPolynomial (Fin n × Fin 3) ℝ) (a b : ℕ)
    (hp : supportBound x p a) (hq : supportBound x q b) :
    supportBound x (p * q) (a + b) := by
  intro m hm
  have hm' := MvPolynomial.support_mul p q hm
  rcases Finset.mem_add.mp hm' with ⟨u, hu, v, hv, huv⟩
  rw [← huv, siteDegree_add]
  exact Nat.add_le_add (hp u hu) (hq v hv)

private theorem supportBound_sum {n : ℕ} {α : Type} [DecidableEq (Fin n × Fin 3)]
    (x : Fin n) (s : Finset α) (f : α → MvPolynomial (Fin n × Fin 3) ℝ)
    (cost : ℕ) (hf : ∀ a ∈ s, supportBound x (f a) cost) :
    supportBound x (∑ a ∈ s, f a) cost := by
  intro m hm
  have hm' : m ∈ s.biUnion (fun a => (f a).support) :=
    MvPolynomial.support_sum (s := s) (f := f) hm
  rcases Finset.mem_biUnion.mp hm' with ⟨a, ha, ham⟩
  exact hf a ha m ham

private theorem supportBound_finset_prod {n : ℕ} {α : Type} [DecidableEq (Fin n × Fin 3)]
    (x : Fin n) (s : Finset α) (f : α → MvPolynomial (Fin n × Fin 3) ℝ)
    (cost : α → ℕ) (hf : ∀ a ∈ s, supportBound x (f a) (cost a)) :
    supportBound x (∏ a ∈ s, f a) (∑ a ∈ s, cost a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [supportBound, siteDegree]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      apply supportBound_mul
      · exact hf a (Finset.mem_insert_self a s)
      · apply ih
        intro b hb
        exact hf b (Finset.mem_insert_of_mem hb)

private theorem supportBound_list_prod {n : ℕ} (x : Fin n)
    (l : List (Fin n × Fin n)) (cost : (Fin n × Fin n) → ℕ)
    (hf : ∀ e ∈ l, supportBound x (AKLT.Blueprint.Mom.dotPolynomial e) (cost e)) :
    supportBound x ((l.map fun e => AKLT.Blueprint.Mom.dotPolynomial e).prod)
      ((l.map cost).sum) := by
  induction l with
  | nil => simp [supportBound, siteDegree]
  | cons e l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      apply supportBound_mul
      · exact hf e (by simp)
      · apply ih
        intro b hb
        exact hf b (by simp [hb])

private theorem supportBound_dot {n : ℕ} (x : Fin n) (e : Fin n × Fin n) :
    supportBound x (AKLT.Blueprint.Mom.dotPolynomial e) (endpointCost e x) := by
  classical
  unfold AKLT.Blueprint.Mom.dotPolynomial
  apply supportBound_sum x Finset.univ
  intro i hi
  exact supportBound_mul x
    (MvPolynomial.X (e.1, i)) (MvPolynomial.X (e.2, i))
    (if e.1 = x then 1 else 0) (if e.2 = x then 1 else 0)
    (supportBound_X x (e.1, i)) (supportBound_X x (e.2, i))

private theorem supportBound_factor {n : ℕ} (x : Fin n) (e : Fin n × Fin n) :
    supportBound x (1 + AKLT.Blueprint.Mom.dotPolynomial e) (endpointCost e x) := by
  apply supportBound_add x 1 (AKLT.Blueprint.Mom.dotPolynomial e) (endpointCost e x)
  · exact supportBound_one x _
  · exact supportBound_dot x e

private theorem finset_indicator_sum {α : Type} (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (∑ a ∈ s, if p a then 1 else 0) = (s.filter p).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      by_cases hp : p a <;> simp_all

private theorem bond_cost_eq_card {n : ℕ} (s : Finset (Fin n × Fin n)) (x : Fin n)
    (hne : ∀ e ∈ s, e.1 ≠ e.2) :
    (∑ e ∈ s, endpointCost e x) = (s.filter fun e => e.1 = x ∨ e.2 = x).card := by
  classical
  have hpoint : ∀ e ∈ s,
      endpointCost e x = if e.1 = x ∨ e.2 = x then 1 else 0 := by
    intro e he
    by_cases h₁ : e.1 = x <;> by_cases h₂ : e.2 = x
    · exfalso
      exact hne e he (h₁.trans h₂.symm)
    · simp [endpointCost, h₁, h₂]
    · simp [endpointCost, h₁, h₂]
    · simp [endpointCost, h₁, h₂]
  calc
    (∑ e ∈ s, endpointCost e x) =
        ∑ e ∈ s, (if e.1 = x ∨ e.2 = x then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro e he
          exact hpoint e he
    _ = (s.filter fun e => e.1 = x ∨ e.2 = x).card := finset_indicator_sum s _

private theorem list_indicator_sum {α : Type} (l : List α) (p : α → Prop)
    [DecidablePred p] :
    (l.map fun a => if p a then 1 else 0).sum = (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases hp : p a <;> simp [hp, ih, Nat.add_comm]

private theorem list_endpoint_cost_split {n : ℕ} (l : List (Fin n × Fin n)) (x : Fin n) :
    (l.map fun e => endpointCost e x).sum =
      (l.map fun e => if e.1 = x then 1 else 0).sum +
        (l.map fun e => if e.2 = x then 1 else 0).sum := by
  induction l with
  | nil => simp [endpointCost]
  | cons e l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      unfold endpointCost
      omega

private theorem list_endpoint_cost_eq {n : ℕ} (l : List (Fin n × Fin n)) (x : Fin n) :
    (l.map fun e => endpointCost e x).sum =
      (l.filter fun e => e.1 = x).length + (l.filter fun e => e.2 = x).length := by
  rw [list_endpoint_cost_split]
  rw [list_indicator_sum, list_indicator_sum]

end AKLT.W.MOM015

namespace AKLT.W.MOM015

theorem main : AKLT.Blueprint.Mom.FreeDegreeStatement := by
  intro n D hD pairs hcounts m hm x
  rcases hD with ⟨_, hlt, _⟩
  have hne : ∀ e ∈ D.bonds, e.1 ≠ e.2 := by
    intro e he
    exact ne_of_lt (hlt e he)
  have hb : (∑ e ∈ D.bonds, endpointCost e x) =
      (D.bonds.filter fun e => e.1 = x ∨ e.2 = x).card :=
    bond_cost_eq_card D.bonds x hne
  have hp : (pairs.map fun e => endpointCost e x).sum =
      (pairs.filter fun e => e.1 = x).length + (pairs.filter fun e => e.2 = x).length :=
    list_endpoint_cost_eq pairs x
  have hcost : (∑ e ∈ D.bonds, endpointCost e x) +
      (pairs.map fun e => endpointCost e x).sum ≤ 4 := by
    have hx := hcounts x
    rw [hb, hp]
    omega
  have hB : supportBound x
      (∏ e ∈ D.bonds, (1 + AKLT.Blueprint.Mom.dotPolynomial e))
      (∑ e ∈ D.bonds, endpointCost e x) := by
    apply supportBound_finset_prod
    intro e he
    exact supportBound_factor x e
  have hP : supportBound x
      ((pairs.map AKLT.Blueprint.Mom.dotPolynomial).prod)
      ((pairs.map fun e => endpointCost e x).sum) := by
    apply supportBound_list_prod
    intro e he
    exact supportBound_dot x e
  have hF : supportBound x (AKLT.Blueprint.Mom.freePolynomial D pairs)
      ((∑ e ∈ D.bonds, endpointCost e x) +
        (pairs.map fun e => endpointCost e x).sum) := by
    simpa [AKLT.Blueprint.Mom.freePolynomial] using
      supportBound_mul x
        (∏ e ∈ D.bonds, (1 + AKLT.Blueprint.Mom.dotPolynomial e))
        ((pairs.map AKLT.Blueprint.Mom.dotPolynomial).prod)
        _ _ hB hP
  exact Nat.le_trans (hF m hm) hcost

end AKLT.W.MOM015
