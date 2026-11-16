import AKLT.W.WIN064.Geometry

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN064

abbrev ComplementPoly (D : Finset Plane) := MvPolynomial (D × Fin 3) ℝ

/-- Coordinates of retained sites; omitted sites have the zero vector. -/
def coordinatePolynomial (D : Finset Plane) (z : Plane) (i : Fin 3) : ComplementPoly D :=
  if h : z ∈ D then MvPolynomial.X (⟨z, h⟩, i) else 0

def bondPolynomial (D : Finset Plane) (e : Plane × Plane) : ComplementPoly D :=
  1 + ∑ i : Fin 3, coordinatePolynomial D e.1 i * coordinatePolynomial D e.2 i

/-- The original leg contributes a factor exactly when its tail survives. -/
def originalPinPolynomial (G D : Finset Plane) (τ : PinAssignment G)
    (e : originalLegs G) : ComplementPoly D :=
  if h : e.val.1 ∈ D then
    1 + ∑ i : Fin 3, MvPolynomial.C ((τ e).val i) * MvPolynomial.X (⟨e.val.1, h⟩, i)
  else 1

def complementPolynomial (G Y : Finset Plane) (τ : PinAssignment G) :
    ComplementPoly (G \ Y) :=
  (∏ e ∈ internalBonds (G \ Y), bondPolynomial (G \ Y) e) *
    ∏ e : originalLegs G, originalPinPolynomial G (G \ Y) τ e

private def siteDegree {ι : Type*} (m : (ι × Fin 3) →₀ ℕ) (x : ι) : ℕ :=
  ∑ i : Fin 3, m (x, i)

private def Bounded {ι : Type*} (p : MvPolynomial (ι × Fin 3) ℝ) (x : ι) (b : ℕ) : Prop :=
  ∀ m ∈ p.support, siteDegree m x ≤ b

private lemma bounded_mono {ι : Type*} {p : MvPolynomial (ι × Fin 3) ℝ} {x : ι}
    {a b : ℕ} (h : Bounded p x a) (hab : a ≤ b) : Bounded p x b :=
  fun m hm => (h m hm).trans hab

private lemma bounded_C {ι : Type*} (x : ι) (c : ℝ) :
    Bounded (MvPolynomial.C c) x 0 := by
  classical
  intro m hm
  have hm0 : m = 0 := by
    have h := MvPolynomial.support_monomial_subset hm
    simpa only [Finset.mem_singleton] using h
  simp [hm0, siteDegree]

private lemma bounded_one {ι : Type*} (x : ι) (b : ℕ) :
    Bounded (1 : MvPolynomial (ι × Fin 3) ℝ) x b :=
  bounded_mono (by simpa using bounded_C x 1) (Nat.zero_le b)

private lemma bounded_add {ι : Type*} {p q : MvPolynomial (ι × Fin 3) ℝ}
    {x : ι} {b : ℕ} (hp : Bounded p x b) (hq : Bounded q x b) : Bounded (p + q) x b := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hp m h
  · exact hq m h

private lemma bounded_mul {ι : Type*} {p q : MvPolynomial (ι × Fin 3) ℝ}
    {x : ι} {a b : ℕ} (hp : Bounded p x a) (hq : Bounded q x b) :
    Bounded (p * q) x (a + b) := by
  classical
  intro m hm
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
  rw [← huv]
  simpa [siteDegree, Finsupp.add_apply, Finset.sum_add_distrib] using
    Nat.add_le_add (hp u hu) (hq v hv)

private lemma bounded_sum {ι α : Type*} (s : Finset α) (p : α → MvPolynomial (ι × Fin 3) ℝ)
    (x : ι) (b : ℕ) (h : ∀ a ∈ s, Bounded (p a) x b) :
    Bounded (∑ a ∈ s, p a) x b := by
  classical
  intro m hm
  obtain ⟨a, ha, hm⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  exact h a ha m hm

private lemma bounded_prod {ι α : Type*} (s : Finset α) (p : α → MvPolynomial (ι × Fin 3) ℝ)
    (x : ι) (b : α → ℕ) (h : ∀ a ∈ s, Bounded (p a) x (b a)) :
    Bounded (∏ a ∈ s, p a) x (∑ a ∈ s, b a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bounded_one x 0
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact bounded_mul (h a (Finset.mem_insert_self _ _))
      (ih fun z hz => h z (Finset.mem_insert_of_mem hz))

private lemma bounded_X {ι : Type*} [DecidableEq ι] (y x : ι) (i : Fin 3) :
    Bounded (MvPolynomial.X (y, i) : MvPolynomial (ι × Fin 3) ℝ) x
      (if y = x then 1 else 0) := by
  classical
  intro m hm
  have hm' : m = Finsupp.single (y, i) 1 := by
    simpa only [MvPolynomial.support_X, Finset.mem_singleton] using hm
  subst m
  by_cases h : y = x
  · subst y
    simp [siteDegree, Finsupp.single_apply]
  · simp [siteDegree, h]

private lemma bounded_coordinate (D : Finset Plane) (z : Plane) (x : D) (i : Fin 3) :
    Bounded (coordinatePolynomial D z i) x (if z = x.val then 1 else 0) := by
  classical
  by_cases h : z ∈ D
  · rw [coordinatePolynomial, dite_eq_left h]
    simpa only [Subtype.ext_iff] using bounded_X (⟨z, h⟩ : D) x i
  · rw [coordinatePolynomial, dite_eq_right h]
    intro m hm
    simp at hm

private lemma bounded_bond (D : Finset Plane) (e : Plane × Plane) (x : D) :
    Bounded (bondPolynomial D e) x
      ((if e.1 = x.val then 1 else 0) + (if e.2 = x.val then 1 else 0)) := by
  classical
  apply bounded_add (bounded_one _ _)
  apply bounded_sum
  intro i hi
  exact bounded_mul (bounded_coordinate D e.1 x i) (bounded_coordinate D e.2 x i)

private lemma bounded_pin (G D : Finset Plane) (τ : PinAssignment G) (e : originalLegs G)
    (x : D) : Bounded (originalPinPolynomial G D τ e) x
      (if e.val.1 = x.val then 1 else 0) := by
  classical
  by_cases h : e.val.1 ∈ D
  · rw [originalPinPolynomial, dite_eq_left h]
    apply bounded_add (bounded_one _ _)
    apply bounded_sum
    intro i hi
    have hb := bounded_mul (bounded_C x ((τ e).val i)) (bounded_X (⟨e.val.1, h⟩ : D) x i)
    simpa only [Nat.zero_add, Subtype.ext_iff] using hb
  · rw [originalPinPolynomial, dite_eq_right h]
    exact bounded_one _ _

private lemma internal_endpoints (D : Finset Plane) (e : Plane × Plane)
    (he : e ∈ internalBonds D) : e.1 ∈ D ∧ e.2 ∈ D ∧ e.1 ≠ e.2 := by
  simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image] at he
  obtain ⟨x, hx, y, hy, rfl⟩ := he
  refine ⟨hx, (Finset.mem_inter.mp hy).2, ?_⟩
  have hp : y = (x.1 + 1, x.2) ∨ y = (x.1, x.2 + 1) := by
    simpa [positiveNeighbours] using (Finset.mem_inter.mp hy).1
  intro hxy
  change x = y at hxy
  subst y
  rcases hp with hp | hp
  · have := congrArg Prod.fst hp
    simp at this
  · have := congrArg Prod.snd hp
    simp at this

/-- The degree budget counts each internal bond once, and only original legs. -/
theorem complementPolynomial_degree (G Y : Finset Plane) (τ : PinAssignment G) :
    SeparateDegreeFour (complementPolynomial G Y τ) := by
  classical
  intro m hm x
  have hb := bounded_prod (internalBonds (G \ Y)) (bondPolynomial (G \ Y)) x
    (fun e => (if e.1 = x.val then 1 else 0) + (if e.2 = x.val then 1 else 0))
    (fun e _ => bounded_bond _ e x)
  have hp := bounded_prod (Finset.univ : Finset (originalLegs G))
    (originalPinPolynomial G (G \ Y) τ) x
    (fun e => if e.val.1 = x.val then 1 else 0)
    (fun e _ => bounded_pin _ _ τ e x)
  have h := bounded_mul hb hp m hm
  have hbond :
      (∑ e ∈ internalBonds (G \ Y),
        ((if e.1 = x.val then 1 else 0) + (if e.2 = x.val then 1 else 0))) =
      ((internalBonds (G \ Y)).filter fun e => e.1 = x.val ∨ e.2 = x.val).card := by
    calc
      _ = ∑ e ∈ internalBonds (G \ Y), if e.1 = x.val ∨ e.2 = x.val then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        have hne := (internal_endpoints _ e he).2.2
        by_cases h1 : e.1 = x.val <;> by_cases h2 : e.2 = x.val
        · exact (hne (h1.trans h2.symm)).elim
        all_goals simp [h1, h2]
      _ = _ := by simp
  have hpin : (∑ e : originalLegs G, if e.val.1 = x.val then 1 else 0) =
      ((originalLegs G).filter fun e => e.1 = x.val).card := by
    calc
      _ = ∑ e ∈ originalLegs G, if e.1 = x.val then 1 else 0 :=
        Finset.sum_coe_sort (originalLegs G) (fun e => if e.1 = x.val then 1 else 0)
      _ = _ := by simp
  rw [hbond, hpin] at h
  exact h.trans (incidence_bound G (G \ Y) Finset.sdiff_subset x.val x.property)

/-- Extension agrees with the partition sums' zero convention outside the sites. -/
def extendVectors {D : Finset Plane} (a : D → Vec3) (z : Plane) : Vec3 :=
  if h : z ∈ D then a ⟨z, h⟩ else 0

lemma eval_coordinatePolynomial (D : Finset Plane) (a : D → Vec3)
    (z : Plane) (i : Fin 3) :
    MvPolynomial.eval (fun v => a v.1 v.2) (coordinatePolynomial D z i) =
      extendVectors a z i := by
  classical
  by_cases h : z ∈ D <;> simp [coordinatePolynomial, extendVectors, h]

lemma eval_bondPolynomial (D : Finset Plane) (a : D → Vec3) (e : Plane × Plane) :
    MvPolynomial.eval (fun v => a v.1 v.2) (bondPolynomial D e) =
      1 + dot (extendVectors a e.1) (extendVectors a e.2) := by
  simp [bondPolynomial, dot, eval_coordinatePolynomial]

lemma eval_originalPinPolynomial (G D : Finset Plane) (τ : PinAssignment G)
    (a : D → Vec3) (e : originalLegs G) :
    MvPolynomial.eval (fun v => a v.1 v.2) (originalPinPolynomial G D τ e) =
      if e.val.1 ∈ D then 1 + dot (τ e).val (extendVectors a e.val.1) else 1 := by
  classical
  by_cases h : e.val.1 ∈ D <;> simp [originalPinPolynomial, dot, extendVectors, h]

lemma eval_complementPolynomial (G Y : Finset Plane) (τ : PinAssignment G)
    (a : ↥(G \ Y) → Vec3) :
    MvPolynomial.eval (fun v => a v.1 v.2) (complementPolynomial G Y τ) =
      (∏ e ∈ internalBonds (G \ Y),
        (1 + dot (extendVectors a e.1) (extendVectors a e.2))) *
      ∏ e : originalLegs G,
        if e.val.1 ∈ G \ Y then 1 + dot (τ e).val (extendVectors a e.val.1) else 1 := by
  classical
  simp [complementPolynomial, eval_bondPolynomial, eval_originalPinPolynomial]

#print axioms complementPolynomial_degree
#print axioms eval_coordinatePolynomial
#print axioms eval_bondPolynomial
#print axioms eval_originalPinPolynomial
#print axioms eval_complementPolynomial

end AKLT.W.WIN064
