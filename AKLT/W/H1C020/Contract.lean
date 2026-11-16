import AKLT.W.H1C020.Fubini

/-!
Generic facts about the finite moment contraction `contractSpins`: variable
support, linearity, contraction of a spin monomial times a vector polynomial,
enlargement of the contracted set by unused sites, and status congruence.
-/

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1

/-- Variables allowed in a polynomial whose internal spins lie in `A`. -/
def Allowed (A : Finset Plane) : LocalVariable → Prop
  | .inl w => w.1 ∈ A
  | .inr _ => True

/-- Every internal spin variable of `p` lies at a site of `A`. -/
def VarsIn (A : Finset Plane) (p : MvPolynomial LocalVariable ℚ) : Prop :=
  ∀ w ∈ p.vars, Allowed A w

lemma VarsIn.supported {A : Finset Plane} {p : MvPolynomial LocalVariable ℚ}
    (h : VarsIn A p) : InternallySupported A p := by
  intro m hm x hx k
  by_contra hne
  have hv : (Sum.inl (x,k) : LocalVariable) ∈ p.vars :=
    (MvPolynomial.mem_vars_iff_mem_support _).mpr ⟨m, hm, Finsupp.mem_support_iff.mpr hne⟩
  exact hx (h _ hv)

lemma VarsIn.mono {A B : Finset Plane} {p : MvPolynomial LocalVariable ℚ}
    (hAB : A ⊆ B) (h : VarsIn A p) : VarsIn B p := by
  intro w hw
  have := h w hw
  cases w with
  | inl w => exact hAB this
  | inr _ => trivial

lemma varsIn_C (A : Finset Plane) (a : ℚ) : VarsIn A (MvPolynomial.C a) := by
  intro w hw
  simp [MvPolynomial.vars_C] at hw

lemma varsIn_one (A : Finset Plane) : VarsIn A (1 : MvPolynomial LocalVariable ℚ) := by
  simpa using varsIn_C A 1

lemma varsIn_zero (A : Finset Plane) : VarsIn A (0 : MvPolynomial LocalVariable ℚ) := by
  simpa using varsIn_C A 0

lemma varsIn_X_inl {A : Finset Plane} {x : Plane} (hx : x ∈ A) (k : Fin 3) :
    VarsIn A (MvPolynomial.X (.inl (x,k))) := by
  intro w hw
  rw [MvPolynomial.vars_X, Finset.mem_singleton] at hw
  subst hw
  exact hx

lemma varsIn_X_inr (A : Finset Plane) (j : Fin 20 × Fin 3) :
    VarsIn A (MvPolynomial.X (.inr j)) := by
  intro w hw
  rw [MvPolynomial.vars_X, Finset.mem_singleton] at hw
  subst hw
  trivial

lemma VarsIn.add {A : Finset Plane} {p q : MvPolynomial LocalVariable ℚ}
    (hp : VarsIn A p) (hq : VarsIn A q) : VarsIn A (p+q) := by
  intro w hw
  rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset p q hw) with h | h
  · exact hp w h
  · exact hq w h

lemma VarsIn.mul {A : Finset Plane} {p q : MvPolynomial LocalVariable ℚ}
    (hp : VarsIn A p) (hq : VarsIn A q) : VarsIn A (p*q) := by
  intro w hw
  rcases Finset.mem_union.mp (MvPolynomial.vars_mul p q hw) with h | h
  · exact hp w h
  · exact hq w h

lemma varsIn_listSum {A : Finset Plane} (l : List (MvPolynomial LocalVariable ℚ))
    (h : ∀ p ∈ l, VarsIn A p) : VarsIn A l.sum := by
  induction l with
  | nil => exact varsIn_zero A
  | cons p l ih =>
      rw [List.sum_cons]
      exact (h p (by simp)).add (ih (fun q hq => h q (by simp [hq])))

lemma varsIn_listProd {A : Finset Plane} (l : List (MvPolynomial LocalVariable ℚ))
    (h : ∀ p ∈ l, VarsIn A p) : VarsIn A l.prod := by
  induction l with
  | nil => exact varsIn_one A
  | cons p l ih =>
      rw [List.prod_cons]
      exact (h p (by simp)).mul (ih (fun q hq => h q (by simp [hq])))

lemma varsIn_rename_inr (A : Finset Plane) (q : MvPolynomial (Fin 20 × Fin 3) ℚ) :
    VarsIn A (MvPolynomial.rename (Sum.inr : Fin 20 × Fin 3 → LocalVariable) q) := by
  intro w hw
  obtain ⟨j, _, rfl⟩ := MvPolynomial.mem_vars_rename _ _ hw
  trivial

lemma rationalStatusMoment_zero (s : Status) :
    rationalStatusMoment s (fun _ => 0) = 1 := by
  simp [rationalStatusMoment, rationalMoment]

lemma momentWeight_zero_of_supported (V : Finset Plane) (s : Plane → Status)
    (m : LocalVariable →₀ ℕ) (hm : ∀ x ∈ V, ∀ k : Fin 3, m (.inl (x,k)) = 0) :
    momentWeight V s m = 1 := by
  unfold momentWeight
  apply Finset.prod_eq_one
  intro x hx
  have : (fun k : Fin 3 => m (.inl (x,k))) = fun _ => 0 := funext (hm x hx)
  rw [this, rationalStatusMoment_zero]

lemma contractSpins_zero' (V : Finset Plane) (s : Plane → Status) :
    contractSpins V s 0 = 0 := by
  simp [contractSpins]

lemma contractSpins_listSum (V : Finset Plane) (s : Plane → Status)
    (l : List (MvPolynomial LocalVariable ℚ)) :
    contractSpins V s l.sum = (l.map (contractSpins V s)).sum := by
  induction l with
  | nil => exact contractSpins_zero' V s
  | cons p l ih => rw [List.sum_cons, contractSpins_add, ih, List.map_cons, List.sum_cons]

lemma comap_inr_add_mapDomain (ms : LocalVariable →₀ ℕ) (hms : ∀ j, ms (.inr j) = 0)
    (n : (Fin 20 × Fin 3) →₀ ℕ) :
    Finsupp.comapDomain Sum.inr (ms + Finsupp.mapDomain Sum.inr n)
      Sum.inr_injective.injOn = n := by
  ext j
  rw [Finsupp.comapDomain_apply, Finsupp.add_apply, hms j, zero_add]
  exact Finsupp.mapDomain_apply_of_injective Sum.inr_injective n j

lemma mapDomain_inr_inl (n : (Fin 20 × Fin 3) →₀ ℕ) (w : Plane × Fin 3) :
    Finsupp.mapDomain (Sum.inr : Fin 20 × Fin 3 → LocalVariable) n (.inl w) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨j, hj⟩
  exact Sum.inr_ne_inl hj

/-- Contraction of a pure spin monomial times an arbitrary vector polynomial. -/
lemma contractSpins_monomial_rename (V : Finset Plane) (s : Plane → Status)
    (ms : LocalVariable →₀ ℕ) (c : ℚ) (hms : ∀ j, ms (.inr j) = 0)
    (q : MvPolynomial (Fin 20 × Fin 3) ℚ) :
    contractSpins V s (MvPolynomial.monomial ms c *
        MvPolynomial.rename (Sum.inr : Fin 20 × Fin 3 → LocalVariable) q) =
      MvPolynomial.C (c * momentWeight V s ms) * q := by
  classical
  conv_lhs => rw [q.as_sum]
  conv_rhs => rw [q.as_sum]
  rw [map_sum, Finset.mul_sum, contractSpins_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [MvPolynomial.rename_monomial, MvPolynomial.monomial_mul_monomial, contractSpins_monomial,
    MvPolynomial.C_mul_monomial]
  have hw : (∏ x ∈ V, rationalStatusMoment (s x)
      (fun k => ((ms + Finsupp.mapDomain Sum.inr n : LocalVariable →₀ ℕ)) (.inl (x,k)))) =
        momentWeight V s ms := by
    unfold momentWeight
    apply Finset.prod_congr rfl
    intro x _
    congr 1
    funext k
    rw [Finsupp.add_apply, mapDomain_inr_inl, add_zero]
  have hc := comap_inr_add_mapDomain ms hms n
  rw [hw]
  congr 1
  · rw [hc]
  · ring

lemma contractSpins_rename (V : Finset Plane) (s : Plane → Status)
    (q : MvPolynomial (Fin 20 × Fin 3) ℚ) :
    contractSpins V s (MvPolynomial.rename (Sum.inr : Fin 20 × Fin 3 → LocalVariable) q) = q := by
  have h := contractSpins_monomial_rename V s 0 1 (fun _ => rfl) q
  have hw : momentWeight V s 0 = 1 :=
    momentWeight_zero_of_supported V s 0 (fun _ _ _ => rfl)
  rw [← MvPolynomial.C_apply, MvPolynomial.C_1, one_mul, hw, one_mul, MvPolynomial.C_1,
    one_mul] at h
  exact h

lemma contractSpins_C (V : Finset Plane) (s : Plane → Status) (a : ℚ) :
    contractSpins V s (MvPolynomial.C a) = MvPolynomial.C a := by
  have h := contractSpins_rename V s (MvPolynomial.C a)
  simpa [MvPolynomial.rename_C] using h

lemma contractSpins_C_mul (V : Finset Plane) (s : Plane → Status) (a : ℚ)
    (p : MvPolynomial LocalVariable ℚ) :
    contractSpins V s (MvPolynomial.C a * p) = MvPolynomial.C a * contractSpins V s p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [Finset.mul_sum, contractSpins_sum, contractSpins_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.C_mul_monomial, contractSpins_monomial, contractSpins_monomial,
    MvPolynomial.C_mul_monomial, mul_assoc]

/-- Enlarging the contracted set by sites without variables changes nothing. -/
lemma contractSpins_superset {A B : Finset Plane} (hAB : A ⊆ B) (s : Plane → Status)
    (p : MvPolynomial LocalVariable ℚ) (hp : InternallySupported A p) :
    contractSpins B s p = contractSpins A s p := by
  unfold contractSpins
  apply Finset.sum_congr rfl
  intro m hm
  congr 2
  symm
  apply Finset.prod_subset hAB
  intro x _ hxA
  have : (fun k : Fin 3 => m (.inl (x,k))) = fun _ => 0 := funext (hp m hm x hxA)
  rw [this, rationalStatusMoment_zero]

lemma contractSpins_congr_status (V : Finset Plane) {s t : Plane → Status}
    (h : ∀ x ∈ V, ∀ m, rationalStatusMoment (s x) m = rationalStatusMoment (t x) m)
    (p : MvPolynomial LocalVariable ℚ) :
    contractSpins V s p = contractSpins V t p := by
  unfold contractSpins
  apply Finset.sum_congr rfl
  intro m _
  congr 2
  apply Finset.prod_congr rfl
  intro x hx
  exact h x hx _

/-- `X` and `D` decide all moments; removed sites behave as uniform ones. -/
lemma rationalStatusMoment_dilutedFlag (s : Status) (m : Fin 3 → ℕ) :
    rationalStatusMoment s m =
      rationalStatusMoment (if decide (s = .D) = true then .D else .U) m := by
  cases s <;> simp [rationalStatusMoment]

end AKLT.W.H1C020
