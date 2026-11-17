module
public import AKLT.Blueprint.H1.NodesPassage

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators Pointwise
open AKLT.Defs
open AKLT.Blueprint.H1

namespace AKLT.W.H1M009

private def siteExponent (m : LocalVariable →₀ ℕ) (x : Plane) : ℕ :=
  ∑ k : Fin 3, m (.inl (x, k))

private structure SiteBound (p : LocalPolynomial) (x : Plane) (d : ℕ) : Prop where
  holds : ∀ m ∈ p.support, siteExponent m x ≤ d

private theorem siteExponent_add (a b : LocalVariable →₀ ℕ) (x : Plane) :
    siteExponent (a + b) x = siteExponent a x + siteExponent b x := by
  simp [siteExponent, Finsupp.add_apply, Finset.sum_add_distrib]

private theorem siteBound_mul {p q : LocalPolynomial} {x : Plane} {a b : ℕ}
    (hp : SiteBound p x a) (hq : SiteBound q x b) : SiteBound (p * q) x (a + b) := by
  classical
  refine ⟨?_⟩
  intro m hm
  have hm' : m ∈ p.support + q.support := MvPolynomial.support_mul p q hm
  change m ∈ Finset.image₂ (fun u v : LocalVariable →₀ ℕ => u + v) p.support q.support at hm'
  rcases Finset.mem_image₂.mp hm' with ⟨u, hu, v, hv, huv⟩
  rw [← huv, siteExponent_add]
  exact Nat.add_le_add (hp.holds u hu) (hq.holds v hv)

private theorem siteBound_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p : ι → LocalPolynomial) (x : Plane) (d : ι → ℕ)
    (h : ∀ i ∈ s, SiteBound (p i) x (d i)) :
    SiteBound (∏ i ∈ s, p i) x (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      constructor
      intro m hm
      have hm0 : m = 0 := by simpa using hm
      simp [siteExponent, hm0]
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi, Finset.sum_insert hi]
      apply siteBound_mul
      · exact h i (Finset.mem_insert_self ..)
      · exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj))

private theorem siteBound_add {p q : LocalPolynomial} {x : Plane} {d : ℕ}
    (hp : SiteBound p x d) (hq : SiteBound q x d) : SiteBound (p + q) x d := by
  refine ⟨?_⟩
  intro m hm
  have hm' : m ∈ p.support ∪ q.support := MvPolynomial.support_add hm
  rcases Finset.mem_union.mp hm' with h | h
  · exact hp.holds m h
  · exact hq.holds m h

private theorem siteBound_sum {ι : Type*} (s : Finset ι)
    (p : ι → LocalPolynomial) (x : Plane) (d : ℕ)
    (h : ∀ i ∈ s, SiteBound (p i) x d) : SiteBound (∑ i ∈ s, p i) x d := by
  classical
  constructor
  intro m hm
  rcases Finset.mem_biUnion.mp (MvPolynomial.support_sum hm) with ⟨i, hi, hmi⟩
  exact (h i hi).holds m hmi

private theorem siteBound_X_internal (x z : Plane) (k : Fin 3) :
    SiteBound (MvPolynomial.X (.inl (x, k) : LocalVariable)) z
      (if x = z then 1 else 0) := by
  classical
  constructor
  intro m hm
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst m
  by_cases hx : x = z
  · subst x
    simp [siteExponent, Finsupp.single_apply]
  · simp [siteExponent, hx, Ne.symm hx]

private theorem siteBound_X_external (j : Fin 20) (k : Fin 3) (z : Plane) :
    SiteBound (MvPolynomial.X (.inr (j, k) : LocalVariable)) z 0 := by
  classical
  constructor
  intro m hm
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst m
  simp [siteExponent]

private theorem siteBound_one (x : Plane) : SiteBound (1 : LocalPolynomial) x 0 := by
  constructor
  intro m hm
  have hm0 : m = 0 := by simpa using hm
  simp [siteExponent, hm0]

private theorem siteBound_mono {p : LocalPolynomial} {x : Plane} {a b : ℕ}
    (h : SiteBound p x a) (hab : a ≤ b) : SiteBound p x b := by
  refine ⟨?_⟩
  intro m hm
  exact (h.holds m hm).trans hab

/-- The contribution to one site's internal degree from one bond factor. -/
private def bondIncidence (x : Plane) (e : Plane × Plane) : ℕ :=
  (if x = e.1 then 1 else 0) + (if x = e.2 then 1 else 0)

/-- The contribution to one site's internal degree from one retained slot factor. -/
private def slotIncidence (π : PatternData) (x : Plane) (j : Fin 20) : ℕ :=
  if π.statusAt (externalSlot j).1 ≠ .X ∧ (externalSlot j).1 = x then 1 else 0

private def bondIncidenceCount (π : PatternData) (x : Plane) : ℕ :=
  ∑ e ∈ π.bonds, bondIncidence x e

private def slotIncidenceCount (π : PatternData) (x : Plane) : ℕ :=
  ∑ j : Fin 20, slotIncidence π x j

/--
Degree bounds for a single formal dot product. The first clause counts
both internal endpoints; the second counts its one internal endpoint.
-/
private def FormalDotSupport : Prop :=
  (∀ x y z : Plane, ∀ m ∈
    (formalDot (fun k => (Sum.inl (x, k) : LocalVariable))
      (fun k => (Sum.inl (y, k) : LocalVariable))).support,
      siteExponent m z ≤ bondIncidence z (x, y)) ∧
  (∀ x z : Plane, ∀ j : Fin 20, ∀ m ∈
    (formalDot (fun k => (Sum.inl (x, k) : LocalVariable))
      (fun k => (Sum.inr (j, k) : LocalVariable))).support,
      siteExponent m z ≤ if x = z then 1 else 0)

/--
Incident bond slots plus retained external slots
fit the degree-four budget at active sites and vanish outside the active set.
-/
private def LocalCounts : Prop :=
  ∀ π : PatternData, ∀ x : Plane,
    bondIncidenceCount π x + slotIncidenceCount π x ≤
      if x ∈ π.active then 4 else 0

private theorem formalDotSupport : FormalDotSupport := by
  constructor
  · intro x y z
    have h : SiteBound
        (formalDot (fun k => (Sum.inl (x, k) : LocalVariable))
          (fun k => (Sum.inl (y, k) : LocalVariable))) z
        (bondIncidence z (x, y)) := by
      unfold formalDot
      apply siteBound_sum
      intro k _
      simpa [bondIncidence, eq_comm] using
        siteBound_mul (siteBound_X_internal x z k) (siteBound_X_internal y z k)
    exact h.holds
  · intro x z j
    have h : SiteBound
        (formalDot (fun k => (Sum.inl (x, k) : LocalVariable))
          (fun k => (Sum.inr (j, k) : LocalVariable))) z
        (if x = z then 1 else 0) := by
      unfold formalDot
      apply siteBound_sum
      intro k _
      simpa using siteBound_mul (siteBound_X_internal x z k) (siteBound_X_external j k z)
    exact h.holds

private theorem template_factor_count : ∀ x ∈ templateSites,
    (∑ e ∈ internalBonds templateSites, bondIncidence x e) +
      (∑ j : Fin 20, if (externalSlot j).1 = x then 1 else 0) ≤ 4 := by
  decide +kernel

private theorem externalSlot_mem_template : ∀ j : Fin 20,
    (externalSlot j).1 ∈ templateSites := by
  decide +kernel

private theorem internalBonds_endpoints {e : Plane × Plane}
    (he : e ∈ internalBonds templateSites) :
    e.1 ∈ templateSites ∧ e.2 ∈ templateSites := by
  rcases Finset.mem_biUnion.mp he with ⟨x, hx, he⟩
  rcases Finset.mem_image.mp he with ⟨y, hy, rfl⟩
  exact ⟨hx, (Finset.mem_inter.mp hy).2⟩

private theorem bonds_endpoints_active (π : PatternData) {e : Plane × Plane}
    (he : e ∈ π.bonds) : e.1 ∈ π.active ∧ e.2 ∈ π.active := by
  have h := Finset.mem_filter.mp he
  have ht := internalBonds_endpoints h.1
  exact ⟨Finset.mem_filter.mpr ⟨ht.1, h.2.1⟩,
    Finset.mem_filter.mpr ⟨ht.2, h.2.2.1⟩⟩

private theorem localCounts : LocalCounts := by
  classical
  intro π x
  by_cases hx : x ∈ π.active
  · simp only [hx, ite_true]
    have hb : bondIncidenceCount π x ≤
        ∑ e ∈ internalBonds templateSites, bondIncidence x e := by
      apply Finset.sum_le_sum_of_subset
      exact Finset.filter_subset _ _
    have hs : slotIncidenceCount π x ≤
        ∑ j : Fin 20, if (externalSlot j).1 = x then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : (externalSlot j).1 = x
      · simp [slotIncidence, hj, (Finset.mem_filter.mp hx).2]
      · simp [slotIncidence, hj]
    exact (Nat.add_le_add hb hs).trans
      (template_factor_count x (Finset.mem_filter.mp hx).1)
  · simp only [hx, ite_false]
    have hb : bondIncidenceCount π x = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      have ha := bonds_endpoints_active π he
      have h₁ : x ≠ e.1 := fun h => hx (h ▸ ha.1)
      have h₂ : x ≠ e.2 := fun h => hx (h ▸ ha.2)
      simp [bondIncidence, h₁, h₂]
    have hs : slotIncidenceCount π x = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      unfold slotIncidence
      split
      · rename_i hj
        have ha : (externalSlot j).1 ∈ π.active :=
          Finset.mem_filter.mpr ⟨externalSlot_mem_template j, hj.1⟩
        exact False.elim (hx (hj.2 ▸ ha))
      · rfl
    simp [hb, hs]

private def bondFactor (π : PatternData) (next : Bool) (e : Plane × Plane) : LocalPolynomial :=
  if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1
  else 1 + formalDot (fun k => (Sum.inl (e.1, k) : LocalVariable))
    (fun k => (Sum.inl (e.2, k) : LocalVariable))

private def slotFactor (π : PatternData) (j : Fin 20) : LocalPolynomial :=
  if π.statusAt (externalSlot j).1 = .X then 1
  else 1 + formalDot (fun k => (Sum.inl ((externalSlot j).1, k) : LocalVariable))
    (fun k => (Sum.inr (j, k) : LocalVariable))

private theorem bondFactor_siteBound (hfd : FormalDotSupport)
    (π : PatternData) (next : Bool) (e : Plane × Plane) (x : Plane) :
    SiteBound (bondFactor π next e) x (bondIncidence x e) := by
  unfold bondFactor
  split
  · exact siteBound_mono (siteBound_one x) (Nat.zero_le _)
  · apply siteBound_add
    · exact siteBound_mono (siteBound_one x) (Nat.zero_le _)
    · exact ⟨hfd.1 e.1 e.2 x⟩

private theorem slotFactor_siteBound (hfd : FormalDotSupport)
    (π : PatternData) (j : Fin 20) (x : Plane) :
    SiteBound (slotFactor π j) x (slotIncidence π x j) := by
  unfold slotFactor slotIncidence
  by_cases hs : π.statusAt (externalSlot j).1 = .X
  · simp [hs]
    exact siteBound_one x
  · simp [hs]
    apply siteBound_add
    · exact siteBound_mono (siteBound_one x) (Nat.zero_le _)
    · exact ⟨hfd.2 (externalSlot j).1 x j⟩

private theorem originalIntegrand_siteBound (hfd : FormalDotSupport)
    (π : PatternData) (next : Bool) (x : Plane) :
    SiteBound (originalIntegrand π next) x
      (bondIncidenceCount π x + slotIncidenceCount π x) := by
  classical
  have hb : SiteBound (∏ e ∈ π.bonds, bondFactor π next e) x (bondIncidenceCount π x) := by
    exact siteBound_prod π.bonds (bondFactor π next) x (bondIncidence x)
      (fun e he => bondFactor_siteBound hfd π next e x)
  have hs : SiteBound (∏ j ∈ (Finset.univ : Finset (Fin 20)), slotFactor π j) x
      (∑ j ∈ (Finset.univ : Finset (Fin 20)), slotIncidence π x j) := by
    exact siteBound_prod Finset.univ (slotFactor π) x (slotIncidence π x)
      (fun j hj => slotFactor_siteBound hfd π j x)
  have hs' : SiteBound (∏ j : Fin 20, slotFactor π j) x (slotIncidenceCount π x) := by
    simpa [slotIncidenceCount] using hs
  have hmul := siteBound_mul hb hs'
  simpa [originalIntegrand, bondFactor, slotFactor] using hmul

theorem main : AKLT.Blueprint.H1.OriginalDegreeStatement := by
  intro π _hcovered next
  constructor
  · intro m hm x hx k
    have hb := (originalIntegrand_siteBound formalDotSupport π next x).holds m hm
    have hc := localCounts π x
    simp [hx] at hc
    have hdeg : siteExponent m x = 0 := by omega
    have hk_le : m (.inl (x, k)) ≤ siteExponent m x := by
      unfold siteExponent
      exact Finset.single_le_sum
        (fun k' _ => Nat.zero_le (m (.inl (x, k')))) (Finset.mem_univ k)
    omega
  · intro m hm x
    have hb := (originalIntegrand_siteBound formalDotSupport π next x).holds m hm
    have hc := localCounts π x
    by_cases hx : x ∈ π.active
    · simp [hx] at hc
      exact hb.trans hc
    · simp [hx] at hc
      exact hb.trans (by omega)

end AKLT.W.H1M009

#print axioms AKLT.W.H1M009.main
