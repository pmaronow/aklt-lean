import AKLT.Blueprint.H1.NodesPassage

noncomputable section
open scoped BigOperators Pointwise
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M010

private def slotDegree (m : LocalVariable →₀ ℕ) (j : Fin 20) : ℕ :=
  ∑ k : Fin 3, m (.inr (j, k))

private lemma formalDot_support_shape (a b : Fin 3 → LocalVariable)
    {m : LocalVariable →₀ ℕ}
    (hm : m ∈ (formalDot a b).support) :
    ∃ k : Fin 3, m = Finsupp.single (a k) 1 + Finsupp.single (b k) 1 := by
  classical
  have hsum : formalDot a b =
      (MvPolynomial.X (a 0) : LocalPolynomial) * MvPolynomial.X (b 0) +
        ((MvPolynomial.X (a 1) : LocalPolynomial) * MvPolynomial.X (b 1) +
          (MvPolynomial.X (a 2) : LocalPolynomial) * MvPolynomial.X (b 2)) := by
    simp [formalDot, Fin.sum_univ_three, add_assoc]
  rw [hsum] at hm
  have hmem : m ∈
      ((MvPolynomial.X (a 0) : LocalPolynomial) * MvPolynomial.X (b 0)).support ∪
        ((MvPolynomial.X (a 1) : LocalPolynomial) * MvPolynomial.X (b 1) +
          (MvPolynomial.X (a 2) : LocalPolynomial) * MvPolynomial.X (b 2)).support :=
    MvPolynomial.support_add hm
  have finish (k : Fin 3) (hk : m ∈
      ((MvPolynomial.X (a k) : LocalPolynomial) * MvPolynomial.X (b k)).support) :
      ∃ k, m = Finsupp.single (a k) 1 + Finsupp.single (b k) 1 := by
    have hmul := (MvPolynomial.support_mul (MvPolynomial.X (a k))
      (MvPolynomial.X (b k))) hk
    have hmem' : m ∈
        ((({Finsupp.single (a k) 1} : Finset (LocalVariable →₀ ℕ)) +
          ({Finsupp.single (b k) 1} : Finset (LocalVariable →₀ ℕ))) :
          Finset (LocalVariable →₀ ℕ)) := by
      simpa only [MvPolynomial.support_X] using hmul
    rcases Finset.mem_add.mp hmem' with ⟨x, hx, y, hy, hxy⟩
    simp only [Finset.mem_singleton] at hx hy
    subst x
    subst y
    exact ⟨k, hxy.symm⟩
  rcases Finset.mem_union.mp hmem with hzero | hrest
  · exact finish 0 hzero
  · have hmem' : m ∈
        ((MvPolynomial.X (a 1) : LocalPolynomial) * MvPolynomial.X (b 1)).support ∪
          ((MvPolynomial.X (a 2) : LocalPolynomial) * MvPolynomial.X (b 2)).support :=
      MvPolynomial.support_add hrest
    rcases Finset.mem_union.mp hmem' with hone | htwo
    · exact finish 1 hone
    · exact finish 2 htwo

private lemma slotDegree_add (m n : LocalVariable →₀ ℕ) (j : Fin 20) :
    slotDegree (m + n) j = slotDegree m j + slotDegree n j := by
  simp [slotDegree, Finsupp.add_apply, Finset.sum_add_distrib]

private lemma slotDegree_formalDot_internal (x y : Plane) (j : Fin 20)
    {m : LocalVariable →₀ ℕ}
    (hm : m ∈ (formalDot (fun k => Sum.inl (x, k))
      (fun k => Sum.inl (y, k))).support) : slotDegree m j = 0 := by
  rcases formalDot_support_shape _ _ hm with ⟨k, rfl⟩
  simp [slotDegree, Finsupp.add_apply]

private lemma slotDegree_formalDot_external (x : Plane) (i j : Fin 20)
    {m : LocalVariable →₀ ℕ}
    (hm : m ∈ (formalDot (fun k => Sum.inl (x, k))
      (fun k => Sum.inr (i, k))).support) :
    slotDegree m j = if i = j then 1 else 0 := by
  rcases formalDot_support_shape _ _ hm with ⟨k, rfl⟩
  by_cases hij : i = j <;>
    simp [slotDegree, Finsupp.add_apply, Finsupp.single_apply, hij]

private lemma slotDegree_one_add_le (p : LocalPolynomial) (j : Fin 20) (b : ℕ)
    (hp : ∀ m ∈ p.support, slotDegree m j ≤ b) :
    ∀ m ∈ (1 + p).support, slotDegree m j ≤ b := by
  intro m hm
  have hsub : (1 + p).support ⊆ (1 : LocalPolynomial).support ∪ p.support :=
    MvPolynomial.support_add
  have hmem := hsub hm
  rcases Finset.mem_union.mp hmem with hconst | hpoly
  · simp only [MvPolynomial.support_one, Finset.mem_singleton] at hconst
    subst m
    simp [slotDegree]
  · exact hp m hpoly

private lemma slotDegree_one_add_zero (p : LocalPolynomial) (j : Fin 20)
    (hp : ∀ m ∈ p.support, slotDegree m j = 0) :
    ∀ m ∈ (1 + p).support, slotDegree m j = 0 := by
  intro m hm
  have hsub : (1 + p).support ⊆ (1 : LocalPolynomial).support ∪ p.support :=
    MvPolynomial.support_add
  have hmem := hsub hm
  rcases Finset.mem_union.mp hmem with hconst | hpoly
  · simp only [MvPolynomial.support_one, Finset.mem_singleton] at hconst
    subst m
    simp [slotDegree]
  · exact hp m hpoly

private lemma slotDegree_mul_le (p q : LocalPolynomial) (j : Fin 20) (a b : ℕ)
    (hp : ∀ m ∈ p.support, slotDegree m j ≤ a)
    (hq : ∀ m ∈ q.support, slotDegree m j ≤ b) :
    ∀ m ∈ (p * q).support, slotDegree m j ≤ a + b := by
  classical
  intro m hm
  have hmem := (MvPolynomial.support_mul p q) hm
  rcases Finset.mem_add.mp hmem with ⟨x, hx, y, hy, hxy⟩
  rw [← hxy, slotDegree_add]
  exact Nat.add_le_add (hp x hx) (hq y hy)

private lemma slotDegree_prod_le {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → LocalPolynomial) (j : Fin 20) (b : α → ℕ)
    (hp : ∀ i ∈ s, ∀ m ∈ (p i).support, slotDegree m j ≤ b i) :
    ∀ m ∈ (∏ i ∈ s, p i).support, slotDegree m j ≤ ∑ i ∈ s, b i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro m hm
      simp at hm
      subst m
      simp [slotDegree]
  | @insert i s his ih =>
      intro m hm
      rw [Finset.prod_insert his] at hm
      rw [Finset.sum_insert his]
      apply slotDegree_mul_le (p i) (∏ k ∈ s, p k) j (b i) (∑ k ∈ s, b k)
      · exact hp i (Finset.mem_insert_self i s) 
      · exact ih (fun k hk => hp k (Finset.mem_insert_of_mem hk))
      · exact hm

private lemma slotDegree_bond_factor (π : PatternData) (next : Bool)
    (e : Plane × Plane) (j : Fin 20) :
    ∀ m ∈ (if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1
      else 1 + formalDot (fun k => Sum.inl (e.1, k)) (fun k => Sum.inl (e.2, k))).support,
      slotDegree m j = 0 := by
  intro m hm
  split at hm
  · simp only [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst m
    simp [slotDegree]
  · exact slotDegree_one_add_zero _ j
      (fun m hm => slotDegree_formalDot_internal e.1 e.2 j hm) m hm

private lemma slotDegree_external_factor (π : PatternData) (i j : Fin 20) :
    ∀ m ∈ (if π.statusAt (externalSlot i).1 = .X then 1
      else 1 + formalDot (fun k => Sum.inl ((externalSlot i).1, k))
        (fun k => Sum.inr (i, k))).support,
      slotDegree m j ≤ if i = j then 1 else 0 := by
  intro m hm
  split at hm
  · simp only [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst m
    simp [slotDegree]
  · exact slotDegree_one_add_le _ j (if i = j then 1 else 0)
      (fun m hm => by
        rw [slotDegree_formalDot_external (externalSlot i).1 i j hm]) m hm

private theorem original_local_vector_affine (π : PatternData) (next : Bool) :
    LocalVectorAffine (originalIntegrand π next) := by
  classical
  intro m hm j
  change m ∈ (originalIntegrand π next).support at hm
  change slotDegree m j ≤ 1
  unfold originalIntegrand at hm
  have hb : ∀ m ∈ (∏ e ∈ π.bonds,
      if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1
      else 1 + formalDot (fun k => Sum.inl (e.1, k)) (fun k => Sum.inl (e.2, k))).support,
      slotDegree m j ≤ 0 := by
    intro m hm
    have h := slotDegree_prod_le π.bonds
      (fun e => if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1
        else 1 + formalDot (fun k => Sum.inl (e.1, k)) (fun k => Sum.inl (e.2, k)))
      j (fun _ => 0) (by
        intro e he m hm
        have hz := slotDegree_bond_factor π next e j m hm
        omega) m hm
    simpa using h
  have he : ∀ m ∈ (∏ i : Fin 20,
      if π.statusAt (externalSlot i).1 = .X then 1
      else 1 + formalDot (fun k => Sum.inl ((externalSlot i).1, k))
        (fun k => Sum.inr (i, k))).support,
      slotDegree m j ≤ 1 := by
    intro m hm
    have h := slotDegree_prod_le (Finset.univ : Finset (Fin 20))
      (fun i => if π.statusAt (externalSlot i).1 = .X then 1
        else 1 + formalDot (fun k => Sum.inl ((externalSlot i).1, k))
          (fun k => Sum.inr (i, k))) j (fun i => if i = j then 1 else 0)
      (by
        intro i hi m hm
        exact slotDegree_external_factor π i j m hm) m hm
    have hs : (∑ i : Fin 20, if i = j then 1 else 0) = 1 := by simp
    simpa [hs] using h
  have hprod := slotDegree_mul_le
    (∏ e ∈ π.bonds,
      if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1
      else 1 + formalDot (fun k => Sum.inl (e.1, k)) (fun k => Sum.inl (e.2, k)))
    (∏ i : Fin 20,
      if π.statusAt (externalSlot i).1 = .X then 1
      else 1 + formalDot (fun k => Sum.inl ((externalSlot i).1, k))
        (fun k => Sum.inr (i, k))) j 0 1 hb he m hm
  simpa using hprod

private lemma dot_orthogonal_mulVec (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R.transpose * R = 1) (x y : Vec3) :
    dot (R.mulVec x) (R.mulVec y) = dot x y := by
  classical
  change dotProduct (R.mulVec x) (R.mulVec y) = dotProduct x y
  have hfirst : dotProduct (R.mulVec x) (R.mulVec y) =
      dotProduct x (R.transpose.mulVec (R.mulVec y)) := by
    have h := Matrix.dotProduct_mulVec x R.transpose (R.mulVec y)
    rw [Matrix.vecMul_transpose] at h
    exact h.symm
  calc
    dotProduct (R.mulVec x) (R.mulVec y) =
        dotProduct x (R.transpose.mulVec (R.mulVec y)) := hfirst
    _ = dotProduct x y := by
      rw [Matrix.mulVec_mulVec, hR]
      simp

private lemma localEvaluation_mul (p q : LocalPolynomial) (n : Plane → Vec3)
    (u : Fin 20 → Vec3) :
    localEvaluation (p * q) n u = localEvaluation p n u * localEvaluation q n u := by
  simp [localEvaluation, MvPolynomial.eval₂_mul]

private lemma localEvaluation_prod {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → LocalPolynomial) (n : Plane → Vec3) (u : Fin 20 → Vec3) :
    localEvaluation (∏ i ∈ s, p i) n u = ∏ i ∈ s, localEvaluation (p i) n u := by
  simp [localEvaluation, MvPolynomial.eval₂_prod]

private theorem original_integrand_invariant (π : PatternData) (next : Bool) :
    IntegrandInvariant (originalIntegrand π next) := by
  intro R hR n u
  have hdot (x y : Plane) :
      (∑ k : Fin 3, (R.mulVec (n x)) k * (R.mulVec (n y)) k) =
        ∑ k : Fin 3, n x k * n y k := by
    exact dot_orthogonal_mulVec R hR (n x) (n y)
  have hslot (x : Plane) (j : Fin 20) :
      (∑ k : Fin 3, (R.mulVec (n x)) k * (R.mulVec (u j)) k) =
        ∑ k : Fin 3, n x k * u j k := by
    exact dot_orthogonal_mulVec R hR (n x) (u j)
  have hbond (e : Plane × Plane) :
      localEvaluation (1 + formalDot (fun k => Sum.inl (e.1, k))
          (fun k => Sum.inl (e.2, k))) (fun x => R.mulVec (n x))
          (fun j => R.mulVec (u j)) =
        localEvaluation (1 + formalDot (fun k => Sum.inl (e.1, k))
          (fun k => Sum.inl (e.2, k))) n u := by
    simp [localEvaluation, formalDot, hdot]
  have hext (i : Fin 20) :
      localEvaluation (1 + formalDot (fun k => Sum.inl ((externalSlot i).1, k))
          (fun k => Sum.inr (i, k))) (fun x => R.mulVec (n x))
          (fun j => R.mulVec (u j)) =
        localEvaluation (1 + formalDot (fun k => Sum.inl ((externalSlot i).1, k))
          (fun k => Sum.inr (i, k))) n u := by
    simp [localEvaluation, formalDot, hslot]
  change localEvaluation
      ((∏ e ∈ π.bonds,
        if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1
        else 1 + formalDot (fun k => Sum.inl (e.1, k)) (fun k => Sum.inl (e.2, k))) *
       ∏ j : Fin 20,
        if π.statusAt (externalSlot j).1 = .X then 1
        else 1 + formalDot (fun k => Sum.inl ((externalSlot j).1, k))
          (fun k => Sum.inr (j, k)))
      (fun x => R.mulVec (n x)) (fun j => R.mulVec (u j)) =
    localEvaluation
      ((∏ e ∈ π.bonds,
        if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1
        else 1 + formalDot (fun k => Sum.inl (e.1, k)) (fun k => Sum.inl (e.2, k))) *
       ∏ j : Fin 20,
        if π.statusAt (externalSlot j).1 = .X then 1
        else 1 + formalDot (fun k => Sum.inl ((externalSlot j).1, k))
          (fun k => Sum.inr (j, k))) n u
  rw [localEvaluation_mul, localEvaluation_mul, localEvaluation_prod,
    localEvaluation_prod, localEvaluation_prod, localEvaluation_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro e he
    by_cases hc : next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step}
    · simp [hc, localEvaluation]
    · simp only [hc]
      exact hbond e
  · apply Finset.prod_congr rfl
    intro j hj
    by_cases hc : π.statusAt (externalSlot j).1 = .X
    · simp [hc, localEvaluation]
    · simp only [hc]
      exact hext j

theorem main : AKLT.Blueprint.H1.OriginalFactorStructureStatement := by
  intro π next
  exact ⟨original_local_vector_affine π next, original_integrand_invariant π next⟩

end AKLT.W.H1M010

#print axioms AKLT.W.H1M010.main

end
