import AKLT.Cert.H1.Production.Leaves

namespace AKLT.W.H1C010

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

noncomputable section

/-! Integer coefficients are certified by membership in the image of the
coefficientwise map from integer polynomials. All the network operations
preserve this subring, independently of geometry or table acceptance. -/

private def integerPolynomials : Subring VectorPolynomial :=
  (MvPolynomial.map (Int.castRingHom ℚ)).range

private theorem integer_C (z : ℤ) : MvPolynomial.C (z : ℚ) ∈ integerPolynomials := by
  exact ⟨MvPolynomial.C z, MvPolynomial.map_C _ _⟩

private theorem integer_X (v : Fin 20 × Fin 3) :
    MvPolynomial.X v ∈ integerPolynomials := by
  exact ⟨MvPolynomial.X v, MvPolynomial.map_X _ _⟩

private theorem integer_iff (p : VectorPolynomial) :
    p ∈ integerPolynomials ↔ ∀ m, ∃ z : ℤ, p.coeff m = z := by
  constructor
  · rintro ⟨q, rfl⟩ m
    exact ⟨q.coeff m, MvPolynomial.coeff_map _ _ _⟩
  · intro h
    change p ∈ Set.range (MvPolynomial.map (Int.castRingHom ℚ))
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    obtain ⟨m, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    obtain ⟨z, hz⟩ := h m
    exact ⟨z, hz.symm⟩

private theorem integer_sum {α : Type*} (xs : List α) (f : α → VectorPolynomial)
    (h : ∀ x ∈ xs, f x ∈ integerPolynomials) :
    (xs.map f).sum ∈ integerPolynomials := by
  apply integerPolynomials.list_sum_mem
  intro p hp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  exact h x hx

private theorem integer_vectorVariable (token color : Nat) :
    vectorVariable token color ∈ integerPolynomials :=
  integer_X _

private theorem integer_vectorFactor (token color : Nat) :
    (if color == 0 then 1 else vectorVariable token color) ∈ integerPolynomials := by
  split_ifs
  · exact integerPolynomials.one_mem
  · exact integer_vectorVariable _ _

private theorem integer_vectorMonomial (token : Nat) (cs : List Nat) :
    vectorMonomial token cs ∈ integerPolynomials := by
  induction cs generalizing token with
  | nil => exact integerPolynomials.one_mem
  | cons c cs ih =>
    unfold vectorMonomial
    apply integerPolynomials.mul_mem _ (ih _)
    split_ifs
    · exact integerPolynomials.one_mem
    · exact integer_vectorVariable _ _

private theorem integer_localPolynomial (site : Nat) (s : SiteSpec) (l r v : Nat) :
    localPolynomial site s l r v ∈ integerPolynomials := by
  unfold localPolynomial
  split
  · exact integerPolynomials.zero_mem
  · split
    · dsimp only
      apply integerPolynomials.mul_mem (integer_C _)
      exact integer_vectorFactor _ _
    · apply integer_sum
      intro cs _
      exact integerPolynomials.mul_mem (integer_C _) (integer_vectorMonomial _ _)

private theorem getD_property {α : Type*} (P : α → Prop) (xs : List α)
    (h : ∀ x ∈ xs, P x) (d : α) (hd : P d) (i : Nat) : P (xs.getD i d) := by
  induction xs generalizing i with
  | nil => simpa using hd
  | cons x xs ih =>
    cases i with
    | zero => simpa only [List.getD_cons_zero] using h x (by simp)
    | succ i =>
      rw [List.getD_cons_succ]
      exact ih (fun y hy => h y (by simp [hy])) i

private def IntegerMatrix (m : PolyFour) : Prop :=
  ∀ row ∈ m, ∀ p ∈ row, p ∈ integerPolynomials

private theorem integer_polyEntry {m : PolyFour} (hm : IntegerMatrix m) (i j : Nat) :
    polyEntry m i j ∈ integerPolynomials := by
  apply getD_property (fun p => p ∈ integerPolynomials)
  · exact getD_property (fun row => ∀ p ∈ row, p ∈ integerPolynomials)
      m hm [] (by simp) i
  · exact integerPolynomials.zero_mem

private theorem integer_matrix (f : Nat → Nat → VectorPolynomial)
    (hf : ∀ i j, f i j ∈ integerPolynomials) :
    IntegerMatrix ((List.range 4).map fun i => (List.range 4).map fun j => f i j) := by
  intro row hrow p hp
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrow
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
  exact hf i j

private theorem integer_polyIdentity : IntegerMatrix polyIdentity := by
  apply integer_matrix
  intro i j
  split_ifs
  · exact integerPolynomials.one_mem
  · exact integerPolynomials.zero_mem

private theorem integer_polyMul {a b : PolyFour}
    (ha : IntegerMatrix a) (hb : IntegerMatrix b) : IntegerMatrix (polyMul a b) := by
  apply integer_matrix
  intro i j
  apply integer_sum
  intro k _
  exact integerPolynomials.mul_mem (integer_polyEntry ha _ _) (integer_polyEntry hb _ _)

private theorem integer_polyTrace {a : PolyFour} (ha : IntegerMatrix a) :
    polyTrace a ∈ integerPolynomials := by
  apply integer_sum
  intro i _
  exact integer_polyEntry ha _ _

private theorem integer_polynomialRingProduct (site : Nat) (ss : List PackedSite)
    (codes : List Nat) : IntegerMatrix (polynomialRingProduct site ss codes) := by
  induction ss generalizing site codes with
  | nil => exact integer_polyIdentity
  | cons s ss ih =>
    apply integer_polyMul _ (ih _ _)
    apply integer_matrix
    intro l r
    exact integer_localPolynomial _ _ _ _ _

private theorem integer_polynomialRingValue (ss : List PackedSite) (codes : List Nat) :
    polynomialRingValue ss codes ∈ integerPolynomials :=
  integer_polyTrace (integer_polynomialRingProduct _ _ _)

/-- Every coefficient of the full integer network numerator is an integer. -/
theorem networkIntegerCoefficients (ss : List PackedSite) (out : Nat) (next : Bool)
    (m : (Fin 20 × Fin 3) →₀ ℕ) :
    ∃ z : ℤ, (networkNumerator ss out next).coeff m = z := by
  apply (integer_iff _).mp _ m
  unfold networkNumerator
  apply integerPolynomials.add_mem
  · apply integerPolynomials.mul_mem _ (integer_polynomialRingValue _ _)
    cases next <;> exact integer_C _
  · apply integerPolynomials.list_sum_mem
    intro p hp
    obtain ⟨⟨x, y⟩, _, hp⟩ := List.mem_filterMap.mp hp
    dsimp only at hp
    by_cases h : (next && (x == out || y == out)) = true
    · simp only [ite_eq_left h] at hp
      cases hp
    · rw [ite_eq_right h, Option.some.injEq] at hp
      rw [← hp]
      apply integer_sum
      intro k _
      exact integer_polynomialRingValue _ _

private def inversionHom (I : Finset (Fin 20)) : VectorPolynomial →+* VectorPolynomial :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun v =>
    (if v.1 ∈ I then -1 else 1) * MvPolynomial.X v)

private theorem inversionHom_C (I : Finset (Fin 20)) (c : ℚ) :
    inversionHom I (MvPolynomial.C c) = MvPolynomial.C c :=
  MvPolynomial.eval₂Hom_C _ _ _

private theorem inversionHom_integer (I : Finset (Fin 20)) {p : VectorPolynomial}
    (hp : p ∈ integerPolynomials) : inversionHom I p ∈ integerPolynomials := by
  obtain ⟨q, rfl⟩ := hp
  induction q using MvPolynomial.induction_on with
  | C z =>
    rw [MvPolynomial.map_C, inversionHom_C]
    exact integer_C z
  | add p q hp hq =>
    rw [map_add, map_add]
    exact integerPolynomials.add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul, map_mul, MvPolynomial.map_X]
    apply integerPolynomials.mul_mem hp
    rw [inversionHom, MvPolynomial.eval₂Hom_X']
    apply integerPolynomials.mul_mem _ (integer_X v)
    split_ifs
    · exact integerPolynomials.neg_mem integerPolynomials.one_mem
    · exact integerPolynomials.one_mem

private theorem inversionHom_involutive (I : Finset (Fin 20)) (p : VectorPolynomial) :
    inversionHom I (inversionHom I p) = p := by
  have hh : (inversionHom I).comp (inversionHom I) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [inversionHom]
    · intro v
      by_cases h : v.1 ∈ I <;> simp [inversionHom, h]
  exact RingHom.congr_fun hh p

/-- Undoing sign inversion preserves all scaled coefficients, including those
outside the support. No matrix entries are used in this argument. -/
theorem inversionCoefficientTransfer (I : Finset (Fin 20)) (p : VectorPolynomial) (k : ℚ)
    (h : ∀ m, ∃ z : ℤ, k * (invertPolynomial I p).coeff m = z) :
    ∀ m, ∃ z : ℤ, k * p.coeff m = z := by
  have hi : MvPolynomial.C k * inversionHom I p ∈ integerPolynomials := by
    apply (integer_iff _).mpr
    intro m
    simpa only [MvPolynomial.coeff_C_mul, inversionHom, invertPolynomial] using h m
  have hh := inversionHom_integer I hi
  rw [map_mul, inversionHom_C, inversionHom_involutive] at hh
  intro m
  simpa only [MvPolynomial.coeff_C_mul] using (integer_iff _).mp hh m

end

end AKLT.W.H1C010

#print axioms AKLT.W.H1C010.networkIntegerCoefficients
#print axioms AKLT.W.H1C010.inversionCoefficientTransfer
