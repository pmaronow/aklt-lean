module
public import AKLT.W.H1M052.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M052

def inversionSign (I : Finset (Fin 20)) (j : Fin 20) : ℝ := if j ∈ I then -1 else 1

theorem inversionSign_sq (I : Finset (Fin 20)) (j : Fin 20) :
    inversionSign I j ^ 2 = 1 := by
  unfold inversionSign
  split_ifs <;> norm_num

def realizationHom (I : Finset (Fin 20)) (n : Plane → Vec3) :
    LocalPolynomial →+* RealPoly :=
  (MvPolynomial.eval₂Hom MvPolynomial.C
    (fun v : Fin 20 × Fin 3 => (if v.1 ∈ I then -1 else 1) * MvPolynomial.X v)).comp
  (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Rat.castHom ℝ))
    (fun v => match v with
      | .inl (x, k) => MvPolynomial.C (n x k)
      | .inr v => MvPolynomial.X v))

@[simp] theorem realizationHom_C (I : Finset (Fin 20)) (n : Plane → Vec3) (q : ℚ) :
    realizationHom I n (MvPolynomial.C q) = MvPolynomial.C (q : ℝ) := by
  simp [realizationHom]

@[simp] theorem realizationHom_internal (I : Finset (Fin 20)) (n : Plane → Vec3)
    (x : Plane) (k : Fin 3) :
    realizationHom I n (MvPolynomial.X (.inl (x, k))) = MvPolynomial.C (n x k) := by
  simp [realizationHom]

@[simp] theorem realizationHom_external (I : Finset (Fin 20)) (n : Plane → Vec3)
    (j : Fin 20) (k : Fin 3) :
    realizationHom I n (MvPolynomial.X (.inr (j, k))) =
      MvPolynomial.C (inversionSign I j) * MvPolynomial.X (j, k) := by
  by_cases h : j ∈ I <;> simp [realizationHom, inversionSign, h]

@[simp] theorem realizationHom_dot (I : Finset (Fin 20)) (n : Plane → Vec3)
    (x y : Plane) :
    realizationHom I n (formalDot (fun k => .inl (x, k)) (fun k => .inl (y, k))) =
      MvPolynomial.C (dot (n x) (n y)) := by
  simp [formalDot, dot, map_sum, map_mul]

theorem realizationHom_slot (I : Finset (Fin 20)) (n : Plane → Vec3)
    (x : Plane) (j : Fin 20) (q : ℚ) :
    realizationHom I n (1 + MvPolynomial.C q *
      formalDot (fun k => .inl (x, k)) (fun k => .inr (j, k))) =
      affineSlot j (inversionSign I j • ((q : ℝ) • n x)) := by
  simp only [map_add, map_one, map_mul, realizationHom_C, formalDot, map_sum,
    realizationHom_internal, realizationHom_external, affineSlot, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem realizationHom_slot_one (I : Finset (Fin 20)) (n : Plane → Vec3)
    (x : Plane) (j : Fin 20) :
    realizationHom I n (1 + formalDot (fun k => .inl (x, k)) (fun k => .inr (j, k))) =
      affineSlot j (inversionSign I j • n x) := by
  simpa using realizationHom_slot I n x j 1

def bondScalar (π : PatternData) (r : Representation) (next : Bool)
    (n : Plane → Vec3) : ℝ :=
  ∏ e ∈ π.bonds, if e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r ∧
      ¬ (next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step}) then
    1 + dot (n e.1) (n e.2) else 1

theorem realizationHom_integrand (π : PatternData) (r : Representation)
    (next : Bool) (I : Finset (Fin 20)) (n : Plane → Vec3) :
    realizationHom I n (reducedIntegrand π r next) =
      MvPolynomial.C (bondScalar π r next n) *
        ∏ j : reductionVectors π r,
          affineSlot j.val (inversionSign I j.val • tokenVector π r n j.val) := by
  classical
  simp only [reducedIntegrand, map_mul, map_prod]
  congr 1
  · simp [bondScalar, apply_ite, map_prod, map_add]
  · rw [Finset.prod_coe_sort (reductionVectors π r)
      (fun j => affineSlot j (inversionSign I j • tokenVector π r n j))]
    change _ = ∏ j ∈ (reductionGroups π).biUnion (groupTokens π r), _
    rw [Finset.prod_biUnion (groupTokens_disjoint π r)]
    apply Finset.prod_congr rfl
    intro x hx
    have hvec (j : Fin 20) (hj : j ∈ groupTokens π r x) :=
      tokenVector_at_group π r n x hx j hj
    rw [show (∏ j ∈ groupTokens π r x,
        affineSlot j (inversionSign I j • tokenVector π r n j)) =
      ∏ j ∈ groupTokens π r x,
        affineSlot j (inversionSign I j • groupVector π r n x) from
      Finset.prod_congr rfl (fun j hj => by rw [hvec j hj])]
    unfold groupTokens groupVector
    split_ifs with hp
    · simp only [map_mul, realizationHom_slot_one]
      rw [Finset.prod_pair (group_pair_distinct x)]
    · simp only [Finset.prod_singleton, realizationHom_slot]

/-- The real Pauli image of a fixed spin configuration is a scalar times a
product of its one-token factors. -/
theorem integrand_pauli_tensor (π : PatternData) (r : Representation)
    (next : Bool) (I : Finset (Fin 20)) (n : Plane → Vec3) :
    realPauliOperator (reductionVectors π r)
        (invertRealPolynomial I (specializeInternal (reducedIntegrand π r next) n)) =
      (bondScalar π r next n : ℂ) •
        tensorMatrix (reductionVectors π r)
          (fun j => 1 + blochMatrix (inversionSign I j.val • tokenVector π r n j.val)) := by
  change realPauliOperator _ (realizationHom I n _) = _
  rw [realizationHom_integrand, realPauliOperator_C_mul, realPauliOperator_affine_prod]

end AKLT.W.H1M052
