STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M052/AKLT/W/H1M052/Main.lean): the requested closed theorem and the reused Pauli difference-linearity lemma.
- [Tensor.lean](/home/ubuntu/aklt/wt/LW_H1M052/AKLT/W/H1M052/Tensor.lean): tensor matrix multiplication, one-token lifts, pair factorization, and commutation with pair symmetries.
- [Pauli.lean](/home/ubuntu/aklt/wt/LW_H1M052/AKLT/W/H1M052/Pauli.lean): coefficient expansion of independent affine slot factors and its real Pauli tensor formula.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_H1M052/AKLT/W/H1M052/Geometry.lean): token ownership, disjoint group tokens, and membership of retained corners in the spin support.
- [Realization.lean](/home/ubuntu/aklt/wt/LW_H1M052/AKLT/W/H1M052/Realization.lean): specialization/inversion of the reduced integrand into scalar and affine slot factors.
- [Expansion.lean](/home/ubuntu/aklt/wt/LW_H1M052/AKLT/W/H1M052/Expansion.lean): equal-sign pair extraction and finite enumeration with unit-spin padding at zero coefficients.
- [Raw.lean](/home/ubuntu/aklt/wt/LW_H1M052/AKLT/W/H1M052/Raw.lean): finite raw current/next expansions, zero U-atom weights, and the raw difference pair expansion.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_H1M052/AKLT/W/H1M052/Audit.lean): exact-type check and one `#print axioms` command for every exported theorem.

All Lean source changes are confined to `AKLT/W/H1M052/`. No frozen statement or other existing project file was changed.

## Requested declaration

```lean
theorem AKLT.W.H1M052.main :
    AKLT.Blueprint.H1.PairExpansionFromRealizationStatement
```

`main` is proved with exactly the requested closed type. It has no additional parameters or residual assumptions.

## Proof

The real Pauli map takes a product with one affine factor per token to the corresponding tensor product. This follows by expanding each factor in its four Pauli monomials, identifying the sum of slot exponents with `pauliExponent`, and using injectivity of that exponent map.

Each reduction-group token has its original group as external-slot owner, so distinct groups have disjoint tokens. Specializing internal spins and applying inversion therefore turns `reducedIntegrand` into a real scalar times independent affine slot factors. Group inversion gives the two selected corner slots the same sign. Their matrix factors form `pairTerm`; the auxiliary tensor has identities in those two slots and commutes with exchange and the symmetric projection.

Current and next use the same retained spin index type. Their scalar weights can be subtracted for each configuration before enumeration by `Fin`. At a U corner, the zero atom makes both weights vanish. The general finite-sum lemma replaces the spin of any zero-coefficient term by the fixed unit vector `(1,0,0)`, preserving the sum and satisfying the unit-spin clause. This uses zero-weight padding instead of filtering the index set.

Finally, the supplied realization equalities and `pauliOperator_invert_difference` identify the required Pauli operator with this raw difference. The difference-linearity lemma is reused from the earlier attempt; its unresolved residual and conditional bridge have been replaced by proofs. No other blueprint leaf is used as a lemma. The raw algebra actually holds for any `PatternData` with the selected pair, so the coveredness premise is not needed by that helper.

## Build and validation

```sh
PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1M052.Main
PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/H1M052/Audit.lean
```

- Main build: passed, rebuilding all seven proof modules; ELAPSED_SECONDS=48.01. No warnings.
- Exact-type and axiom audit: passed; ELAPSED_SECONDS=5.41.
- [Build log](/home/ubuntu/aklt/reports/LW/H1M052/build-main.log) and [audit log](/home/ubuntu/aklt/reports/LW/H1M052/audit.log).
- Source scan found no forbidden proof constructs.

## Axioms

All 57 exported theorems were checked individually. Their complete `#print axioms` output is:

```text
'AKLT.W.H1M052.tensorMatrix_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.tensorMatrix_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.tensorMatrix_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.toEnd_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.toEnd_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.mul_swapMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.swapMatrix_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.tensorMatrix_commute_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.tensorEnd_commute_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.remainingTensor_commute' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.tensorMatrix_factor_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.slotExponent_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.pauliExponent_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.pauliExponent_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.sum_slotExponent' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.prod_slotPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.realPauliOperator_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.realPauliOperator_C_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.realPauliOperator_monomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.realPauliOperator_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.affineSlot_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.pauliCoordinate_matrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.realPauliOperator_affine_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.group_mem_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.leader_owner' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.second_owner' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.pair_corner' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.token_owner' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.groupTokens_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.group_pair_distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.pair_ne_origin' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.pair_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.tokenVector_at_group' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.tokenVector_leader' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.tokenVector_second' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.inversionSign_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.realizationHom_C' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.realizationHom_internal' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.realizationHom_external' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.realizationHom_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.realizationHom_slot' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.realizationHom_slot_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.realizationHom_integrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.integrand_pauli_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.blochMatrix_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.summand_factor_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.pairExpansion_of_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.spinVector_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.spinVector_unit_of_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.toEnd_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.toEnd_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.rawPauli_tensor_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.rawEnd_pair_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.spinMass_zero_at_U' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.rawDifference_pairExpansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.pauliOperator_invert_difference' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M052.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Exported declaration signatures

All names below are in namespace `AKLT.W.H1M052`. The source files open `AKLT.Defs`, `AKLT.Blueprint.H1`, and the `BigOperators` and `ComplexOrder` scopes. The following catalog includes all public theorem and definition signatures; abbreviation bodies are included where the type is inferred. Every theorem has a completed proof in its linked source file.

### Tensor.lean

```lean
abbrev SmallMatrix := Matrix (Fin 2) (Fin 2) ℂ

def tensorMatrix (J : Finset (Fin 20)) (A : J → SmallMatrix) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ

@[simp] theorem tensorMatrix_one (J : Finset (Fin 20)) :
    tensorMatrix J (fun _ => 1) = 1

theorem tensorMatrix_mul (J : Finset (Fin 20)) (A B : J → SmallMatrix) :
    tensorMatrix J (fun j => A j * B j) = tensorMatrix J A * tensorMatrix J B

theorem tensorMatrix_single (J : Finset (Fin 20)) (j : J) (A : SmallMatrix) :
    tensorMatrix J (fun l => if l = j then A else 1) = tokenMatrix J j A

abbrev toEnd {J : Finset (Fin 20)}
    (M : Matrix (J → Fin 2) (J → Fin 2) ℂ) := Matrix.toEuclideanLin M

@[simp] theorem toEnd_mul {J : Finset (Fin 20)}
    (A B : Matrix (J → Fin 2) (J → Fin 2) ℂ) :
    toEnd (A * B) = toEnd A * toEnd B

@[simp] theorem toEnd_one (J : Finset (Fin 20)) :
    toEnd (1 : Matrix (J → Fin 2) (J → Fin 2) ℂ) = 1

def swapMatrix {J : Finset (Fin 20)} (j k : J) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ

theorem mul_swapMatrix {J : Finset (Fin 20)} (j k : J)
    (A : Matrix (J → Fin 2) (J → Fin 2) ℂ) (σ τ : J → Fin 2) :
    (A * swapMatrix j k) σ τ = A σ (τ ∘ Equiv.swap j k)

theorem swapMatrix_mul {J : Finset (Fin 20)} (j k : J)
    (A : Matrix (J → Fin 2) (J → Fin 2) ℂ) (σ τ : J → Fin 2) :
    (swapMatrix j k * A) σ τ = A (σ ∘ Equiv.swap j k) τ

theorem tensorMatrix_commute_swap {J : Finset (Fin 20)} (j k : J)
    (A : J → SmallMatrix) (h : A j = A k) :
    Commute (tensorMatrix J A) (swapMatrix j k)

theorem tensorEnd_commute_pair {J : Finset (Fin 20)} (j k : J)
    (A : J → SmallMatrix) (h : A j = A k) :
    Commute (toEnd (tensorMatrix J A)) (exchangeOperator J j k) ∧
      Commute (toEnd (tensorMatrix J A)) (symmetricPairProjection J j k)

def remainingTensor {J : Finset (Fin 20)} (j k : J) (A : J → SmallMatrix) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ

theorem remainingTensor_commute {J : Finset (Fin 20)} (j k : J) (A : J → SmallMatrix) :
    Commute (toEnd (remainingTensor j k A)) (exchangeOperator J j k) ∧
      Commute (toEnd (remainingTensor j k A)) (symmetricPairProjection J j k)

theorem tensorMatrix_factor_pair {J : Finset (Fin 20)} (j k : J) (hjk : j ≠ k)
    (A : J → SmallMatrix) (B : SmallMatrix) (hj : A j = B) (hk : A k = B) :
    tensorMatrix J A = (tokenMatrix J j B * tokenMatrix J k B) * remainingTensor j k A
```

### Pauli.lean

```lean
abbrev RealPoly := MvPolynomial (Fin 20 × Fin 3) ℝ

def slotExponent (j : Fin 20) (a : Fin 4) : (Fin 20 × Fin 3) →₀ ℕ

@[simp] theorem slotExponent_apply (j l : Fin 20) (a : Fin 4) (k : Fin 3) :
    slotExponent j a (l, k) = if l = j ∧ a.val = k.val + 1 then 1 else 0

@[simp] theorem pauliExponent_apply (J : Finset (Fin 20)) (a : J → Fin 4)
    (j : J) (k : Fin 3) :
    pauliExponent J a (j.val, k) = if (a j).val = k.val + 1 then 1 else 0

theorem pauliExponent_injective (J : Finset (Fin 20)) :
    Function.Injective (pauliExponent J)

theorem sum_slotExponent (J : Finset (Fin 20)) (a : J → Fin 4) :
    (∑ j : J, slotExponent j.val (a j)) = pauliExponent J a

def slotPolynomial (j : Fin 20) (b : Fin 4 → ℝ) : RealPoly

theorem prod_slotPolynomial (J : Finset (Fin 20)) (b : J → Fin 4 → ℝ) :
    (∏ j : J, slotPolynomial j.val (b j)) =
      ∑ a : J → Fin 4, MvPolynomial.monomial (pauliExponent J a) (∏ j, b j (a j))

theorem realPauliOperator_sum (J : Finset (Fin 20)) {α : Type*} (s : Finset α)
    (p : α → RealPoly) :
    realPauliOperator J (∑ a ∈ s, p a) = ∑ a ∈ s, realPauliOperator J (p a)

theorem realPauliOperator_C_mul (J : Finset (Fin 20)) (c : ℝ) (p : RealPoly) :
    realPauliOperator J (MvPolynomial.C c * p) = (c : ℂ) • realPauliOperator J p

theorem realPauliOperator_monomial (J : Finset (Fin 20)) (a : J → Fin 4) (c : ℝ) :
    realPauliOperator J (MvPolynomial.monomial (pauliExponent J a) c) =
      (c : ℂ) • tensorMatrix J (fun j => pauli (a j))

theorem realPauliOperator_prod (J : Finset (Fin 20)) (b : J → Fin 4 → ℝ) :
    realPauliOperator J (∏ j : J, slotPolynomial j.val (b j)) =
      tensorMatrix J (fun j => ∑ a : Fin 4, (b j a : ℂ) • pauli a)

def affineSlot (j : Fin 20) (n : Vec3) : RealPoly

theorem affineSlot_eq (j : Fin 20) (n : Vec3) :
    affineSlot j n = slotPolynomial j (pauliCoordinate n)

theorem pauliCoordinate_matrix (n : Vec3) :
    (∑ a : Fin 4, (pauliCoordinate n a : ℂ) • pauli a) = 1 + blochMatrix n

theorem realPauliOperator_affine_prod (J : Finset (Fin 20)) (n : J → Vec3) :
    realPauliOperator J (∏ j : J, affineSlot j.val (n j)) =
      tensorMatrix J (fun j => 1 + blochMatrix (n j))
```

### Geometry.lean

```lean
def groupTokens (π : PatternData) (r : Representation) (x : Plane) : Finset (Fin 20)

theorem group_mem_boundary (π : PatternData) (x : reductionGroups π) :
    x.val ∈ templateCorners ∪ templateTips

theorem leader_owner (x : Plane) (hx : x ∈ templateCorners ∪ templateTips) :
    (externalSlot (groupLeader x)).1 = x

theorem second_owner (x : Plane) (hx : x ∈ templateCorners) :
    (externalSlot (groupSecond x)).1 = x

theorem pair_corner (π : PatternData) (r : Representation) (x : Plane)
    (h : groupIsPair π r x = true) :
    x ∈ templateCorners ∧ ¬ SingleReplacement π r x

theorem token_owner (π : PatternData) (r : Representation) (x : Plane)
    (hx : x ∈ reductionGroups π) (j : Fin 20) (hj : j ∈ groupTokens π r x) :
    (externalSlot j).1 = x

theorem groupTokens_disjoint (π : PatternData) (r : Representation) :
    (reductionGroups π : Set Plane).PairwiseDisjoint (groupTokens π r)

theorem group_pair_distinct (x : Plane) : groupLeader x ≠ groupSecond x

theorem pair_ne_origin (π : PatternData) (r : Representation) (x : Plane)
    (h : groupIsPair π r x = true) : x ≠ (0, 0)

theorem pair_retained (π : PatternData) (r : Representation) (x : reductionGroups π)
    (h : groupIsPair π r x.val = true) : x.val ∈ reducedSpinSites π r

def groupVector (π : PatternData) (r : Representation) (n : Plane → Vec3)
    (x : Plane) : Vec3

def tokenVector (π : PatternData) (r : Representation) (n : Plane → Vec3)
    (j : Fin 20) : Vec3

theorem tokenVector_at_group (π : PatternData) (r : Representation) (n : Plane → Vec3)
    (x : Plane) (hx : x ∈ reductionGroups π) (j : Fin 20)
    (hj : j ∈ groupTokens π r x) : tokenVector π r n j = groupVector π r n x

theorem tokenVector_leader (π : PatternData) (r : Representation) (n : Plane → Vec3)
    (x : reductionGroups π) (h : groupIsPair π r x.val = true) :
    tokenVector π r n (groupLeader x.val) = n x.val

theorem tokenVector_second (π : PatternData) (r : Representation) (n : Plane → Vec3)
    (x : reductionGroups π) (h : groupIsPair π r x.val = true) :
    tokenVector π r n (groupSecond x.val) = n x.val
```

### Realization.lean

```lean
def inversionSign (I : Finset (Fin 20)) (j : Fin 20) : ℝ

theorem inversionSign_sq (I : Finset (Fin 20)) (j : Fin 20) :
    inversionSign I j ^ 2 = 1

def realizationHom (I : Finset (Fin 20)) (n : Plane → Vec3) :
    LocalPolynomial →+* RealPoly

@[simp] theorem realizationHom_C (I : Finset (Fin 20)) (n : Plane → Vec3) (q : ℚ) :
    realizationHom I n (MvPolynomial.C q) = MvPolynomial.C (q : ℝ)

@[simp] theorem realizationHom_internal (I : Finset (Fin 20)) (n : Plane → Vec3)
    (x : Plane) (k : Fin 3) :
    realizationHom I n (MvPolynomial.X (.inl (x, k))) = MvPolynomial.C (n x k)

@[simp] theorem realizationHom_external (I : Finset (Fin 20)) (n : Plane → Vec3)
    (j : Fin 20) (k : Fin 3) :
    realizationHom I n (MvPolynomial.X (.inr (j, k))) =
      MvPolynomial.C (inversionSign I j) * MvPolynomial.X (j, k)

@[simp] theorem realizationHom_dot (I : Finset (Fin 20)) (n : Plane → Vec3)
    (x y : Plane) :
    realizationHom I n (formalDot (fun k => .inl (x, k)) (fun k => .inl (y, k))) =
      MvPolynomial.C (dot (n x) (n y))

theorem realizationHom_slot (I : Finset (Fin 20)) (n : Plane → Vec3)
    (x : Plane) (j : Fin 20) (q : ℚ) :
    realizationHom I n (1 + MvPolynomial.C q *
      formalDot (fun k => .inl (x, k)) (fun k => .inr (j, k))) =
      affineSlot j (inversionSign I j • ((q : ℝ) • n x))

theorem realizationHom_slot_one (I : Finset (Fin 20)) (n : Plane → Vec3)
    (x : Plane) (j : Fin 20) :
    realizationHom I n (1 + formalDot (fun k => .inl (x, k)) (fun k => .inr (j, k))) =
      affineSlot j (inversionSign I j • n x)

def bondScalar (π : PatternData) (r : Representation) (next : Bool)
    (n : Plane → Vec3) : ℝ

theorem realizationHom_integrand (π : PatternData) (r : Representation)
    (next : Bool) (I : Finset (Fin 20)) (n : Plane → Vec3) :
    realizationHom I n (reducedIntegrand π r next) =
      MvPolynomial.C (bondScalar π r next n) *
        ∏ j : reductionVectors π r,
          affineSlot j.val (inversionSign I j.val • tokenVector π r n j.val)

theorem integrand_pauli_tensor (π : PatternData) (r : Representation)
    (next : Bool) (I : Finset (Fin 20)) (n : Plane → Vec3) :
    realPauliOperator (reductionVectors π r)
        (invertRealPolynomial I (specializeInternal (reducedIntegrand π r next) n)) =
      (bondScalar π r next n : ℂ) •
        tensorMatrix (reductionVectors π r)
          (fun j => 1 + blochMatrix (inversionSign I j.val • tokenVector π r n j.val))
```

### Expansion.lean

```lean
theorem blochMatrix_smul (a : ℝ) (n : Vec3) :
    blochMatrix (a • n) = (a : ℂ) • blochMatrix n

def summandMatrices (π : PatternData) (r : Representation) (I : Finset (Fin 20))
    (n : Plane → Vec3) : reductionVectors π r → SmallMatrix

theorem summand_factor_pair (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (hI : GroupInversion π r I)
    (x : reductionGroups π) (h : groupIsPair π r x.val = true) (n : Plane → Vec3) :
    toEnd (tensorMatrix (reductionVectors π r) (summandMatrices π r I n)) =
      pairTerm (reductionVectors π r) (leaderToken π r x) (secondToken π r x h)
        (inversionSign I (groupLeader x.val)) (n x.val) *
      toEnd (remainingTensor (leaderToken π r x) (secondToken π r x h)
        (summandMatrices π r I n))

theorem pairExpansion_of_sum {J : Finset (Fin 20)} (j k : J) (unitOnly : Prop)
    {α : Type*} [Fintype α] (η : ℝ) (hη : η ^ 2 = 1)
    (w : α → ℂ) (n : α → Vec3) (H : α → Module.End ℂ (TensorSpace J))
    (hn : ∀ a, normSq (n a) ≤ 1 ∧ (unitOnly → w a ≠ 0 → normSq (n a) = 1))
    (hH : ∀ a, Commute (H a) (exchangeOperator J j k) ∧
      Commute (H a) (symmetricPairProjection J j k)) :
    PairExpansion J j k (∑ a, w a • (pairTerm J j k η (n a) * H a)) unitOnly

theorem spinVector_norm (hNorm : ∀ j : IcoLetter, normSq (icoVector j) = 1)
    (a : SpinLetter) : normSq (spinVector a) ≤ 1

theorem spinVector_unit_of_weight (hNorm : ∀ j : IcoLetter, normSq (icoVector j) = 1)
    (a : SpinLetter) (h : spinWeight .U a ≠ 0) : normSq (spinVector a) = 1
```

### Raw.lean

```lean
@[simp] theorem toEnd_sub {J : Finset (Fin 20)}
    (A B : Matrix (J → Fin 2) (J → Fin 2) ℂ) :
    toEnd (A - B) = toEnd A - toEnd B

@[simp] theorem toEnd_smul {J : Finset (Fin 20)}
    (z : ℂ) (A : Matrix (J → Fin 2) (J → Fin 2) ℂ) :
    toEnd (z • A) = z • toEnd A

def spinMass (π : PatternData) (r : Representation) (next : Bool)
    (a : reducedSpinSites π r → SpinLetter) : ℝ

def rawWeight (π : PatternData) (r : Representation) (next : Bool)
    (a : reducedSpinSites π r → SpinLetter) : ℝ

def differenceWeight (π : PatternData) (r : Representation) (c : ℚ)
    (a : reducedSpinSites π r → SpinLetter) : ℂ

def rawAuxiliary (π : PatternData) (r : Representation) (I : Finset (Fin 20))
    (x : reductionGroups π) (h : groupIsPair π r x.val = true)
    (a : reducedSpinSites π r → SpinLetter) : Module.End ℂ (TensorSpace (reductionVectors π r))

theorem rawPauli_tensor_sum (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (next : Bool) :
    rawPauliFunctional (reducedSpinSites π r) (nextStatus π next) (reductionVectors π r) I
        (reducedIntegrand π r next) =
      ∑ a : reducedSpinSites π r → SpinLetter,
        (rawWeight π r next a : ℂ) • tensorMatrix (reductionVectors π r)
          (summandMatrices π r I (supportSpins (reducedSpinSites π r) a))

theorem rawEnd_pair_sum (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (hI : GroupInversion π r I)
    (x : reductionGroups π) (h : groupIsPair π r x.val = true) (next : Bool) :
    toEnd (rawPauliFunctional (reducedSpinSites π r) (nextStatus π next) (reductionVectors π r) I
        (reducedIntegrand π r next)) =
      ∑ a : reducedSpinSites π r → SpinLetter,
        (rawWeight π r next a : ℂ) •
          (pairTerm (reductionVectors π r) (leaderToken π r x) (secondToken π r x h)
            (inversionSign I (groupLeader x.val))
            (supportSpins (reducedSpinSites π r) a x.val) * rawAuxiliary π r I x h a)

theorem spinMass_zero_at_U (π : PatternData) (r : Representation)
    (x : reductionGroups π) (h : groupIsPair π r x.val = true)
    (hU : π.statusAt x.val = .U) (next : Bool)
    (a : reducedSpinSites π r → SpinLetter)
    (ha : a ⟨x.val, pair_retained π r x h⟩ = none) : spinMass π r next a = 0

theorem rawDifference_pairExpansion
    (hNorm : ∀ j : IcoLetter, normSq (icoVector j) = 1)
    (π : PatternData) (r : Representation) (I : Finset (Fin 20))
    (hI : GroupInversion π r I) (c : ℚ)
    (x : reductionGroups π) (h : groupIsPair π r x.val = true) :
    PairExpansion (reductionVectors π r) (leaderToken π r x) (secondToken π r x h)
      (toEnd (rawPauliFunctional (reducedSpinSites π r) (nextStatus π false)
          (reductionVectors π r) I (reducedIntegrand π r false) -
        (c : ℂ) • rawPauliFunctional (reducedSpinSites π r) (nextStatus π true)
          (reductionVectors π r) I (reducedIntegrand π r true)))
      (π.statusAt x.val = .U)
```

### Main.lean

```lean
theorem pauliOperator_invert_difference
    (J I : Finset (Fin 20)) (p q : VectorPolynomial) (c : ℚ) :
    pauliOperator J (invertPolynomial I (p - MvPolynomial.C c * q)) =
      pauliOperator J (invertPolynomial I p) -
        (c : ℂ) • pauliOperator J (invertPolynomial I q)

theorem main : AKLT.Blueprint.H1.PairExpansionFromRealizationStatement
```

## Open issues

None. There are no residual propositions, unproved dependencies, or changes to the required theorem type.

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT/W/H1M052/Main.lean` and seven helper/audit files in the same directory.
- Exact declaration: `AKLT.W.H1M052.main : AKLT.Blueprint.H1.PairExpansionFromRealizationStatement`.
- Main builds without warnings; full seven-module rebuild took 48.01 seconds.
- Exact-type check and all 57 theorem axiom checks passed in 5.41 seconds.
- Every exported theorem depends only on `[propext, Classical.choice, Quot.sound]`.
- The earlier Pauli difference-linearity proof was reused; the earlier residual is fully discharged and removed.
- Current and next are combined termwise because their spin configuration types agree.
- Zero-coefficient terms use unit-spin padding instead of deleting their indices.
- No other blueprint leaves, extra premises, forbidden constructs, or frozen-file changes.
- Open names: none. Limitations: none. No orchestrator decision is required.
