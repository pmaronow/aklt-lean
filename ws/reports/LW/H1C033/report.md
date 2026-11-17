STATUS: PROVED FROM DEPS

The exact requested theorem is proved, with no residual propositions or additional hypotheses:

```lean
theorem AKLT.W.H1C033.main :
    AKLT.Cert.H1.Production.Leaves.mirrorDataWitness
```

## Files

- [Geometry.lean](/home/ubuntu/aklt/wt/LW_H1C033/AKLT/W/H1C033/Geometry.lean)
- [Polynomial.lean](/home/ubuntu/aklt/wt/LW_H1C033/AKLT/W/H1C033/Polynomial.lean)
- [Basis.lean](/home/ubuntu/aklt/wt/LW_H1C033/AKLT/W/H1C033/Basis.lean)
- [Operators.lean](/home/ubuntu/aklt/wt/LW_H1C033/AKLT/W/H1C033/Operators.lean)
- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C033/AKLT/W/H1C033/Main.lean)
- [Build and axiom-audit log](/home/ubuntu/aklt/reports/LW/H1C033/build.log)

`Main.lean` transitively imports every source file in the task directory. No existing source file outside this directory was changed. The previous partial implementation has been replaced; `report.luna.md` remains as historical context.

## Proof and dependency

The proof constructs involutions of sites, positively oriented bonds, and the twenty vector tokens. The token map sends group leaders to reflected leaders and retained second tokens to reflected second tokens. It transports the group inversion set and the exact denominator. Isolated retained spins are removed from the contraction using a proved zero-exponent lemma, so their unrecorded statuses cause no gap.

The proof then transports the reduced integrand, moment contraction, Pauli exponents, rational operator entries, and unnormalized exchange-basis coefficients. The resulting equivalence preserves magnetic weight and the central weight. A permutation lemma for the fold of rational complex multiplication handles the order of tensor factors in `rationalOperatorEntry`.

For a source witness with `index : Fin t ≃ CentralBasis ...`, the target index is `index.trans (centralEquiv ...)`. The indexed threshold matrix is proved equal entry by entry. The same `g`, `d`, `S`, and `L` are reused. Consequently the lower-triangular condition and every Gram residual row condition are inherited directly, without a row permutation of `L`.

The permitted proved-leaf dependency is:

- Statement: `AKLT.Blueprint.H1.ReducedDegreeStatement`.
- Indexed theorem/module: `AKLT.W.H1M023.main` / `AKLT.W.H1M023.Main`.
- Reused proved helpers from its imports: `AKLT.W.H1M023.leaf_bond`, `group_single`, `bonds_and_singles_le`, and `reducedIntegrand_degreeBudget`.

No unproved blueprint leaf is used. Both coveredness hypotheses of the requested statement are retained in its exact type; the transport lemmas in fact need only `MirrorEffectiveData`.

## Build and exact-type check

Final command, from `/home/ubuntu/aklt/wt/LW_H1C033`:

```sh
PATH="$HOME/.elan/bin:$PATH" /usr/bin/time -p lake build AKLT.W.H1C033.Main
```

Result: success. Wall time **18.31 seconds** (`user 16.88`, `sys 4.88`); Lake reported `Main` built in **5.7 seconds**. All imported helper modules were built successfully. There were only non-failing style/linter warnings.

`Main.lean` also checks the exact required type:

```lean
#check (AKLT.W.H1C033.main : AKLT.Cert.H1.Production.Leaves.mirrorDataWitness)
```

Lean output: `main : Leaves.mirrorDataWitness`.

The delivered sources contain no forbidden proof mechanism. No increased heartbeat limit is used. Index and basis transports use explicit equivalences and named congruence lemmas; no large concrete certificate, enumeration, or matrix is reduced to establish the final equality. The independent campaign kernels have not been run here.

## Exported declarations and statements

All names below are in namespace `AKLT.W.H1C033`. The following signatures are copied from the delivered sources; definitions are listed by type, and theorem proof terms are omitted.

### Geometry.lean

```lean
abbrev flip (x : Plane) : Plane

@[simp] theorem flip_flip (x : Plane) : flip (flip x) = x

@[simp] theorem flip_zero : flip (0,0) = (0,0)

def pointEquiv : Plane ≃ Plane

@[simp] theorem flip_inj {x y : Plane} : flip x = flip y ↔ x = y

@[simp] theorem flip_tips (x : Plane) : flip x ∈ templateTips ↔ x ∈ templateTips

@[simp] theorem flip_corners (x : Plane) : flip x ∈ templateCorners ↔ x ∈ templateCorners

@[simp] theorem flip_sites (x : Plane) : flip x ∈ templateSites ↔ x ∈ templateSites

def flipEdge (e : Plane × Plane) : Plane × Plane

@[simp] theorem flipEdge_flipEdge (e : Plane × Plane) : flipEdge (flipEdge e) = e

def edgeEquiv : (Plane × Plane) ≃ (Plane × Plane)

@[simp] theorem flipEdge_incident (e : Plane × Plane) (x : Plane) :
    ((flipEdge e).1 = flip x ∨ (flipEdge e).2 = flip x) ↔ (e.1 = x ∨ e.2 = x)

@[simp] theorem flipEdge_internal (e : Plane × Plane) :
    flipEdge e ∈ internalBonds templateSites ↔ e ∈ internalBonds templateSites

theorem internal_not_reverse {a b : Plane} (h : (a,b) ∈ internalBonds templateSites) :
    (b,a) ∉ internalBonds templateSites

theorem mem_bonds_iff (π : PatternData) (a b : Plane) :
    (a,b) ∈ π.bonds ↔ (a,b) ∈ internalBonds templateSites ∧ presentBond π a b = true

theorem mirror_edge (π ρ : PatternData) (h : MirrorEffectiveData π ρ) (e : Plane × Plane) :
    e ∈ π.bonds ↔ flipEdge e ∈ ρ.bonds

theorem mirror_degree (π ρ : PatternData) (h : MirrorEffectiveData π ρ) (x : Plane) :
    patternDegree π x = patternDegree ρ (flip x)

theorem mirror_groups (π ρ : PatternData) (h : MirrorEffectiveData π ρ) (x : Plane) :
    flip x ∈ reductionGroups ρ ↔ x ∈ reductionGroups π

theorem mirror_single (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (x : Plane) :
    SingleReplacement π r x ↔ SingleReplacement ρ r (flip x)

theorem mirror_pair (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (x : Plane) : groupIsPair π r x = groupIsPair ρ r (flip x)

theorem mirror_symm (π ρ : PatternData) (h : MirrorEffectiveData π ρ) :
    MirrorEffectiveData ρ π

theorem mirror_h1Numerator_eq (π ρ : PatternData)
    (h : MirrorEffectiveData π ρ) : h1Numerator π = h1Numerator ρ

theorem mirror_h1Denominator_eq (π ρ : PatternData)
    (h : MirrorEffectiveData π ρ) : h1Denominator π = h1Denominator ρ

def flipToken (j : Fin 20) : Fin 20

@[simp] theorem flipToken_flipToken (j : Fin 20) : flipToken (flipToken j) = j

def tokenEquiv : Fin 20 ≃ Fin 20

theorem flip_leader (x : Plane) (hx : x ∈ templateCorners ∪ templateTips) :
    flipToken (groupLeader x) = groupLeader (flip x)

theorem flip_second (x : Plane) (hx : x ∈ templateCorners) :
    flipToken (groupSecond x) = groupSecond (flip x)

theorem mirror_vectors (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (j : Fin 20) :
    flipToken j ∈ reductionVectors ρ r ↔ j ∈ reductionVectors π r

theorem mirror_inversion (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (I : Finset (Fin 20)) (hI : GroupInversion ρ r I) :
    GroupInversion π r (I.image flipToken)

theorem mirror_neighbour (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (x : Plane) (hx : patternDegree π x = 1) :
    leafNeighbour ρ (flip x) = flip (leafNeighbour π x)

theorem isolated_exponent (π : PatternData) (r : Representation) (next : Bool)
    (m : LocalVariable →₀ ℕ) (hm : m ∈ (reducedIntegrand π r next).support)
    (x : Plane) (hx : patternDegree π x = 0) (k : Fin 3) : m (.inl (x,k)) = 0

def bondedSpins (π : PatternData) (r : Representation) : Finset Plane

theorem mirror_bondedSpins (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (x : Plane) :
    flip x ∈ bondedSpins ρ r ↔ x ∈ bondedSpins π r

theorem trim_contract (π : PatternData) (r : Representation) (next : Bool) :
    reducedPolynomial π r next = contractSpins (bondedSpins π r)
      (fun x => if next ∧ x = (0,0) then .D else π.statusAt x) (reducedIntegrand π r next)
```

### Polynomial.lean

```lean
@[simp] theorem pointEquiv_apply (x : Plane) : pointEquiv x = flip x

@[simp] theorem tokenEquiv_apply (j : Fin 20) : tokenEquiv j = flipToken j

abbrev vectorEquiv : (Fin 20 × Fin 3) ≃ (Fin 20 × Fin 3)

abbrev localEquiv : LocalVariable ≃ LocalVariable

@[simp] theorem vectorEquiv_apply (j : Fin 20) (k : Fin 3) :
    vectorEquiv (j,k) = (flipToken j,k)

@[simp] theorem localEquiv_inl (x : Plane) (k : Fin 3) :
    localEquiv (.inl (x,k)) = .inl (flip x,k)

@[simp] theorem localEquiv_inr (j : Fin 20) (k : Fin 3) :
    localEquiv (.inr (j,k)) = .inr (flipToken j,k)

theorem rename_formalDot {σ τ : Type*} (f : σ → τ) (a b : Fin 3 → σ) :
    MvPolynomial.rename f (formalDot a b) = formalDot (f ∘ a) (f ∘ b)

theorem formalDot_comm {σ : Type*} (a b : Fin 3 → σ) :
    formalDot a b = formalDot b a

theorem positive_of_incident (π : PatternData) {e : Plane × Plane}
    (he : e ∈ π.bonds) : 0 < patternDegree π e.1 ∧ 0 < patternDegree π e.2

theorem mirror_retained (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (x : Plane) (hx : 0 < patternDegree π x) :
    flip x ∈ reducedSpinSites ρ r ↔ x ∈ reducedSpinSites π r

theorem flip_pair_eq (a b c d : Plane) :
    ({flip a,flip b} : Finset Plane) = {flip c,flip d} ↔
      ({a,b} : Finset Plane) = {c,d}

theorem mirror_out_edge (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (e : Plane × Plane) :
    ({(flipEdge e).1,(flipEdge e).2} : Finset Plane) = {(0,0),ρ.outgoing.step} ↔
      ({e.1,e.2} : Finset Plane) = {(0,0),π.outgoing.step}

theorem mirror_integrand (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (next : Bool) :
    MvPolynomial.rename localEquiv (reducedIntegrand π r next) = reducedIntegrand ρ r next

theorem externalExponent_rename (m : LocalVariable →₀ ℕ) :
    Finsupp.comapDomain Sum.inr (m.mapDomain localEquiv) (by
      intro a _ b _ hab; exact Sum.inr.inj hab) =
    (Finsupp.comapDomain Sum.inr m (by
      intro a _ b _ hab; exact Sum.inr.inj hab)).mapDomain vectorEquiv

theorem contract_rename (V W : Finset Plane) (s t : Plane → Status)
    (hV : ∀ x, x ∈ V ↔ flip x ∈ W) (hs : ∀ x ∈ V, s x = t (flip x))
    (p : MvPolynomial LocalVariable ℚ) :
    contractSpins W t (MvPolynomial.rename localEquiv p) =
      MvPolynomial.rename vectorEquiv (contractSpins V s p)

theorem mirror_polynomial (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (next : Bool) :
    MvPolynomial.rename vectorEquiv (reducedPolynomial π r next) = reducedPolynomial ρ r next

theorem mirror_denominator (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (D : ℕ) (hD : ClearsDenominator π r D) :
    ClearsDenominator ρ r D

theorem invert_rename (I : Finset (Fin 20)) (p : MvPolynomial (Fin 20 × Fin 3) ℚ) :
    invertPolynomial (I.image flipToken) (MvPolynomial.rename vectorEquiv p) =
      MvPolynomial.rename vectorEquiv (invertPolynomial I p)
```

### Basis.lean

```lean
def groupEquiv (π ρ : PatternData) (h : MirrorEffectiveData π ρ) :
    reductionGroups π ≃ reductionGroups ρ

@[simp] theorem groupEquiv_val (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (x : reductionGroups π) : (groupEquiv π ρ h x).val = flip x.val

def vectorIndexEquiv (π ρ : PatternData) (h : MirrorEffectiveData π ρ) (r : Representation) :
    reductionVectors π r ≃ reductionVectors ρ r

@[simp] theorem vectorIndexEquiv_val (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (x : reductionVectors π r) :
    (vectorIndexEquiv π ρ h r x).val = flipToken x.val

def mirroredSigns (π ρ : PatternData) (h : MirrorEffectiveData π ρ) (ε : ExchangeSigns π) :
    ExchangeSigns ρ

@[simp] theorem mirroredSigns_apply (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (ε : ExchangeSigns π) (x : reductionGroups π) :
    mirroredSigns π ρ h ε (groupEquiv π ρ h x) = ε x

theorem group_status (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (x : reductionGroups π) : π.statusAt x.val = ρ.statusAt (groupEquiv π ρ h x).val

abbrev basisSize (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (x : reductionGroups π) : ℕ

theorem mirror_basisSize (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (x : reductionGroups π) :
    basisSize π r ε x = basisSize ρ r (mirroredSigns π ρ h ε) (groupEquiv π ρ h x)

def groupBasisEquiv (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (x : reductionGroups π) :
    GroupBasis π r ε x ≃ GroupBasis ρ r (mirroredSigns π ρ h ε) (groupEquiv π ρ h x)

@[simp] theorem groupBasisEquiv_val (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (x : reductionGroups π)
    (b : GroupBasis π r ε x) : (groupBasisEquiv π ρ h r ε x b).val = b.val

def exchangeEquiv (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) :
    ExchangeBasis π r ε ≃ ExchangeBasis ρ r (mirroredSigns π ρ h ε)

@[simp] theorem exchangeEquiv_val (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (b : ExchangeBasis π r ε)
    (x : reductionGroups π) :
    ((exchangeEquiv π ρ h r ε b) (groupEquiv π ρ h x)).val = (b x).val

theorem mirror_weight (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (b : ExchangeBasis π r ε) :
    exchangeWeight ρ r (mirroredSigns π ρ h ε) (exchangeEquiv π ρ h r ε b) =
      exchangeWeight π r ε b

theorem mirror_centralWeight (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) : centralWeight π r = centralWeight ρ r

def centralEquiv (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) :
    CentralBasis π r ε ≃ CentralBasis ρ r (mirroredSigns π ρ h ε)

@[simp] theorem centralEquiv_val (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (b : CentralBasis π r ε) :
    (centralEquiv π ρ h r ε b).val = exchangeEquiv π ρ h r ε b.val

def pushEquiv {α β γ : Type*} (e : α ≃ β) : (α → γ) ≃ (β → γ)

@[simp] theorem pushEquiv_apply {α β γ : Type*} (e : α ≃ β) (f : α → γ) (x : α) :
    pushEquiv e f (e x) = f x

theorem vectorIndexEquiv_leader (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (x : reductionGroups π) :
    vectorIndexEquiv π ρ h r (leaderToken π r x) = leaderToken ρ r (groupEquiv π ρ h x)

theorem vectorIndexEquiv_second (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (x : reductionGroups π) (hp : groupIsPair π r x.val = true) :
    vectorIndexEquiv π ρ h r (secondToken π r x hp) =
      secondToken ρ r (groupEquiv π ρ h x) ((mirror_pair π ρ h r x.val).symm.trans hp)

theorem mirror_basisVector (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (b : ExchangeBasis π r ε)
    (σ : reductionVectors π r → Fin 2) :
    exchangeBasisVector ρ r (mirroredSigns π ρ h ε) (exchangeEquiv π ρ h r ε b)
      (pushEquiv (vectorIndexEquiv π ρ h r) σ) = exchangeBasisVector π r ε b σ
```

### Operators.lean

```lean
theorem ratComplex_rightComm (a b c : ℚ × ℚ) :
    ratComplexMul (ratComplexMul a b) c = ratComplexMul (ratComplexMul a c) b

theorem foldRat_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℚ × ℚ) :
    (((Finset.univ : Finset β).toList.map f).foldl ratComplexMul (1,0)) =
      (((Finset.univ : Finset α).toList.map (fun x => f (e x))).foldl ratComplexMul (1,0))

theorem mirror_pauliExponent (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (a : reductionVectors π r → Fin 4) :
    pauliExponent (reductionVectors ρ r) (pushEquiv (vectorIndexEquiv π ρ h r) a) =
      (pauliExponent (reductionVectors π r) a).mapDomain vectorEquiv

theorem mirror_operatorEntry (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (p : MvPolynomial (Fin 20 × Fin 3) ℚ)
    (σ τ : reductionVectors π r → Fin 2) :
    rationalOperatorEntry (reductionVectors ρ r) (MvPolynomial.rename vectorEquiv p)
      (pushEquiv (vectorIndexEquiv π ρ h r) σ) (pushEquiv (vectorIndexEquiv π ρ h r) τ) =
      rationalOperatorEntry (reductionVectors π r) p σ τ

theorem mirror_sectorEntry (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π)
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ) (a b : CentralBasis π r ε) :
    rationalSectorEntry ρ r (mirroredSigns π ρ h ε) (MvPolynomial.rename vectorEquiv p)
      (centralEquiv π ρ h r ε a) (centralEquiv π ρ h r ε b) =
      rationalSectorEntry π r ε p a b

theorem mirror_integerMatrix (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (I : Finset (Fin 20)) (D : ℕ)
    (next : Bool) (a b : CentralBasis π r ε) :
    integerSectorMatrix ρ r (mirroredSigns π ρ h ε) (I.image flipToken) D next
      (centralEquiv π ρ h r ε a) (centralEquiv π ρ h r ε b) =
      integerSectorMatrix π r ε I D next a b

theorem mirror_thresholdMatrix (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (I : Finset (Fin 20)) (D p q : ℕ)
    (a b : CentralBasis π r ε) :
    thresholdSectorMatrix ρ r (mirroredSigns π ρ h ε) (I.image flipToken) D p q
      (centralEquiv π ρ h r ε a) (centralEquiv π ρ h r ε b) =
      thresholdSectorMatrix π r ε I D p q a b
```

### Main.lean

```lean
theorem mirror_sectorWitnesses (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (I : Finset (Fin 20)) (D p q : ℕ)
    (hw : H1SectorWitnesses π r I D p q) :
    H1SectorWitnesses ρ r (I.image flipToken) D p q

theorem main : AKLT.Cert.H1.Production.Leaves.mirrorDataWitness
```

## `#print axioms` output

The final build checks every exported theorem (68 declarations):

```text
'AKLT.W.H1C033.flip_flip' depends on axioms: [propext]
'AKLT.W.H1C033.flip_zero' depends on axioms: [propext]
'AKLT.W.H1C033.flip_inj' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C033.flip_tips' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.flip_corners' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.flip_sites' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.flipEdge_flipEdge' depends on axioms: [propext]
'AKLT.W.H1C033.flipEdge_incident' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C033.flipEdge_internal' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.internal_not_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mem_bonds_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_degree' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_groups' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_h1Numerator_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_h1Denominator_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.flipToken_flipToken' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.flip_leader' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.flip_second' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_vectors' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_inversion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_neighbour' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.isolated_exponent' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_bondedSpins' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.trim_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.pointEquiv_apply' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C033.tokenEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.vectorEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.localEquiv_inl' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.localEquiv_inr' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.rename_formalDot' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.formalDot_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.positive_of_incident' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.flip_pair_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_out_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_integrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.externalExponent_rename' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.contract_rename' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_denominator' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.invert_rename' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.groupEquiv_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.vectorIndexEquiv_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirroredSigns_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.group_status' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_basisSize' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.groupBasisEquiv_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.exchangeEquiv_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_centralWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.centralEquiv_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.pushEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.vectorIndexEquiv_leader' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.vectorIndexEquiv_second' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_basisVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.ratComplex_rightComm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.foldRat_reindex' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_pauliExponent' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_operatorEntry' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_sectorEntry' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_integerMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_thresholdMatrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.mirror_sectorWitnesses' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C033.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three permitted axioms occur; no residual statement or user axiom occurs in `main` or its helpers.

## Open issues

None in the proof. The independent con-ron/NanoDa checks remain for the campaign runner.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C033/Main.lean` and four transitively imported helper files.
- Exact theorem: `AKLT.W.H1C033.main : AKLT.Cert.H1.Production.Leaves.mirrorDataWitness`.
- Complete proof; no residual propositions and no extra theorem assumptions.
- Reuses approved H1M023 geometry/degree helpers from `AKLT.W.H1M023.Main`.
- The reflected witness preserves its original `Fin t` ordering and reuses the same triangular `L`.
- Isolated-site status differences are discharged explicitly by zero exponents and unit constant moments.
- Final requested build and exact-type check succeeded; 18.31 s wall time.
- Axiom audit of all 68 exported theorems uses only propext, Classical.choice, Quot.sound.
- No source outside `AKLT/W/H1C033/` was changed.
- Limitation: independent campaign kernels were not run in this session.
- Orchestrator: run the standard independent checks and register the proved leaf.
