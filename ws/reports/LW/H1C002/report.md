STATUS: PROVED FROM DEPS

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C002/AKLT/W/H1C002/Main.lean): the requested closed theorem, with exactly the required name and type.
- [Algebra.lean](/home/ubuntu/aklt/wt/LW_H1C002/AKLT/W/H1C002/Algebra.lean): inversion coefficients, integral entry reconstruction, rational linearity, and the rational/complex entry bridge.
- [Structure.lean](/home/ubuntu/aklt/wt/LW_H1C002/AKLT/W/H1C002/Structure.lean): imaginary cancellation from indexed moment and polynomial-structure leaves.
- [build.log](/home/ubuntu/aklt/reports/LW/H1C002/build.log) and [check.log](/home/ubuntu/aklt/reports/LW/H1C002/check.log): successful validation output.

Both helper modules are imported by Main. No existing files outside the assigned task directory were edited. The earlier report remains in report.luna.md.

## Proof

Inversion multiplies each coefficient by an integer sign. The denominator hypothesis therefore makes the scaled inverted coefficients integral. Rational Pauli components and their folded complex products are integral; distributing the finite sums proves that each scaled rational sector entry is integral. Thus the floor defining integerSectorMatrix is exact.

The rational complex fold represents the ordinary complex product, so rationalOperatorEntry is exactly the real part of pauliOperator. Indexed moment, reduced-structure, inversion, reflection-parity, and Pauli-reality lemmas prove the imaginary part is zero for the inverted difference. This gives exact complex-sector reconstruction.

Distribute current minus c times next through inversion and sector entries. Then 5q times the 3D₀ current entry minus 3p times the 5D₀ next entry is exactly 15D₀q times the difference at c = p/q. The positive denominator q justifies clearing this division. No residual assumption remains.

## Exported declarations and statements

All names below belong to AKLT.W.H1C002. In these signatures, `Poly` abbreviates `MvPolynomial (Fin 20 × Fin 3) ℚ`, and the definitions from AKLT.Defs are open. Each displayed signature is copied from the delivered source, without its proof body.

### `AKLT.W.H1C002.main`

```lean
theorem main : AKLT.Cert.H1.Production.TopLeaves.thresholdScale
```

### `AKLT.W.H1C002.coeff_invertPolynomial`

```lean
theorem coeff_invertPolynomial (I : Finset (Fin 20)) (p : Poly)
    (d : (Fin 20 × Fin 3) →₀ ℕ) :
    (invertPolynomial I p).coeff d = p.coeff d *
      ∏ v ∈ d.support, (if v.1 ∈ I then (-1 : ℚ) else 1) ^ d v
```

### `AKLT.W.H1C002.sector_integral`

```lean
theorem sector_integral (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (p : Poly) (k : ℚ) (hk : ∀ d, ∃ z : ℤ, k * p.coeff d = z)
    (a b : CentralBasis π r ε) :
    ∃ z : ℤ, k * rationalSectorEntry π r ε p a b = z
```

### `AKLT.W.H1C002.integerSectorMatrix_exact`

```lean
theorem integerSectorMatrix_exact (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (D₀ : ℕ) (hD : ClearsDenominator π r D₀)
    (ε : ExchangeSigns π) (next : Bool) (a b : CentralBasis π r ε) :
    (integerSectorMatrix π r ε I D₀ next a b : ℚ) =
      (if next then 5 else 3) * (D₀ : ℚ) * rationalSectorEntry π r ε
        (invertPolynomial I (reducedPolynomial π r next)) a b
```

### `AKLT.W.H1C002.rationalSectorEntry_sub`

```lean
theorem rationalSectorEntry_sub (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (p q : Poly) (a b : CentralBasis π r ε) :
    rationalSectorEntry π r ε (p - q) a b =
      rationalSectorEntry π r ε p a b - rationalSectorEntry π r ε q a b
```

### `AKLT.W.H1C002.rationalSectorEntry_C_mul`

```lean
theorem rationalSectorEntry_C_mul (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (p : Poly) (k : ℚ) (a b : CentralBasis π r ε) :
    rationalSectorEntry π r ε (MvPolynomial.C k * p) a b =
      k * rationalSectorEntry π r ε p a b
```

### `AKLT.W.H1C002.rationalSectorEntry_difference`

```lean
theorem rationalSectorEntry_difference (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (ε : ExchangeSigns π) (c : ℚ)
    (a b : CentralBasis π r ε) :
    rationalSectorEntry π r ε (invertPolynomial I (reducedDifference π r c)) a b =
      rationalSectorEntry π r ε (invertPolynomial I (reducedPolynomial π r false)) a b -
        c * rationalSectorEntry π r ε (invertPolynomial I (reducedPolynomial π r true)) a b
```

### `AKLT.W.H1C002.rationalOperatorEntry_real`

```lean
theorem rationalOperatorEntry_real (J : Finset (Fin 20)) (p : Poly)
    (σ τ : J → Fin 2) :
    (rationalOperatorEntry J p σ τ : ℝ) = (pauliOperator J p σ τ).re
```

### `AKLT.W.H1C002.complexSectorMatrix_exact`

```lean
theorem complexSectorMatrix_exact (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (p : Poly)
    (hreal : ∀ σ τ, (pauliOperator (reductionVectors π r) p σ τ).im = 0)
    (a b : CentralBasis π r ε) :
    complexSectorMatrix π r ε p a b = (rationalSectorEntry π r ε p a b : ℂ)
```

### `AKLT.W.H1C002.invertedDifference_real`

```lean
theorem invertedDifference_real (π : PatternData) (hπ : π.Covered) (r : Representation)
    (I : Finset (Fin 20)) (c : ℚ) :
    ∀ σ τ, (pauliOperator (reductionVectors π r)
      (invertPolynomial I (reducedDifference π r c)) σ τ).im = 0
```

## Indexed dependencies

Every imported leaf module was checked against `/home/ubuntu/aklt/state/lw/proved-index.tsv`. All twenty imports appear there. Only proved leaves and existing proved assembly implications are used.

```text
statement	theorem	module
AKLT.Blueprint.Mom.IcoInjectivityStatement	AKLT.W.MOM001.main	AKLT.W.MOM001.Main
AKLT.Blueprint.Mom.IcoUnitStatement	AKLT.W.MOM002.main	AKLT.W.MOM002.Main
AKLT.Blueprint.Mom.OddMonomialStatement	AKLT.W.MOM003.main	AKLT.W.MOM003.Main
AKLT.Blueprint.Mom.SecondScalarMomentStatement	AKLT.W.MOM004.main	AKLT.W.MOM004.Main
AKLT.Blueprint.Mom.FourthScalarMomentStatement	AKLT.W.MOM005.main	AKLT.W.MOM005.Main
AKLT.Blueprint.Mom.MixedScalarMomentStatement	AKLT.W.MOM006.main	AKLT.W.MOM006.Main
AKLT.Blueprint.Mom.ScalarTensorReconstructionStatement	AKLT.W.MOM007.main	AKLT.W.MOM007.Main
AKLT.Blueprint.Mom.TensorMonomialStatement	AKLT.W.MOM008.main	AKLT.W.MOM008.Main
AKLT.Blueprint.Mom.OrthogonalTensorStatement	AKLT.W.MOM009.main	AKLT.W.MOM009.Main
AKLT.Blueprint.Mom.PolynomialExpansionStatement	AKLT.W.MOM010.main	AKLT.W.MOM010.Main
AKLT.Blueprint.H1.MomentCovarianceTransferStatement	AKLT.W.H1M013.main	AKLT.W.H1M013.Main
AKLT.Blueprint.H1.ContractionAffineStatement	AKLT.W.H1M014.main	AKLT.W.H1M014.Main
AKLT.Blueprint.H1.ContractionSupportStatement	AKLT.W.H1M015.main	AKLT.W.H1M015.Main
AKLT.Blueprint.H1.InversionPolynomialStatement	AKLT.W.H1M020.main	AKLT.W.H1M020.Main
AKLT.Blueprint.H1.ReducedDegreeStatement	AKLT.W.H1M023.main	AKLT.W.H1M023.Main
AKLT.Blueprint.H1.ReducedFactorStructureStatement	AKLT.W.H1M024.main	AKLT.W.H1M024.Main
AKLT.Blueprint.H1.DifferenceStructureStatement	AKLT.W.H1M031.main	AKLT.W.H1M031.Main
AKLT.Blueprint.H1.ReflectionParityStatement	AKLT.W.H1M042.main	AKLT.W.H1M042.Main
AKLT.Blueprint.H1.PauliRealityStatement	AKLT.W.H1M043.main	AKLT.W.H1M043.Main
AKLT.Blueprint.H1.InversionCovarianceStatement	AKLT.W.H1M044.main	AKLT.W.H1M044.Main
```

## Axiom audit

The separate import check ran `#print axioms` on every exported theorem:

```text
'AKLT.W.H1C002.coeff_invertPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C002.sector_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C002.integerSectorMatrix_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C002.rationalSectorEntry_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C002.rationalSectorEntry_C_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C002.rationalSectorEntry_difference' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C002.rationalOperatorEntry_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C002.complexSectorMatrix_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C002.invertedDifference_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C002.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only propext, Classical.choice, and Quot.sound occur.

## Build and exact-type check

- `/usr/bin/time -f 'ELAPSED %e s' lake build AKLT.W.H1C002.Main` — succeeded, 62.19 seconds. New Algebra and Main modules built; dependencies were cached. Structure had already compiled successfully.
- `/usr/bin/time -f 'ELAPSED %e s' lake env lean /tmp/h1c002-Check.lean` — succeeded, 13.38 seconds. This imported the built Main module, checked the exact type, and audited all ten exported theorems.

The exact-type check included:

```lean
import AKLT.W.H1C002.Main

#check (AKLT.W.H1C002.main : AKLT.Cert.H1.Production.TopLeaves.thresholdScale)
example : AKLT.Cert.H1.Production.TopLeaves.thresholdScale := AKLT.W.H1C002.main
```

The output confirmed:

```text
AKLT.W.H1C002.main : AKLT.Cert.H1.Production.TopLeaves.thresholdScale
```

The delivered source contains no prohibited proof construction or heartbeat override. Proofs use symbolic sums, lists, and named finite-product identities; no concrete sector or polynomial enumeration is evaluated by definitional equality. Replayed warnings in the build log come from existing dependency modules.

## Open issues

None for this leaf. Validation here used Lean's kernel; the campaign's later independent-kernel recheck remains external.

## ORCH-SUMMARY

- Delivered AKLT.W.H1C002.main : AKLT.Cert.H1.Production.TopLeaves.thresholdScale.
- STATUS: PROVED FROM DEPS; all twenty leaf imports are present in the supplied proved index.
- Exact flooring, inversion signs, rational linearity, and rational/complex reconstruction are proved in Algebra.lean.
- Imaginary cancellation is proved in Structure.lean using the indexed structural leaves.
- The scale is exactly 15 * D₀ * q.
- No residual statements or additional hypotheses remain.
- All three source files are imported transitively by Main.
- Build succeeded in 62.19 s; separate exact-type/axiom check succeeded in 13.38 s.
- Every exported theorem uses only propext, Classical.choice, and Quot.sound.
- No changes outside the assigned source/report directories; no sub-agents used.
- Limitation: independent-kernel checks are performed by the campaign, not in this session.
- Open names: none. Orchestrator can register this leaf as proved.
