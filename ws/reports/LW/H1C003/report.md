STATUS: PROVED FROM DEPS

## Delivery

The exact requested closed theorem is proved:

```lean
theorem AKLT.W.H1C003.main : AKLT.Cert.H1.Production.TopLeaves.positiveScale
```

The proof also establishes `AKLT.W.H1C003.thresholdScale_proof : AKLT.Cert.H1.Production.TopLeaves.thresholdScale` without residual hypotheses. The earlier `Residual_thresholdScale` and `main_of_residual` have been removed.

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C003/AKLT/W/H1C003/Main.lean): positive scalar transfer and the requested `main`.
- [Algebra.lean](/home/ubuntu/aklt/wt/LW_H1C003/AKLT/W/H1C003/Algebra.lean): diagonal polynomial substitutions and denominator clearing after inversion.
- [Reflection.lean](/home/ubuntu/aklt/wt/LW_H1C003/AKLT/W/H1C003/Reflection.lean): reflection through moment contraction, vanishing odd-Y coefficients, and real Pauli entries.
- [Pauli.lean](/home/ubuntu/aklt/wt/LW_H1C003/AKLT/W/H1C003/Pauli.lean): rational/complex reconstruction, integrality, and exact removal of the integer floor.
- [Scaling.lean](/home/ubuntu/aklt/wt/LW_H1C003/AKLT/W/H1C003/Scaling.lean): entrywise threshold identity at scale `15 * D₀ * q`.
- [Check.lean](/home/ubuntu/aklt/reports/LW/H1C003/Check.lean): separate exact-type check and checks of every public declaration and exported theorem's axioms.
- [check.log](/home/ubuntu/aklt/reports/LW/H1C003/check.log): complete successful audit output.

Every Lean source file in `AKLT/W/H1C003/` is transitively imported by `Main.lean`. No project source outside that directory was changed. The earlier report remains in `report.luna.md`.

## Proof and dependencies

The denominator hypothesis makes every scaled inverted coefficient integral. Rational complex multiplication and integer basis congruence preserve integrality, so the floor defining `integerSectorMatrix` equals its input exactly. Simultaneous reflection of the second coordinate fixes the reduced integrand; nonzero internal moments have even second-coordinate exponent, so contraction preserves this reflection. Inversion commutes with reflection. Odd-Y coefficients therefore vanish and the reconstructed complex entries are real. Linearity then gives the exact threshold scaling identity.

The final transfer extracts `0 < D₀` from `ClearsDenominator` and uses the explicit hypothesis `0 < q` to prove positivity of the complex scalar through its natural-number cast in `ComplexOrder`. Scaling by this scalar and by its positive inverse proves both directions, including empty sectors.

The following two previously proved leaves are imported and used, both present in the supplied proved index:

- `AKLT.W.H1M023.main : AKLT.Blueprint.H1.ReducedDegreeStatement`, module `AKLT.W.H1M023.Main`; only its assertion that internal variables outside `reducedSpinSites` have zero exponent is used.
- `AKLT.W.H1M043.main : AKLT.Blueprint.H1.PauliRealityStatement`, module `AKLT.W.H1M043.Main`; it turns vanishing odd-Y coefficients into real Pauli entries.

No unproved blueprint leaf is assumed. In particular, `thresholdScale` is proved locally rather than supplied as an unresolved input.

## Validation

From `/home/ubuntu/aklt/wt/LW_H1C003`, with `PATH="$HOME/.elan/bin:$PATH"`:

```text
/usr/bin/time -f 'ELAPSED_SECONDS=%e' lake build AKLT.W.H1C003.Main
Build completed successfully (8979 jobs).
ELAPSED_SECONDS=16.56
```

Lake reported 5.9 seconds for `Scaling` and 5.3 seconds for `Main` in this final build. All helper modules compiled successfully. Remaining warnings came from existing dependencies, not the delivered files.

```text
/usr/bin/time -f 'ELAPSED_SECONDS=%e' lake env lean /home/ubuntu/aklt/reports/LW/H1C003/Check.lean
Exit status: 0
ELAPSED_SECONDS=6.46
```

`Check.lean` includes the exact-type check:

```lean
example : AKLT.Cert.H1.Production.TopLeaves.positiveScale := AKLT.W.H1C003.main
```

The source scan found no forbidden declarations or tactics. All 24 exported theorems were checked with `#print axioms`; only permitted axioms occur. The four auxiliary definitions are transparent: `scaleVariables` is a diagonal evaluation homomorphism, `monomialScale` is the product of variable scales to their exponents, `inversionSign` is the tokenwise ±1 sign, and `IntegralRat x` is `∃ z : ℤ, x = z`.

## Exported declarations and axiom output

The following is the successful `#check` and `#print axioms` output for all 28 public declarations. Cast target types, where elided by Lean's printer, are explicit in the source signatures.

```text
AKLT.W.H1C003.scaleVariables.{u_1} {σ : Type u_1} (s : σ → ℚ) : MvPolynomial σ ℚ →+* MvPolynomial σ ℚ
AKLT.W.H1C003.monomialScale.{u_1} {σ : Type u_1} (s : σ → ℚ) (d : σ →₀ ℕ) : ℚ
AKLT.W.H1C003.scaleVariables_C.{u_1} {σ : Type u_1} (s : σ → ℚ) (c : ℚ) :
  (AKLT.W.H1C003.scaleVariables s) (MvPolynomial.C c) = MvPolynomial.C c
'AKLT.W.H1C003.scaleVariables_C' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.scaleVariables_X.{u_1} {σ : Type u_1} (s : σ → ℚ) (v : σ) :
  (AKLT.W.H1C003.scaleVariables s) (MvPolynomial.X v) = MvPolynomial.C (s v) * MvPolynomial.X v
'AKLT.W.H1C003.scaleVariables_X' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.scaleVariables_monomial.{u_1} {σ : Type u_1} (s : σ → ℚ) (d : σ →₀ ℕ) (c : ℚ) :
  (AKLT.W.H1C003.scaleVariables s) ((MvPolynomial.monomial d) c) =
    (MvPolynomial.monomial d) (c * AKLT.W.H1C003.monomialScale s d)
'AKLT.W.H1C003.scaleVariables_monomial' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.coeff_scaleVariables.{u_1} {σ : Type u_1} (s : σ → ℚ) (p : MvPolynomial σ ℚ) (d : σ →₀ ℕ) :
  ((AKLT.W.H1C003.scaleVariables s) p).coeff d = p.coeff d * AKLT.W.H1C003.monomialScale s d
'AKLT.W.H1C003.coeff_scaleVariables' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.inversionSign (I : Finset (Fin 20)) (v : Fin 20 × Fin 3) : ℚ
AKLT.W.H1C003.invertPolynomial_eq_scaleVariables (I : Finset (Fin 20)) (p : MvPolynomial (Fin 20 × Fin 3) ℚ) :
  AKLT.Defs.invertPolynomial I p = (AKLT.W.H1C003.scaleVariables (AKLT.W.H1C003.inversionSign I)) p
'AKLT.W.H1C003.invertPolynomial_eq_scaleVariables' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.IntegralRat (x : ℚ) : Prop
AKLT.W.H1C003.integralRat_intCast (z : ℤ) : AKLT.W.H1C003.IntegralRat ↑z
'AKLT.W.H1C003.integralRat_intCast' depends on axioms: [propext, Quot.sound]
AKLT.W.H1C003.IntegralRat.add {x y : ℚ} (hx : AKLT.W.H1C003.IntegralRat x) (hy : AKLT.W.H1C003.IntegralRat y) :
  AKLT.W.H1C003.IntegralRat (x + y)
'AKLT.W.H1C003.IntegralRat.add' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.IntegralRat.sub {x y : ℚ} (hx : AKLT.W.H1C003.IntegralRat x) (hy : AKLT.W.H1C003.IntegralRat y) :
  AKLT.W.H1C003.IntegralRat (x - y)
'AKLT.W.H1C003.IntegralRat.sub' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.IntegralRat.mul {x y : ℚ} (hx : AKLT.W.H1C003.IntegralRat x) (hy : AKLT.W.H1C003.IntegralRat y) :
  AKLT.W.H1C003.IntegralRat (x * y)
'AKLT.W.H1C003.IntegralRat.mul' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.IntegralRat.pow {x : ℚ} (hx : AKLT.W.H1C003.IntegralRat x) (n : ℕ) : AKLT.W.H1C003.IntegralRat (x ^ n)
'AKLT.W.H1C003.IntegralRat.pow' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.integralRat_sum.{u_1} {ι : Type u_1} (s : Finset ι) (f : ι → ℚ)
  (h : ∀ i ∈ s, AKLT.W.H1C003.IntegralRat (f i)) : AKLT.W.H1C003.IntegralRat (∑ i ∈ s, f i)
'AKLT.W.H1C003.integralRat_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.integralRat_prod.{u_1} {ι : Type u_1} (s : Finset ι) (f : ι → ℚ)
  (h : ∀ i ∈ s, AKLT.W.H1C003.IntegralRat (f i)) : AKLT.W.H1C003.IntegralRat (∏ i ∈ s, f i)
'AKLT.W.H1C003.integralRat_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.integralRat_inversionScale (I : Finset (Fin 20)) (d : Fin 20 × Fin 3 →₀ ℕ) :
  AKLT.W.H1C003.IntegralRat (AKLT.W.H1C003.monomialScale (AKLT.W.H1C003.inversionSign I) d)
'AKLT.W.H1C003.integralRat_inversionScale' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.denominator_inverted_coeff (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation) (D₀ : ℕ)
  (hD : AKLT.Defs.ClearsDenominator π r D₀) (I : Finset (Fin 20)) (next : Bool) (d : Fin 20 × Fin 3 →₀ ℕ) :
  AKLT.W.H1C003.IntegralRat
    ((if next = true then 5 else 3) * ↑D₀ *
      (AKLT.Defs.invertPolynomial I (AKLT.Defs.reducedPolynomial π r next)).coeff d)
'AKLT.W.H1C003.denominator_inverted_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.inverted_reducedPolynomial_real (π : AKLT.Defs.PatternData) (hπ : π.Covered)
  (r : AKLT.Defs.Representation) (I J : Finset (Fin 20)) (next : Bool) (σ τ : ↥J → Fin 2) :
  (AKLT.Defs.pauliOperator J (AKLT.Defs.invertPolynomial I (AKLT.Defs.reducedPolynomial π r next)) σ τ).im = 0
'AKLT.W.H1C003.inverted_reducedPolynomial_real' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.rationalOperatorEntry_re (J : Finset (Fin 20)) (p : MvPolynomial (Fin 20 × Fin 3) ℚ) (σ τ : ↥J → Fin 2) :
  ↑(AKLT.Defs.rationalOperatorEntry J p σ τ) = (AKLT.Defs.pauliOperator J p σ τ).re
'AKLT.W.H1C003.rationalOperatorEntry_re' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.scaled_rationalOperatorEntry_integral (J : Finset (Fin 20)) (p : MvPolynomial (Fin 20 × Fin 3) ℚ) (k : ℚ)
  (hk : ∀ (d : Fin 20 × Fin 3 →₀ ℕ), AKLT.W.H1C003.IntegralRat (k * p.coeff d)) (σ τ : ↥J → Fin 2) :
  AKLT.W.H1C003.IntegralRat (k * AKLT.Defs.rationalOperatorEntry J p σ τ)
'AKLT.W.H1C003.scaled_rationalOperatorEntry_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.scaled_rationalSectorEntry_integral (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation)
  (ε : AKLT.Defs.ExchangeSigns π) (p : MvPolynomial (Fin 20 × Fin 3) ℚ) (k : ℚ)
  (hk : ∀ (d : Fin 20 × Fin 3 →₀ ℕ), AKLT.W.H1C003.IntegralRat (k * p.coeff d)) (a b : AKLT.Defs.CentralBasis π r ε) :
  AKLT.W.H1C003.IntegralRat (k * AKLT.Defs.rationalSectorEntry π r ε p a b)
'AKLT.W.H1C003.scaled_rationalSectorEntry_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.integerSectorMatrix_cast (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation)
  (ε : AKLT.Defs.ExchangeSigns π) (I : Finset (Fin 20)) (D₀ : ℕ) (hD : AKLT.Defs.ClearsDenominator π r D₀) (next : Bool)
  (a b : AKLT.Defs.CentralBasis π r ε) :
  ↑(AKLT.Defs.integerSectorMatrix π r ε I D₀ next a b) =
    (if next = true then 5 else 3) * ↑D₀ *
      AKLT.Defs.rationalSectorEntry π r ε (AKLT.Defs.invertPolynomial I (AKLT.Defs.reducedPolynomial π r next)) a b
'AKLT.W.H1C003.integerSectorMatrix_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.inverted_rationalSectorEntry_cast (π : AKLT.Defs.PatternData) (hπ : π.Covered)
  (r : AKLT.Defs.Representation) (ε : AKLT.Defs.ExchangeSigns π) (I : Finset (Fin 20)) (next : Bool)
  (a b : AKLT.Defs.CentralBasis π r ε) :
  ↑(AKLT.Defs.rationalSectorEntry π r ε (AKLT.Defs.invertPolynomial I (AKLT.Defs.reducedPolynomial π r next)) a b) =
    AKLT.Defs.complexSectorMatrix π r ε (AKLT.Defs.invertPolynomial I (AKLT.Defs.reducedPolynomial π r next)) a b
'AKLT.W.H1C003.inverted_rationalSectorEntry_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.integerSectorMatrix_cast_complex (π : AKLT.Defs.PatternData) (hπ : π.Covered)
  (r : AKLT.Defs.Representation) (ε : AKLT.Defs.ExchangeSigns π) (I : Finset (Fin 20)) (D₀ : ℕ)
  (hD : AKLT.Defs.ClearsDenominator π r D₀) (next : Bool) (a b : AKLT.Defs.CentralBasis π r ε) :
  ↑(AKLT.Defs.integerSectorMatrix π r ε I D₀ next a b) =
    (if next = true then 5 else 3) * ↑D₀ *
      AKLT.Defs.complexSectorMatrix π r ε (AKLT.Defs.invertPolynomial I (AKLT.Defs.reducedPolynomial π r next)) a b
'AKLT.W.H1C003.integerSectorMatrix_cast_complex' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.thresholdScale_proof : AKLT.Cert.H1.Production.TopLeaves.thresholdScale
'AKLT.W.H1C003.thresholdScale_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.positiveScale_of_thresholdScale (hthreshold : AKLT.Cert.H1.Production.TopLeaves.thresholdScale) :
  AKLT.Cert.H1.Production.TopLeaves.positiveScale
'AKLT.W.H1C003.positiveScale_of_thresholdScale' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C003.main : AKLT.Cert.H1.Production.TopLeaves.positiveScale
'AKLT.W.H1C003.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Open issues

No mathematical residual or unproved dependency remains. This session ran Lake/Lean verification; the campaign's separate con-ron/NanoDa recheck remains for its runner.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1C003.main : AKLT.Cert.H1.Production.TopLeaves.positiveScale`.
- Also proved `AKLT.W.H1C003.thresholdScale_proof : AKLT.Cert.H1.Production.TopLeaves.thresholdScale`.
- Status is PROVED FROM DEPS: uses indexed leaves `AKLT.W.H1M023.main` and `AKLT.W.H1M043.main`.
- All five source files are imported transitively by Main.
- No residual statements or open leaf names remain.
- Final Lake build passed in 16.56 seconds; exact-type/axiom check passed in 6.46 seconds.
- All 24 exported theorems use only permitted axioms.
- No source outside the assigned directory was changed; no sub-agents were used.
- Independent kernel recheck remains for the campaign runner.
- Orchestrator: check and accept the exact main theorem; no mathematical follow-up is needed.
