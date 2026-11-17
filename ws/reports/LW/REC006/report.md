STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC006/AKLT/W/REC006/Main.lean): exact requested theorem.
- [Positivity.lean](/home/ubuntu/aklt/wt/LW_REC006/AKLT/W/REC006/Positivity.lean): concrete monomial positivity, tensorization, and free network pair positivity.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC006/AKLT/W/REC006/Audit.lean): exact-type example and axiom checks for every exported theorem.
- [report.md](/home/ubuntu/aklt/reports/LW/REC006/report.md): this report.

Only files in `AKLT/W/REC006/` and this report were written. The earlier conditional proof in `Main.lean` has been replaced; no blueprint, definition, proved library, or dependency file was edited.

## Proof

For every exponent k, the sum of the two sign powers is either two or zero. Each icosahedral group has one zero coordinate and two independently signed coordinates with nonnegative magnitudes. Its average of every coordinate monomial is therefore nonnegative, in every degree. The same holds for all three site statuses, by their explicit nonnegative weights.

A polynomial with natural-number coefficients has nonnegative product-functional value: prove this on monomials by finite tensorization, then use addition. The free bond product, with an optional scalar-product insertion, is such a polynomial. Coordinate polynomials reproduce `Network.spins`, including its extension by zero. Thus the actual free pair numerator and normalizer are nonnegative. `div_nonneg` proves the normalized result, applied to `removeSite a.D a.y`.

This proves the stronger assertion that every free network pair mean is nonnegative, for arbitrary networks and endpoints. Consequently the requested neighbour and distinctness hypotheses need not be used.

No other open blueprint leaf is used as a lemma or hypothesis. There are no residual statements.

## Exported declarations

All names below are in namespace `AKLT.W.REC006`. Statements use `open AKLT.Defs` and `open scoped BigOperators`; proofs are in the linked source files.

```lean
theorem sign_power_sum_nonneg (k : ℕ) :
    0 ≤ ∑ j : Fin 2, signValue j ^ k

theorem two_sign_moment_nonneg (p q r : ℕ) :
    0 ≤ ∑ b : Fin 2, ∑ c : Fin 2,
      (0 : ℝ)^p * (signValue b / icoRadius)^q *
        (signValue c * goldenRatio / icoRadius)^r

theorem ico_monomial_nonneg (m : Fin 3 → ℕ) :
    0 ≤ ∑ j : IcoLetter, ∏ i : Fin 3, icoVector j i ^ m i

theorem site_monomial_nonneg (s : Status) (m : Fin 3 → ℕ) :
    0 ≤ siteFunctional s (fun v => ∏ i, v i ^ m i)

theorem product_polynomial_nonneg {ι : Type*} [Fintype ι]
    (s : ι → Status) (p : MvPolynomial (ι × Fin 3) ℕ) :
    0 ≤ productFunctional s
      (fun a => p.eval₂ (Nat.castRingHom ℝ) (fun z => a z.1 z.2))

theorem eval_coordinatePolynomial {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) (x : Plane) (i : Fin 3) :
    (coordinatePolynomial D x i).eval₂ (Nat.castRingHom ℝ)
        (fun z => spinVector (n z.1) z.2) = D.spins n x i

theorem eval_pairPolynomial {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) (x y : Plane) :
    (pairPolynomial D x y).eval₂ (Nat.castRingHom ℝ)
        (fun z => spinVector (n z.1) z.2) = dot (D.spins n x) (D.spins n y)

theorem eval_bondPolynomial {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) :
    (bondPolynomial D).eval₂ (Nat.castRingHom ℝ)
        (fun z => spinVector (n z.1) z.2) =
      ∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))

theorem free_pair_numerator_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (f g : Plane) :
    0 ≤ D.partition τ false (fun a => dot (a f) (a g))

theorem free_normalizer_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) :
    0 ≤ D.partition τ false (fun _ => 1)

theorem free_pair_mean_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (f g : Plane) :
    0 ≤ D.expectation τ false (fun a => dot (a f) (a g))

theorem main : AKLT.Blueprint.Rec.FreeRemovedPairStatement
```

The three polynomial definitions have these signatures; their concrete bodies are in `Positivity.lean`.

```lean
def coordinatePolynomial {G : Finset Plane} (D : Network G) (x : Plane)
    (i : Fin 3) : MvPolynomial (D.active × Fin 3) ℕ

def pairPolynomial {G : Finset Plane} (D : Network G) (x y : Plane) :
    MvPolynomial (D.active × Fin 3) ℕ

def bondPolynomial {G : Finset Plane} (D : Network G) :
    MvPolynomial (D.active × Fin 3) ℕ
```

## Axiom audit

`Audit.lean` runs `#print axioms` on every exported theorem. Output:

```text
'AKLT.W.REC006.sign_power_sum_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC006.two_sign_moment_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC006.ico_monomial_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC006.site_monomial_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC006.product_polynomial_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC006.eval_coordinatePolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC006.eval_pairPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC006.eval_bondPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC006.free_pair_numerator_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC006.free_normalizer_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC006.free_pair_mean_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC006.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All dependencies are among the three permitted axioms. A source scan found none of the forbidden proof shortcuts or declarations.

## Validation

Commands ran with `$HOME/.elan/bin` added to `PATH`.

- `lake build AKLT.W.REC006.Main` — succeeded; 18.90 seconds wall time. New helper module: 8.4 seconds; main module: 5.5 seconds.
- `lake build AKLT.W.REC006.Audit` — succeeded; 9.29 seconds wall time. Audit module: 4.5 seconds. Its independent exact-type example compiled and `#check` printed:

```text
AKLT.W.REC006.main : AKLT.Blueprint.Rec.FreeRemovedPairStatement
```

An initial development build failed at equality of finite enumerations. The final proof explicitly identifies the enumerations; the successful builds above validate the corrected source.

## Open issues and deviations

None for the requested theorem. The proof uses the concrete alphabet's all-degree coordinate sign symmetry instead of reindexing to the common finite-network model and invoking a degree-four result. This stronger property is specific to the given alphabet and is proved directly here.

The normalizer lemma establishes nonnegativity, which is sufficient for this target in Lean's totalized division. It does not claim to prove the separate strict-positive-normalizer blueprint leaf. Conditioning estimates and coefficient bounds mentioned in the suggested route are outside this leaf and are not needed.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC006.main : AKLT.Blueprint.Rec.FreeRemovedPairStatement`.
- Status: PROVED, with no extra hypotheses or residuals.
- Main imports only the new helper and the existing statement dependency chain.
- Helper proves all-degree monomial positivity for the explicit icosahedral alphabet.
- Free pair numerator and free normalizer are nonnegative for every network.
- Normalized positivity follows by `div_nonneg`; strict normalizer positivity is not needed or claimed.
- Route deviation: direct alphabet symmetry, without degree-four reindexing or other blueprint leaves.
- All 12 exported theorems have axioms `[propext, Classical.choice, Quot.sound]` only.
- Main build and independent exact-type/axiom audit both pass.
- Open names: none. No orchestrator decision is required.
