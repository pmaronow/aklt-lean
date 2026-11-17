STATUS: PARTIAL

## Delivered files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C010/AKLT/W/H1C010/Main.lean): positive local denominators, positivity of their product, selection of an outgoing ring site, and the complete reduction to the moment-polynomial leaf.
- [Arithmetic.lean](/home/ubuntu/aklt/wt/LW_H1C010/AKLT/W/H1C010/Arithmetic.lean): unconditional integrality of every coefficient of the integer network numerator, and preservation of scaled coefficient integrality when undoing inversion. Imported by Main.
- [build.log](/home/ubuntu/aklt/reports/LW/H1C010/build.log): successful Lake build and axiom output.

Only files inside the assigned task directory and report directory were changed. The earlier report is preserved as report.luna.md. There are no unimported Lean files in the task directory.

## Exported declarations

All names below are in namespace `AKLT.W.H1C010`. In these statements, `Leaves` abbreviates `AKLT.Cert.H1.Production.Leaves`; the other definitions are the original Defs and Production definitions.

```lean
theorem networkIntegerCoefficients
    (ss : List PackedSite) (out : Nat) (next : Bool)
    (m : (Fin 20 × Fin 3) →₀ ℕ) :
    ∃ z : ℤ, (networkNumerator ss out next).coeff m = z

theorem inversionCoefficientTransfer
    (I : Finset (Fin 20)) (p : VectorPolynomial) (k : ℚ)
    (h : ∀ m, ∃ z : ℤ, k * (invertPolynomial I p).coeff m = z) :
    ∀ m, ∃ z : ℤ, k * p.coeff m = z

theorem localTotalDenPositive (s : SiteSpec) : 0 < s.totalDen

theorem denominator_of_momentPolynomial
    (hMoment : Leaves.momentPolynomial) : Leaves.denominator

def Residual_momentIdentity : Prop := Leaves.momentPolynomial

theorem main (hMoment : Residual_momentIdentity) : Leaves.denominator
```

The requested unconditional type
`AKLT.W.H1C010.main : AKLT.Cert.H1.Production.Leaves.denominator`
is **not established**. The delivered `main` has the explicit residual premise displayed above. It must not be entered in the proved-leaf index as an unconditional proof.

## Proof and remaining dependency

Integer polynomials form the range subring of the coefficientwise map from `MvPolynomial (Fin 20 × Fin 3) ℤ` to rational polynomials. The proof shows that all vector monomials, local polynomials, ring products, traces, and center-insertion sums belong to this subring. Consequently `networkIntegerCoefficients` needs neither geometry nor table-acceptance hypotheses.

Inversion preserves this subring and is involutive. Applying inversion to `C k * invertPolynomial I p` proves integrality of every coefficient of `C k * p`. This argument works on the actual polynomial coefficients; it does not infer them from matrix entries.

Every local LCD and every `SiteSpec.totalDen` is positive. Given the moment-polynomial identity, taking an arbitrary coefficient gives integrality of the scaled inverted reduced polynomial. The proved inversion theorem transfers that integrality to the original reduced polynomial, for both `next = false` and `next = true`. Together with product positivity, this is precisely `ClearsDenominator`.

The sole residual is the exact existing blueprint leaf:

```lean
AKLT.Cert.H1.Production.Leaves.momentPolynomial
```

It does not appear in `/home/ubuntu/aklt/state/lw/proved-index.tsv`. It identifies the integer ring-network expansion with the denominator-scaled inversion of the literal `reducedPolynomial`, under coveredness, group inversion, network geometry, and the outgoing-site equality. Proving this identity requires the remaining global moment-contraction/geometry bridge, including tip radii, retained versus replaced corners, and the changed next-mode center law. No proof of that leaf is imported or assumed implicitly.

Compared with the earlier attempt, `Residual_networkIntegerCoefficients` and `Residual_inversionCoefficientTransfer` have been discharged and removed. Only `Residual_momentIdentity` remains; it is a transparent definition of the named missing blueprint leaf.

## Axioms

The delivered modules run `#print axioms` on every exported theorem. The successful build reports:

```text
'AKLT.W.H1C010.networkIntegerCoefficients' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C010.inversionCoefficientTransfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C010.localTotalDenPositive' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C010.denominator_of_momentPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C010.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No forbidden proof placeholder, custom axiom, unsafe declaration, kernel-check bypass, or unbounded-heartbeat setting occurs in the delivered files. The proofs use symbolic polynomial and list lemmas rather than evaluating a concrete large certificate.

## Build

```sh
PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1C010.Main
```

Passed. Final timed build: 17.68 seconds wall time; Lake reported Arithmetic 5.9 seconds and Main 6.2 seconds. Existing dependencies were replayed. Neither Mathlib nor package metadata was changed. Earlier direct `lake env lean AKLT/W/H1C010/Arithmetic.lean` checks were used while developing the arithmetic proof; the final Lake build checked both delivered modules without warnings from these modules.

## ORCH-SUMMARY

- Status: PARTIAL; unconditional denominator leaf remains open.
- Delivered Arithmetic.lean and Main.lean; Main imports every task helper.
- Proved all integer-network polynomial coefficients integral, with no geometry assumptions.
- Proved inversion transfers integrality of every scaled polynomial coefficient.
- Proved every local total denominator and its network product positive.
- Proved `Leaves.momentPolynomial → Leaves.denominator`.
- Sole open prerequisite: `AKLT.Cert.H1.Production.Leaves.momentPolynomial`.
- Transparent residual: `AKLT.W.H1C010.Residual_momentIdentity`.
- Delivered `AKLT.W.H1C010.main` is conditional on that residual.
- Do not register this main as the exact unconditional target.
- Build passed in 17.68 seconds; all exported theorem axioms are allowed.
- No proved blueprint dependencies were imported; missing moment leaf is absent from the index.
- Pass the moment-polynomial bridge to its leaf writer; once proved, apply `denominator_of_momentPolynomial` to it.
