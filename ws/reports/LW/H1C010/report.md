STATUS: PROVED FROM DEPS

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C010/AKLT/W/H1C010/Main.lean): positivity, denominator assembly, and the unconditional requested theorem.
- [Arithmetic.lean](/home/ubuntu/aklt/wt/LW_H1C010/AKLT/W/H1C010/Arithmetic.lean): reused unchanged; proves integrality of the network coefficients and transport through inversion. Imported by Main.

Only Main.lean was changed in this attempt. Every Lean file in the task directory is transitively imported by Main.

## Exported declarations

All declarations below are in namespace `AKLT.W.H1C010`. Here `VectorPolynomial`, `SiteSpec`, and the polynomial operations denote their existing production definitions.

```lean
theorem networkIntegerCoefficients (ss : List PackedSite) (out : Nat) (next : Bool)
    (m : (Fin 20 × Fin 3) →₀ ℕ) :
    ∃ z : ℤ, (networkNumerator ss out next).coeff m = z

theorem inversionCoefficientTransfer (I : Finset (Fin 20)) (p : VectorPolynomial) (k : ℚ)
    (h : ∀ m, ∃ z : ℤ, k * (invertPolynomial I p).coeff m = z) :
    ∀ m, ∃ z : ℤ, k * p.coeff m = z

theorem localTotalDenPositive (s : SiteSpec) : 0 < s.totalDen

theorem denominator_of_momentPolynomial
    (hMoment : AKLT.Cert.H1.Production.Leaves.momentPolynomial) :
    AKLT.Cert.H1.Production.Leaves.denominator

theorem main : AKLT.Cert.H1.Production.Leaves.denominator
```

The exact delivered name is `AKLT.W.H1C010.main`. It has no additional hypotheses.

## Proof and dependency

The sole imported blueprint proof is `AKLT.W.H1C020.main` from `AKLT.W.H1C020.Main`, registered in `/home/ubuntu/aklt/state/lw/proved-index.tsv` for `AKLT.Cert.H1.Production.Leaves.momentPolynomial`.

Each local `SiteSpec.totalDen` is positive, so their product D is positive. The moment-polynomial identity identifies the network numerator with `C ((if next then 5 else 3) * D)` times the inverted actual `reducedPolynomial`. The numerator belongs to the image of the coefficientwise map from integer polynomials, so all its coefficients are integers. Sign inversion preserves that image and is involutive. Applying it again establishes integer coefficients for the scaled original polynomial, for either value of `next` and every monomial. This proves the required coefficient clearing for both actual reduced polynomials.

The former `Residual_momentIdentity` definition was removed, and the former conditional `main` was replaced by the requested closed theorem.

## Axiom checks

The source files contain `#print axioms` commands for every exported theorem. Build output:

```text
'AKLT.W.H1C010.networkIntegerCoefficients' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C010.inversionCoefficientTransfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C010.localTotalDenPositive' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C010.denominator_of_momentPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C010.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are exactly the permitted axioms. A source scan found none of the forbidden declarations or proof shortcuts in the task directory.

## Build

Command, run from `/home/ubuntu/aklt/wt/LW_H1C010`:

```sh
PATH="$HOME/.elan/bin:$PATH" /usr/bin/time -p lake build AKLT.W.H1C010.Main
```

Result: exit code 0, `Build completed successfully (8996 jobs).`

- Total wall time: 131.13 seconds, including compilation of newly imported H1C020 dependency modules.
- H1C010.Main compilation: 6.2 seconds.
- CPU times: user 203.92 seconds, system 34.95 seconds.

No existing files outside the task directory were edited. Mathlib was not rebuilt, and no sub-agents were used.

## Open issues

None. No residual propositions remain in H1C010.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1C010.main : AKLT.Cert.H1.Production.Leaves.denominator` unconditionally.
- Status: PROVED FROM DEPS.
- Dependency: indexed `AKLT.W.H1C020.main`, proving `Leaves.momentPolynomial`.
- Reused Arithmetic.lean unchanged; Main imports it.
- Proves positivity and coefficient clearing for both actual reduced polynomials.
- Removed the former residual definition and conditional main signature.
- All five exported theorem axiom checks list only propext, Classical.choice, Quot.sound.
- Build succeeded; 131.13 seconds overall, 6.2 seconds for H1C010.Main.
- Open names: none. Limitations or deviations: none.
- Orchestrator: register H1C010.main as the completed denominator leaf.
