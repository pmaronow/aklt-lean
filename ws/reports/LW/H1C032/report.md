STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C032/AKLT/W/H1C032/Main.lean) — complete proof; the only Lean source in this task directory.

## Exported declarations

```lean
theorem AKLT.W.H1C032.main :
    AKLT.Cert.H1.Production.Leaves.sameDataWitness

theorem AKLT.W.H1C032.sectorWitnesses_transfer
    (π ρ : AKLT.Defs.PatternData)
    (h : AKLT.Cert.H1.Production.SameEffectiveData π ρ)
    (r : AKLT.Defs.Representation) (I : Finset (Fin 20)) (D p q : Nat)
    (hw : AKLT.Defs.H1SectorWitnesses π r I D p q) :
    AKLT.Defs.H1SectorWitnesses ρ r I D p q
```

All other task declarations are private helper definitions or proved lemmas. There are no residual assumptions or unfinished declarations. No other blueprint leaf is used as a lemma.

## Proof

Reused the earlier attempt's proofs identifying reduction groups, vector tokens, and reduced current/next polynomials. Sites of degree zero have zero internal exponent in every supported integrand monomial, so their moment factor is one even when their statuses or retained-spin membership differ.

Completed the sector transport with explicit equivalences of group indices, vector indices, exchange signs, group bases, and central bases. The equivalences preserve coordinate values and the reconstructed rational sector entries. Therefore they preserve the integer threshold matrix. Composing the certificate's chosen indexing with the central-basis equivalence leaves its `Fin t` matrix order unchanged, allowing the same lower-triangular factor, positive scales, and residual row inequalities to be reused.

The main theorem also transfers group inversion and the clearing denominator, and identifies the threshold numerator and denominator from the equal outgoing direction. It transports the reduced witness; it never asserts equality of the raw current/next functionals.

## Axiom checks

The module contains `#print axioms` checks. Output for both exported theorems:

```text
'AKLT.W.H1C032.sectorWitnesses_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C032.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The private `reducedPolynomial_eq` likewise reports only `[propext, Classical.choice, Quot.sound]`. A source scan found none of the forbidden proof escape mechanisms.

## Validation

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1C032.Main` — passed; 12.82 seconds wall time, 7.9 seconds reported for the new module. This module emits no warnings; Lake replays existing warnings from imported libraries.
- `PATH="$HOME/.elan/bin:$PATH" lake env lean /tmp/H1C032ExactType.lean` — passed; 6.12 seconds wall time. The separate checker imports the built module and contains:

```lean
import AKLT.W.H1C032.Main

example : AKLT.Cert.H1.Production.Leaves.sameDataWitness := AKLT.W.H1C032.main
#print axioms AKLT.W.H1C032.main
#print axioms AKLT.W.H1C032.sectorWitnesses_transfer
```

Only the task directory and report were changed. Independent kernels were not run here.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C032/Main.lean` and this report.
- Exact requested theorem: `AKLT.W.H1C032.main : AKLT.Cert.H1.Production.Leaves.sameDataWitness`.
- Also exported `AKLT.W.H1C032.sectorWitnesses_transfer`, with no coveredness requirement.
- Closed the earlier sector-transport residual; no residual propositions remain.
- Preserved the chosen certificate matrix ordering and reused its Gram witness.
- No raw current/next equality is asserted.
- No dependencies on other proved blueprint leaves.
- Only allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Required Lake build and separate import/exact-type check passed.
- Open declarations: none. Limitations: independent-kernel checks remain for the campaign checker.
- No orchestrator decision or additional premise is needed.
