STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C032/AKLT/W/H1C032/Main.lean)

## Delivered declarations

- `AKLT.W.H1C032.Residual_sectorWitnessTransport : Prop`

  `∀ π ρ, SameEffectiveData π ρ → ∀ r I D₀ p q, H1SectorWitnesses ρ r I D₀ p q → H1SectorWitnesses π r I D₀ p q`

- `AKLT.W.H1C032.sameDataWitness_of_sectorResidual (hResidual : Residual_sectorWitnessTransport) : AKLT.Cert.H1.Production.Leaves.sameDataWitness`

The conditional theorem also transfers the chosen representation, inversion set, and denominator. The proved reductions establish equality of reduction groups, retained vector sets, and reduced current/next polynomials. The polynomial proof handles degree-zero spins whose membership in `reducedSpinSites` may differ: their internal exponents are absent from the reduced integrand, so their moment factor is 1.

The requested declaration `AKLT.W.H1C032.main : AKLT.Cert.H1.Production.Leaves.sameDataWitness` is not delivered. The residual is the remaining sector witness transport obligation.

## Axiom checks

`#print axioms reducedPolynomial_eq` and `#print axioms sameDataWitness_of_sectorResidual` each report:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake env lean AKLT/W/H1C032/Main.lean` — passed.
- `lake build AKLT.W.H1C032.Main` — passed; 12.8 s wall time, module build reported 7.7 s.
- No tests were run.

## Open issue

`AKLT.W.H1C032.Residual_sectorWitnessTransport` must be proved. It requires transporting each chosen sector indexing and Gram witness across the equivalence between the two reduction-group bases, and showing the reconstructed integer sector matrices agree under that transport. A direct rewrite on the subtype-indexed bases fails because equality of the group Finsets does not identify their dependent function domains. No `sorry`, `admit`, or axiom was used.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C032/Main.lean` and this report.
- Proved equal reduction groups, vector sets, reduced polynomials, inversion transfer, and denominator transfer under `SameEffectiveData`.
- Proved `sameDataWitness_of_sectorResidual`, conditional on the closed residual below.
- Open exact declaration: `AKLT.W.H1C032.Residual_sectorWitnessTransport`.
- The requested exact theorem `AKLT.W.H1C032.main` remains open.
- Blocker: dependent sector basis and integer matrix witness transport across group-index equivalences.
- Build passed; only allowed classical/proof axioms appear in `#print axioms`.
- Orchestrator must prove or route the residual transport obligation before treating the leaf as complete.
