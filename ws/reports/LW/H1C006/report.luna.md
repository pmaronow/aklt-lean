STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/Main.lean)

## Exported declarations

- `AKLT.W.H1C006.Residual_sectorToBall : Prop` — strict positivity of all indexed central-sector matrices implies nonnegativity of the rational-threshold reduced difference on every supported product of closed balls. This isolates the exact scaling, inversion/product-density, operator-structure, and ladder-sector work.
- `AKLT.W.H1C006.Residual_commonReconstruction : Prop` — each covered pattern assignment has a common positive factor and a common reduced vector representing both current and next functionals.
- `AKLT.W.H1C006.main_of_residuals (hSector : Residual_sectorToBall) (hReconstruct : Residual_commonReconstruction) : AKLT.Cert.H1.Production.TopLeaves.sectorPositiveImpliesBound`.
- `AKLT.W.H1C006.main` has the same conditional signature as `main_of_residuals`. The requested unconditional signature is not proved in this partial delivery.

The assembly uses the existing proved `AKLT.Blueprint.H1.differenceEvaluation` lemma and exact coercion of `p / q` from `ℚ` to `ℝ`; multiplying the reduced nonnegativity by the common positive factor gives the original inequality.

## Axioms

`#print axioms AKLT.W.H1C006.main_of_residuals` and `#print axioms AKLT.W.H1C006.main` both report:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H1C006.Main` — passed; Main compiled in 6.2 seconds (13.6 seconds for the command invocation including Lake overhead).

## Open issues

Neither residual has a proof yet. The first is the main analytic bridge: the certificate matrices are indexed central restrictions, and the proof must recover positivity for arbitrary product densities while respecting the symmetric support of U sectors and the D-sector decomposition. The second is the common-factor reduction from the original pattern functional. Consequently, `AKLT.W.H1C006.main` is conditional and does not meet the requested exact theorem type.

The suggested different-cheaper-model first attempt was not made; this delivery followed the leaf-writer restriction against sub-agents.

## ORCH-SUMMARY

- Delivered compiled `AKLT/W/H1C006/Main.lean` and this report.
- `AKLT.W.H1C006.main` is conditional on `Residual_sectorToBall` and `Residual_commonReconstruction`; requested unconditional theorem remains open.
- Both residuals are closed `Prop` definitions and name the outstanding analytic and reduction bridges.
- Build passed with `lake build AKLT.W.H1C006.Main`.
- Exported theorem axioms: `[propext, Classical.choice, Quot.sound]`.
- No sorry/admit/axiom was added; no existing file was edited.
- Different-cheaper-model first attempt was omitted under the no-sub-agent rule.
- Orchestrator: assign proofs for the two residuals or route this leaf for further work.
