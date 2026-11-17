STATUS: PROVED FROM DEPS

The required unconditional theorem is proved and passes the exact-type check:

```lean
theorem AKLT.W.H3C026.main : CertData.H3.Bridge.RowTermsV2Leaf
```

The earlier conditional `main` and its residual have been replaced. No residual statements or additional hypotheses on `main` remain.

## Files

All Lean files are under `/home/ubuntu/aklt/wt/LW_H3C026/AKLT/W/H3C026/`:

| File | Contents |
| --- | --- |
| `Main.lean` | Required closed theorem. |
| `Assembly.lean` | Row expansion and transport to corrected V2 coefficients. |
| `Routing.lean` | Direction blocks, packed components, scalar mask/pull expansion. |
| `Scalar.lean` | Each scalar direction equals its stationary phase sum. |
| `Local.lean` | Quotient correctness consequences, known-site edges, table extension, checked centre zero. |
| `Arithmetic.lean` | Exact diagonal and response coefficient ceilings. |
| `Translation.lean` | Translation of local response sums and the non-neighbour case. |
| `Coefficients.lean` | Five dead-neighbour cases and phase-sum identities. |
| `Masks.lean` | Packing/subtraction identities and the ordinary mask leaf. |
| `KnownMask.lean` | Known-site mask leaf. |
| `DeadMask.lean` | Dead-neighbour mask leaf. |
| `PullMasks.lean` | Boundary masks, lane refinement, mask complements. |
| `Pull.lean` | Boundary fill, spatial indexing, pull leaf. |
| `Audit.lean` | Exact-type check and main axiom audit. |

Report artifacts in `/home/ubuntu/aklt/reports/LW/H3C026/`:

- `report.md`: this report.
- [declarations.md](declarations.md): statements of every exported theorem and the exported helper definitions.
- [axioms.txt](axioms.txt): complete `#print axioms` output for all 54 exported theorems.
- [build.log](build.log): final successful requested-module build.
- [exact-type-check.log](exact-type-check.log): independent exact-type check output.
- `report.luna.md`: supplied earlier-attempt report, preserved.

## Main exported declarations

All theorem names below have prefix `AKLT.W.H3C026.`.

| Theorem | Statement | Module |
| --- | --- | --- |
| `main` | `CertData.H3.Bridge.RowTermsV2Leaf` | `AKLT.W.H3C026.Main` |
| `ordinaryMask_proved` | `CertData.H3.Bridge.OrdinaryMaskLeaf` | `AKLT.W.H3C026.Masks` |
| `knownMask_proved` | `CertData.H3.Bridge.KnownMaskLeaf` | `AKLT.W.H3C026.KnownMask` |
| `deadMask_proved` | `CertData.H3.Bridge.DeadMaskLeaf` | `AKLT.W.H3C026.DeadMask` |
| `pull_proved` | `CertData.H3.Bridge.PullLeaf` | `AKLT.W.H3C026.Pull` |
| `rowTermsV2_from_leaves` | `OrdinaryMaskLeaf → KnownMaskLeaf → DeadMaskLeaf → PullLeaf → RowTermsV2Leaf` (all in `CertData.H3.Bridge`) | `AKLT.W.H3C026.Assembly` |

The remaining exported helpers have their complete statements in [declarations.md](declarations.md).

## Proof and dependency

The only imported proved blueprint leaf is the indexed theorem
`AKLT.W.H3C024.main : CertData.H3.Bridge.CentreZeroV2Leaf`.
The four mask/pull leaves are proved locally.

The proof expands the four direction blocks and their phase contributions. Generic packed-lane identities prove the masks and boundary routing symbolically. The small local direction/dead-neighbour cases establish exact rational response ceilings, with the response sum taken before rounding and the exact dyadic witness retained. Quotient correctness supplies the incoming-direction and departure-kind facts.

The checked centre lane gives zero extended continuation value in every phase/state. This handles centre-destination terms, and the indexed centre-zero lemma transports the legacy sum to `stationaryCoefficientV2`, including the distinct known-site centre-edge rule. No whole certificate or stored plane is normalized.

## Axioms and soundness

Every exported theorem has a `#print axioms` command in its source. Complete results are in [axioms.txt](axioms.txt). The required theorem reports:

```text
'AKLT.W.H3C026.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every other exported theorem uses a subset of these allowed axioms. The source audit found no forbidden proof constructs and no remaining residual declarations. Finite checks use kernel-checked proofs and `norm_num`; no `native_decide` is used. No sub-agents were used. Existing files outside this task directory were not edited.

## Build and exact-type validation

With `PATH="$HOME/.elan/bin:$PATH"`:

```text
lake build AKLT.W.H3C026.Main
Build completed successfully (8986 jobs).
ELAPSED 13.50

lake env lean AKLT/W/H3C026/Audit.lean
AKLT.W.H3C026.main : CertData.H3.Bridge.RowTermsV2Leaf
'AKLT.W.H3C026.main' depends on axioms: [propext, Classical.choice, Quot.sound]
ELAPSED 5.89
```

The final build is incremental over the supplied prebuilt project and helpers compiled during this attempt. The exact response arithmetic helper took 55 seconds in its successful compilation. Non-fatal warnings concern unused simplification arguments and deprecated tactic-lemma aliases.

Open issues: none.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C026/Main.lean` with the exact unconditional requested theorem.
- Register `CertData.H3.Bridge.RowTermsV2Leaf` → `AKLT.W.H3C026.main`, module `AKLT.W.H3C026.Main`.
- Also proved `OrdinaryMaskLeaf`, `KnownMaskLeaf`, `DeadMaskLeaf`, and `PullLeaf`; mappings are above.
- Reused only the indexed blueprint dependency `AKLT.W.H3C024.main : CentreZeroV2Leaf`.
- Exact-type check and requested build both pass.
- Main axioms: `propext`, `Classical.choice`, `Quot.sound`; all 54 exported theorem audits are recorded.
- No residuals, open mathematical obligations, or extra premises remain.
- No certificate-wide normalization, forbidden proof mechanisms, or sub-agents.
- Final build timing is incremental; non-fatal lint/deprecation warnings remain.
- No orchestrator decision or further proof input is required.
