STATUS: PARTIAL

## Files

- `AKLT/W/REC044/Main.lean`
- `/home/ubuntu/aklt/reports/LW/REC044/report.md`

## Delivered declarations

- `AKLT.W.REC044.icoVector_normSq_one` proves every explicit icosahedron spin vector has squared norm one.
- `AKLT.W.REC044.dSite_normSq` proves the D-site squared-norm mass is `3/5`.
- `AKLT.W.REC044.dSite_mass` proves the D-site total mass is one.
- `AKLT.W.REC044.traceStep_present_mono` and `traceNetwork_present_mono` show tracing cannot create a present bond.
- `AKLT.W.REC044.traceNetwork_status_of_not_mem_dropLast` and `firstHitStatus` show the target status is unchanged before its first hit.
- `AKLT.W.REC044.firstHit_D_no_neighbours` and `firstHit_D_no_original_legs` prove that a D target is isolated after arrival and has no original pin leg. `firstHitIsolation` packages these facts.
- `AKLT.W.REC044.main_of_core_residuals` proves the requested `PairTerminalFactorStatement` assuming the two residual propositions below.

The residual and reduction signatures are:

```lean
Residual_IsolatedSiteLaw : Prop :=
  ∀ G E τ b v, v ∈ E.active → (E.status v = .U ∨ E.status v = .D) →
    (E.status v = .D → E.presentNeighbours v = ∅) →
    (E.status v = .D → ∀ e ∈ originalLegs G, e.1 ≠ v) →
    0 < E.partition τ b (fun _ => 1) →
    E.expectation τ b (fun a => normSq (a v)) = targetFactor E v

Residual_TracePartitionPositive : Prop :=
  ∀ G τ D, D.Auxiliary → ∀ u v, D.AdmissibleStart u →
    AdmissibleTarget D v → u ≠ v → ∀ n w,
    StoppedNetworkTrail D u (insert v (protectedSites G)) w →
    wordVertex u w n = v → ∀ b,
    0 < (traceNetwork D (wordVertices u w)).partition τ b (fun _ => 1)

main_of_core_residuals :
  Residual_IsolatedSiteLaw → Residual_TracePartitionPositive →
    AKLT.Blueprint.Rec.PairTerminalFactorStatement
```

Other exported declarations have these statements: `traceStep_present_mono` and `traceNetwork_present_mono` pull a live bond back to the original network; `traceStep_no_traced_bond` and `traceNetwork_no_traced_bond` say an edge consumed along the trace is absent in both orientations; `traceNetwork_status_of_not_mem_dropLast` preserves the status of any site outside the departure prefix; `wordVertex_mem_of_mem_dropLast` and `wordVertices_split_terminal` identify the departure prefix and final arrival; `network_present_symm` and `adjacent_mem_neighbours` provide lattice edge symmetry; `originalLeg_root_is_protected` places every original pin root in the protected layer; `firstHit_D_no_neighbours`, `firstHit_D_no_original_legs`, and `firstHitIsolation` prove the D-target isolation facts; `firstHitStatus` proves status preservation.

The exact requested declaration `AKLT.W.REC044.main : AKLT.Blueprint.Rec.PairTerminalFactorStatement` is not yet proved.

## Remaining residuals

- `AKLT.W.REC044.Residual_IsolatedSiteLaw`: for an active U site, or an isolated D site with no original pin legs, the normalized expectation of its squared norm equals `targetFactor`, given a positive partition normalizer. This is the remaining finite partition factorization and one-site summation.
- `AKLT.W.REC044.Residual_TracePartitionPositive`: positivity of the traced network partition for every admissible stopped trail and either pin choice. The local degree bounds should support a finite greedy positive-weight configuration, but that construction is not proved here.

`AKLT.W.REC044.main_of_residuals` reduces the requested statement to these two residuals and the proved trace invariants. No assumptions were added to or edits made to the frozen blueprint statement.

## Axioms

`#print axioms` was run on every exported theorem in the module. Each reported:

```text
[propext, Classical.choice, Quot.sound]
```

These are the allowed Lean axioms. The conditional theorem has the two residual propositions as explicit parameters; neither residual is claimed proved.

## Build

- `lake build AKLT.W.REC044.Main` — succeeded, 11.96 seconds (module compile reported 7.2 seconds).
- `lake env lean /tmp/REC044Axioms.lean` — succeeded, 3.97 seconds.

## Open issues

The two residuals above remain open. Consequently the requested unconditional `AKLT.W.REC044.main` is absent and the status is PARTIAL.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC044/Main.lean` with proved spin-moment and first-hit trace/isolation lemmas.
- Delivered `main_of_core_residuals`, conditional on `Residual_IsolatedSiteLaw` and `Residual_TracePartitionPositive`.
- `Residual_IsolatedSiteLaw` is the isolated-site finite partition identity with a positive normalizer.
- `Residual_TracePartitionPositive` is positivity for the traced networks under the stated trail premises.
- The exact unconditional export `AKLT.W.REC044.main` remains unproved.
- Build succeeded with `lake build AKLT.W.REC044.Main`; reported axioms are only the allowed three.
- No edits were made outside the assigned new module and report.
