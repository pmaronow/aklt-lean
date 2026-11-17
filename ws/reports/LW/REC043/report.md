STATUS: PROVED

## Files

- [Bonds.lean](/home/ubuntu/aklt/wt/LW_REC043/AKLT/W/REC043/Bonds.lean)
- [Enumeration.lean](/home/ubuntu/aklt/wt/LW_REC043/AKLT/W/REC043/Enumeration.lean)
- [Factors.lean](/home/ubuntu/aklt/wt/LW_REC043/AKLT/W/REC043/Factors.lean)
- [Fibres.lean](/home/ubuntu/aklt/wt/LW_REC043/AKLT/W/REC043/Fibres.lean)
- [Iteration.lean](/home/ubuntu/aklt/wt/LW_REC043/AKLT/W/REC043/Iteration.lean)
- [LocalStep.lean](/home/ubuntu/aklt/wt/LW_REC043/AKLT/W/REC043/LocalStep.lean)
- [Main.lean](/home/ubuntu/aklt/wt/LW_REC043/AKLT/W/REC043/Main.lean)
- [Moments.lean](/home/ubuntu/aklt/wt/LW_REC043/AKLT/W/REC043/Moments.lean)
- [Normalization.lean](/home/ubuntu/aklt/wt/LW_REC043/AKLT/W/REC043/Normalization.lean)
- [Padding.lean](/home/ubuntu/aklt/wt/LW_REC043/AKLT/W/REC043/Padding.lean)
- [SetMoments.lean](/home/ubuntu/aklt/wt/LW_REC043/AKLT/W/REC043/SetMoments.lean)
- [Trace.lean](/home/ubuntu/aklt/wt/LW_REC043/AKLT/W/REC043/Trace.lean)
- [Trails.lean](/home/ubuntu/aklt/wt/LW_REC043/AKLT/W/REC043/Trails.lean)

`LocalStep.lean` supplies the missing local contraction. `SetMoments.lean` repairs the finite-set reindexing proofs in the earlier attempt. `Main.lean` now exports the requested closed theorem. The other files retain the earlier attempt's finite iteration, trail enumeration, Fubini decomposition, and normalization proofs.

All source changes are confined to `AKLT/W/REC043/`. No frozen definition, statement, or other leaf file was edited. No other blueprint leaf is imported as a lemma.

## Exported declarations

```lean
theorem AKLT.W.REC043.main : AKLT.Blueprint.Rec.PairExpansionStatement

theorem AKLT.W.REC043.coordinateStep : AKLT.Blueprint.Rec.CoordinateStepStatement

theorem AKLT.W.REC043.uStepMoment : AKLT.Blueprint.Rec.UStepMomentStatement

theorem AKLT.W.REC043.dStepMoment : AKLT.Blueprint.Rec.DStepMomentStatement
```

The complete inventory of 66 exported declarations, including exact helper signatures and definition types, is in [declarations.md](/home/ubuntu/aklt/reports/LW/REC043/declarations.md). All 53 exported theorems were checked individually with `#check` and `#print axioms`; their elaborated signatures and axiom outputs are in [audit.log](/home/ubuntu/aklt/reports/LW/REC043/audit.log).

The main theorem has no hypotheses. The legacy transparent definition `LocalPartitionResidual := CoordinateStepStatement` remains for the conditional iteration lemmas, and is discharged by the proved `coordinateStep` theorem in `main`.

## Proof

At an unprotected departure, disintegrate the original partition into a finite sum over the outside configurations and a one-site functional. The bond and original-leg products outside the departure agree before and after each trace step. Apply the finite U/D site-moment identities to the marked coordinate, retaining the fixed target coordinate as a scalar. This proves the local coordinate-step statement for both pin choices.

The existing fuel induction uses the strictly decreasing present-bond count, including zero contributions from dead branches. Its finite choice tree equals the stopped direction-word sum. Sum the three unnormalized coordinate identities and divide only at the end.

Normalization uses nonnegative configuration weights: if a normalizer is zero, all its observable numerators are zero. Thus the required cancellation holds without an additional strict-positivity premise. The frozen statement is proved as written.

## Axioms

```text
'AKLT.W.REC043.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC043.coordinateStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC043.uStepMoment' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC043.dStepMoment' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every one of the 53 exported theorems has exactly the same allowed axiom list; see the complete [axiom audit](/home/ubuntu/aklt/reports/LW/REC043/audit.log). Source scanning found none of the prohibited proof mechanisms.

## Builds and exact-type check

Commands use `PATH="$HOME/.elan/bin:$PATH"`.

- `lake build AKLT.W.REC043.Main` — success. The first successful build compiled `LocalStep` in 3.4 seconds and `Main` in 3.3 seconds. A final timed validation took 7.61 seconds, exit code 0; [build.log](/home/ubuntu/aklt/reports/LW/REC043/build.log), [build.time](/home/ubuntu/aklt/reports/LW/REC043/build.time).
- `lake env lean /tmp/REC043Audit.lean` — success, 5.13 seconds, exit code 0; [audit.log](/home/ubuntu/aklt/reports/LW/REC043/audit.log), [audit.time](/home/ubuntu/aklt/reports/LW/REC043/audit.time). The audit included the independent exact-type check:

```lean
import AKLT.W.REC043.Main
example : AKLT.Blueprint.Rec.PairExpansionStatement := AKLT.W.REC043.main
```

The build emits only inherited unused-simp-argument warnings and one deprecated tactic-name warning. No Mathlib or package files were rebuilt or modified.

## Open issues

None. The requested exact declaration exists, compiles, and depends only on the allowed axioms. There are no remaining residual statements to prove.

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT/W/REC043/Main.lean` and its 12 helper files.
- Exact theorem: `AKLT.W.REC043.main : AKLT.Blueprint.Rec.PairExpansionStatement`.
- Missing local contraction is proved as `AKLT.W.REC043.coordinateStep`.
- U/D site-moment identities are also proved locally.
- Main build and independent exact-type check pass.
- All 53 exported theorems use only propext, Classical.choice, and Quot.sound.
- No imported blueprint proof dependencies; no changes outside REC043 source/report directories.
- Open names: none. Legacy `LocalPartitionResidual` is fully discharged.
- Deviation: final cancellation handles zero normalizers using nonnegative weights.
- Limitations: harmless inherited linter/deprecation warnings only.
- Orchestrator: accept/index the main theorem; no further premise or proof task is needed.
