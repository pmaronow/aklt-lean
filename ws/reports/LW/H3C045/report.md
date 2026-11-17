STATUS: PROVED

## Delivered

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C045/AKLT/W/H3C045/Main.lean) proves the exact target `AKLT.W.H3C045.main : CertData.H3.Bridge.UniformRowCoverageLeaf`.
- This file also proves the reusable helper leaves `planeBatchSound : CertData.H3.Bridge.PlaneBatchSoundLeaf` and `rowCoverage : CertData.H3.Bridge.RowCoverageLeaf`, with interval-check coverage lemmas.

## Proof outline

`planeBatchSound` follows from `List.all`. `intervalEnd_cover` extracts coverage from the recursive interval checker, yielding `rowCoverage`. For the uniform statement, a target key `phaseKey (phaseCode φ) a.val` is below 14964. Division by the positive group selects its batch index; quotient/remainder arithmetic shows that the key's offset is inside the final possibly-shortened batch. Batch soundness then gives the requested `planeCheck`.

The direct chunk argument makes the generic `rowCoverage` helper unnecessary inside `main`; it is proved as a separately reusable leaf. No certificate-wide normalization or native computation is used.

## Exported declarations

- `AKLT.W.H3C045.main : CertData.H3.Bridge.UniformRowCoverageLeaf`
- `AKLT.W.H3C045.planeBatchSound : CertData.H3.Bridge.PlaneBatchSoundLeaf`
- `AKLT.W.H3C045.intervalEnd_cover`: an accepted interval sequence covers every index between its start and end.
- `AKLT.W.H3C045.intervalCheck_cover`: a successful `intervalCheck` covers every index below its limit.
- `AKLT.W.H3C045.rowCoverage : CertData.H3.Bridge.RowCoverageLeaf`

`#print axioms` output for each exported declaration:

```text
AKLT.W.H3C045.main          [propext, Quot.sound]
AKLT.W.H3C045.planeBatchSound [propext, Quot.sound]
AKLT.W.H3C045.intervalEnd_cover [propext, Quot.sound]
AKLT.W.H3C045.intervalCheck_cover [propext, Quot.sound]
AKLT.W.H3C045.rowCoverage   [propext, Quot.sound]
```

## Build

Command: `export PATH="$HOME/.elan/bin:$PATH"; time lake build AKLT.W.H3C045.Main`

Result: successful (`Built AKLT.W.H3C045.Main`). The final build took 21.720 seconds wall time, including replay of project modules; the target module itself took 10 seconds.

## Open issues and deviations

- None for the proof.
- The brief requested an initial attempt using a different cheaper model. No model-switch tool was available in the session; delegation was prohibited by the task instructions, so the proof was completed with the active model.

## ORCH-SUMMARY

- Delivered the exact closed target theorem in `AKLT/W/H3C045/Main.lean`.
- Also proved reusable `PlaneBatchSoundLeaf` and `RowCoverageLeaf` helpers.
- `lake build AKLT.W.H3C045.Main` succeeds; all exported declarations use only `propext` and `Quot.sound`.
- No open proof obligations or residual statements.
- Limitation: the requested cheaper-model first attempt was unavailable without prohibited delegation.
- No orchestrator decision or additional input is needed.
