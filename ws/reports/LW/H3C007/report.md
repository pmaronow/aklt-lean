STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C007/AKLT/W/H3C007/Main.lean)
- Report: `/home/ubuntu/aklt/reports/LW/H3C007/report.md`

## Exported declaration

`AKLT.W.H3C007.main : CertData.H3.Bridge.LegalDirectionLeaf`

The proof uses `WalkRepresents` to identify the final position, incoming code, and used-bond list. It proves that `Walk.legal` is equivalent to avoiding every previous unoriented word bond, then matches the numeric reversal check with `WindowAdmissible`'s compass reversal condition.

## Axioms

`#print axioms AKLT.W.H3C007.main`:

```text
'AKLT.W.H3C007.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

`lake build AKLT.W.H3C007.Main` — succeeded; final cached invocation: 4.849 s real time (`Built`/`Replayed` 8976 jobs).

## Open issues and deviations

The `CodeEncodeLeaf` hint was not needed: this leaf's conclusion depends only on the represented position, incoming direction, and used bonds; the encoded word fields do not enter the equivalence. The requested cheaper-model first attempt could not be selected because this interface has no direct model-switch control. I did not use sub-agents, per the task instruction. No proof obligations remain.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C007/Main.lean` with `AKLT.W.H3C007.main` at the exact requested type.
- `lake build AKLT.W.H3C007.Main` succeeds; exported theorem axioms are `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit`, `native_decide`, or other forbidden proof escape is present.
- `CodeEncodeLeaf` was not needed for this semantics-only equivalence.
- Model selection was unavailable in the interface; no sub-agents were used, as instructed.
- No remaining proof blockers or decisions for the orchestrator.
