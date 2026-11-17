STATUS: PROVED FROM DEPS

## Files

- `/home/ubuntu/aklt/wt/LW_H3C025/AKLT/W/H3C025/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3C025/report.md`

## Exported declaration

`AKLT.W.H3C025.main : CertData.H3.Bridge.TableBoundsLeaf`

The proof specializes each checker row at `phaseKey (phaseCode φ) a.val`, extracts the cap and center-lane checks from `planeCheck`, and extracts the stored-plane cap check from the packed checker’s list of terms. The existing `AKLT.Gen.Packed.capCheck_sound` supplies `Fits`; no whole-certificate normalization or `native_decide` is used.

## Axioms

Output of `#print axioms AKLT.W.H3C025.main`:

```text
'AKLT.W.H3C025.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake env lean AKLT/W/H3C025/Main.lean` — succeeded (about 11 seconds).
- `time lake build AKLT.W.H3C025.Main` — succeeded; Lake reported 8.4 seconds for the target and 19.004 seconds total wall time including replayed dependencies.

## Open issues and deviations

- No proof issue remains.
- The brief requested a first attempt by a different cheaper model and also prohibited sub-agents. This environment exposed no model-switching or alternate-model invocation tool, so the proof was attempted directly in the active model; no sub-agent was used.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C025.main` with the exact requested type in `AKLT/W/H3C025/Main.lean`.
- Status: proved from existing dependencies; target build succeeded.
- `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
- No unresolved proof obligations or theorem-name deviations.
- Limitation: an alternate cheaper-model attempt was unavailable in the exposed tools; sub-agents were prohibited by the brief.
- Orchestrator action: none required.
