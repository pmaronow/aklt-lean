STATUS: PARTIAL

## Files

- `AKLT/W/REC098/Main.lean`
- `/home/ubuntu/aklt/reports/LW/REC098/report.md`

No existing project file was edited.

## Declarations

- `AKLT.W.REC098.FarCoverResidual : Prop` — for every first stopped trail and its protected endpoint, every second-trace U departure farther than two from that endpoint has a `CoveredDepartureV2` witness.
- `AKLT.W.REC098.secondDeparture_distance_pos` — for a second stopped trail and a protected first endpoint, its departure is at positive lattice distance from that endpoint.
- `AKLT.W.REC098.main_of_farCoverResidual (hcover : FarCoverResidual) : AKLT.Blueprint.Rec.TerminalExceptionLocationStatementV2` — assembles the target conclusion from the far-cover residual and the positive-distance lemma.

The requested unconditional declaration `AKLT.W.REC098.main` is not delivered. The remaining proof obligation is exactly `FarCoverResidual`: preserve the one-fixed-endpoint invariant through the second trace and construct the local pattern witness outside the endpoint's radius-two diamond.

## Axioms

The file's `#print axioms` output is:

```text
'AKLT.W.REC098.secondDeparture_distance_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC098.main_of_farCoverResidual' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted axioms. No `sorry`, `admit`, or added axiom is used.

## Build

Command: `export PATH="$HOME/.elan/bin:$PATH"; lake build AKLT.W.REC098.Main`

Result: successful; Lake reported `Built AKLT.W.REC098.Main` in 3.5 seconds (8965 jobs already present in the build graph).

## Open issue

Prove `AKLT.W.REC098.FarCoverResidual`. Its proof needs the prefix invariant for the second trace with the first endpoint as the only fixed defect, followed by local extraction of a `PatternData.Covered` witness that matches shared internal bonds and permits missing external factors and tip data.

## ORCH-SUMMARY

- Delivered a compiled partial module at `AKLT/W/REC098/Main.lean`.
- Proved positive distance from each second-trace departure to the first protected endpoint.
- Proved the requested statement conditionally as `main_of_farCoverResidual`.
- Unresolved exact residual: `AKLT.W.REC098.FarCoverResidual`.
- Unconditional `AKLT.W.REC098.main` is not present; status is PARTIAL.
- Exported theorem axioms are `[propext, Classical.choice, Quot.sound]`.
- Build command succeeded: `lake build AKLT.W.REC098.Main`.
- Orchestrator should pass on the fixed-defect prefix invariant and local shared-matcher pattern witness proof.
