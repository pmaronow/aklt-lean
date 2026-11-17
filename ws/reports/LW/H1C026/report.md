STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_H1C026/AKLT/W/H1C026/Main.lean`

## Exported declaration

`AKLT.W.H1C026.main : AKLT.Cert.H1.Production.Leaves.enumerationSoundness`

The helper lemmas and the `LawfulBEq RawOption` instance are private to the file.

## Proof outline

Induction through `CoverageRowsAccepted` retrieves `CoverageAccepted` for the requested axial row. The compatible first corner belongs to `cornerOptions`; its position selects one of the eight accepted `coverageShard` obligations. The three nested `List.all` checks then establish `markedCheck` for the requested four corners. At the live outgoing index, the marked check reduces to `isSome` for the catalogue lookup under `rawKey`.

The shard's early all-X skip is handled using the live outgoing-bond premise: when the first three axial statuses are zero, each of the first three center edges is false, contradicting the assumed live edge at an index below 3.

## Axioms

Output of `#print axioms AKLT.W.H1C026.main`:

```text
'AKLT.W.H1C026.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted Lean axioms.

## Build

Command: `lake build AKLT.W.H1C026.Main`

Result: succeeded; command wall time 14.3 seconds. Lake replayed cached dependencies and built the target. The target emitted only linter deprecation/unused-simp warnings; there are no proof errors.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C026/Main.lean` with `AKLT.W.H1C026.main` proving the requested closed statement.
- Build succeeded with `lake build AKLT.W.H1C026.Main`.
- Exported theorem axioms: `propext`, `Classical.choice`, `Quot.sound`.
- The all-X shard skip is discharged using the live outgoing-bond hypothesis.
- No residual claims, false-status concerns, or open issues.
- No deviation from the requested theorem name or type.
