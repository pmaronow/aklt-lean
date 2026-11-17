STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC002/AKLT/W/REC002/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/REC002/report.md)

## Exported declarations

- `golden_sq : goldenRatio ^ 2 = goldenRatio + 1`
- `golden_pos : 0 < goldenRatio`
- `radius_sq : icoRadius ^ 2 = goldenRatio + 2`
- `radius_ne : icoRadius ≠ 0`
- `moment_coordinate (i) : moment (fun v => v i) = 0`
- `moment_pair_diag (i) : moment (fun v => v i ^ 2) = 1 / 3`
- `moment_coord_pair (i j) : moment (fun v => v i * v j) = if i = j then 1 / 3 else 0`
- `moment_coord_triple (i j k) : moment (fun v => v i * v j * v k) = 0`
- `main_of_residuals (hPre : Residual_PreStep) (hPost : Residual_PostStep) : AKLT.Blueprint.Rec.ThreeFactorizationStatement`

`Residual_PreStep` and `Residual_PostStep` are closed `Prop` definitions, each containing one of the two equalities in the target under the target's hypotheses. `main_of_residuals` proves the target from these two explicit residuals. The required declaration `AKLT.W.REC002.main` is not delivered because neither residual has been proved.

## Axioms

`#print axioms` was run on every exported theorem listed above. Each output was:

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

No forbidden axiom or placeholder was introduced.

## Build

Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC002.Main`

Result: success, 28.1 seconds (first full build; subsequent replay took 5.1 seconds).

## Open issues

- `Residual_PreStep` needs the finite active-spin sum reindexing at the unpinned U departure, a proof that the interior departure has no original legs, and the incident-bond product identification with `{o, f, g}`. The explicit coordinate moments are present, but are not yet connected to this partition sum.
- `Residual_PostStep` needs the corresponding reindexing for `traceStep`, identification of the two retained incident bonds, and the D-site local integration giving `responseJ`.
- Consequently, `AKLT.W.REC002.main` remains open. The residuals are not hypotheses of the requested theorem; they are named proof obligations, and no result is claimed without proving them.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC002/Main.lean` with exact low-order coordinate moment proofs and a compiled reduction from `Residual_PreStep` and `Residual_PostStep` to the target.
- Open: `AKLT.W.REC002.Residual_PreStep` and `AKLT.W.REC002.Residual_PostStep`.
- The requested `AKLT.W.REC002.main` is not proved or declared; status is `PARTIAL`.
- Build succeeded with `lake build AKLT.W.REC002.Main`; checked theorem axioms are only `propext`, `Classical.choice`, `Quot.sound`.
- Orchestrator should either accept this as partial progress or assign completion of the two partition factorizations.
