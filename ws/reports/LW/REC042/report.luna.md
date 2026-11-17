STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC042/AKLT/W/REC042/Main.lean)
- [Moments.lean](/home/ubuntu/aklt/wt/LW_REC042/AKLT/W/REC042/Moments.lean)

## Delivered declarations

- `AKLT.W.REC042.moment_second`: the explicit icosahedral second coordinate moment.
- `AKLT.W.REC042.moment_fourth`: the fourth coordinate tensor identity, proved by finite coordinate cases and the golden-ratio/radius identities.
- `AKLT.W.REC042.startLegFree`: proves an admissible start outside the protected layer has no original pin legs.
- `AKLT.W.REC042.ResidualSiteMomentStatement`: the pair of U and D one-site moment identities required by the suggested route.
- `AKLT.W.REC042.ResidualPartitionFactorizationStatement`: the finite partition reindexing and one-step trace identity, under explicit local hypotheses and the site moment statement.
- `AKLT.W.REC042.main` proves `AKLT.Blueprint.Rec.CoordinateStepStatement` from the two named residual statements. It does not have the requested closed type because those residuals remain unproved.

The exported theorem currently has this conditional type:

```lean
AKLT.W.REC042.main :
  AKLT.W.REC042.ResidualSiteMomentStatement →
  AKLT.W.REC042.ResidualPartitionFactorizationStatement →
  AKLT.Blueprint.Rec.CoordinateStepStatement
```

`ResidualSiteMomentStatement` is exactly `UStepMomentStatement ∧ DStepMomentStatement`. `ResidualPartitionFactorizationStatement` assumes that site-moment pair and states the coordinate partition identity for any locally valid network, active distinct endpoints, a leg-free departure, and the corresponding U/D incident-degree bound.

## Axioms

`#print axioms` output:

```text
'AKLT.W.REC042.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC042.startLegFree' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC042.moment_second' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC042.moment_fourth' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No forbidden proof escape hatches are used.

## Build

- `lake build AKLT.W.REC042.Main` — final invocation successful in 3.6 s; the helper module compiled in 74 s.
- The axiom audit via `lake env lean /tmp/REC042Axioms.lean` — successful, 3.8 s.

## Open issues

The exact requested declaration `AKLT.W.REC042.main : AKLT.Blueprint.Rec.CoordinateStepStatement` is not yet proved. The remaining obligations are exactly:

1. `AKLT.W.REC042.ResidualSiteMomentStatement` — derive the finite U/D site moment expansions from the second- and fourth-moment identities.
2. `AKLT.W.REC042.ResidualPartitionFactorizationStatement` — split the finite network partition at the moving coordinate, extract incident factors, and identify the resulting sums with the `traceStep` partitions.

The fourth-moment proof uses `set_option maxHeartbeats 800000` because its direct 81-case coordinate calculation exceeds Lean's default heartbeat limit. No existing project files were edited.

## ORCH-SUMMARY

- Added `AKLT/W/REC042/Main.lean`, `AKLT/W/REC042/Moments.lean`, and this report.
- Proved the second and fourth coordinate moment identities and the interior-start no-leg fact.
- Added a conditional `main` reduction to two transparent residual propositions.
- Open: `ResidualSiteMomentStatement`, `ResidualPartitionFactorizationStatement`.
- Limitation: `AKLT.W.REC042.main` still takes these residuals as hypotheses; the requested closed theorem is not delivered.
- Build: `lake build AKLT.W.REC042.Main` succeeded; allowed axioms only.
- Orchestrator should treat this leaf as partial and continue with the two listed obligations.
