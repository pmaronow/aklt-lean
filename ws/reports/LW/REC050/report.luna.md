STATUS: PARTIAL

## Files

- `AKLT/W/REC050/Main.lean`
- `/home/ubuntu/aklt/reports/LW/REC050/report.md`

## Exported declarations

- `AKLT.W.REC050.main (h₁ : Residual_1) (h₂ : Residual_2) (h₃ : Residual_3) : AKLT.Blueprint.Rec.KeptInvariantStatement`.
- `AKLT.W.REC050.MutualKept D`: active adjacent sites in `D` have equivalent kept flags.
- `AKLT.W.REC050.residual_4`: for every `PairSetup` normalized trail prefix, active adjacent sites have equivalent kept flags.
- `AKLT.W.REC050.residual_5`: for every `PairSetup` normalized trail prefix and `i < j`, the status of the `i`th vertex is not U.
- `AKLT.W.REC050.Residual_1`: every prefix network is Auxiliary.
- `AKLT.W.REC050.Residual_2`: every nonlive U site in a prefix has kept set `neighbours x ∩ p.G`.
- `AKLT.W.REC050.Residual_3`: every nonlive D site in a prefix has exactly two kept flags.

The binders common to each residual are `p : PairSetup`, `T : Finset Plane`, `n : ℕ`, `w : DirectionWord n`, a proof of `StoppedNetworkTrail p.normalized p.u T w`, and `j ≤ n`. The complete declarations are in [Main.lean](/home/ubuntu/aklt/wt/LW_REC050/AKLT/W/REC050/Main.lean:212).

The requested theorem name and conclusion are present, but `main` still has three residual hypotheses, so it is not the requested closed proof. Each residual is a single conjunction component of the frozen statement, with the shared trail and prefix quantifiers made explicit. No counterexample or missing premise was found; status is partial, not false.

`residual_4` proves the mutual-flag clause: normalization only erases the flag to the removed, inactive centre, and each trace step erases both flags on its traversed bond. `residual_5` proves nonreturn to U directly from the recursive trace definition: each departure sets the site's status to D or X, and later steps cannot turn a non-U status into U.

The unresolved induction must establish Auxiliary validity and the U/D kept-set cardinalities at every prefix. Its initial case needs the paper’s geometric fact that `p.interior` implies all four neighbors of `p.u` belong to `p.G`; the induction then separates U departure, initial D departure, later D departure, and arrival.

## Axioms

`#print axioms AKLT.W.REC050.main`:

```text
'AKLT.W.REC050.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`#print axioms AKLT.W.REC050.residual_4`:

```text
'AKLT.W.REC050.residual_4' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`#print axioms AKLT.W.REC050.residual_5`:

```text
'AKLT.W.REC050.residual_5' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the allowed Lean axioms listed in the task brief.

## Build

- `lake build AKLT.W.REC050.Main` — succeeded; Lean reported 4.1 seconds for the module (8.90 seconds wall time for the full Lake invocation).
- `lake env lean /tmp/rec050-axioms.lean` checked all three exported theorems after the final build.

## Open issues

- Prove `AKLT.W.REC050.Residual_1` from the initial normalized network and trace transitions.
- Prove `AKLT.W.REC050.Residual_2`, including the initial departure and U arrivals.
- Prove `AKLT.W.REC050.Residual_3`, including initial D and later D arrivals/departures.
- Remove the three hypotheses from `AKLT.W.REC050.main` to obtain the requested closed theorem type.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC050/Main.lean` and this report.
- `AKLT.W.REC050.residual_4` proves mutual kept flags through every prefix.
- `AKLT.W.REC050.residual_5` proves previously departed sites never return to U.
- `AKLT.W.REC050.main` derives the frozen statement from `Residual_1`, `Residual_2`, and `Residual_3`.
- The requested closed theorem remains incomplete; `main` still takes those three residuals.
- Open exact declarations: `AKLT.W.REC050.Residual_1`, `AKLT.W.REC050.Residual_2`, `AKLT.W.REC050.Residual_3`.
- No false-premise counterexample was identified.
- `lake build AKLT.W.REC050.Main` succeeds.
- Exported theorem axioms are `propext`, `Classical.choice`, and `Quot.sound`.
