STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_GAP010/AKLT/W/GAP010/Main.lean`

## Exported declaration

`AKLT.W.GAP010.main : AKLT.Blueprint.Gap.ConditionalPatchCouplingStatement`

The proof forms a maximal-overlap coupling of the `B` marginals, lifts it by independently completing each law conditional on its `B` restriction, and uses a fixed assignment on `A`. The assignment bound gives conditional success at least `α^|A|` in each completion. The product success mass is therefore at least `t * α^(2*|A|)`, which implies the required disagreement bound. Empty sets and zero residual overlap are covered by the finite-sum and zero-denominator branches.

## Axioms

`#print axioms AKLT.W.GAP010.main`:

```text
'AKLT.W.GAP010.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.GAP010.Main` — succeeded; module build 8.1 s, command wall time 15.362 s.
- `lake env lean /tmp/gap010_axioms.lean` — succeeded and printed the axiom list above.

The build reports four deprecation warnings for `if_true` and `if_false` simp lemmas in residual-coupling marginal calculations. They do not affect compilation or proof soundness.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP010.main` with the exact requested statement in `AKLT/W/GAP010/Main.lean`.
- `lake build AKLT.W.GAP010.Main` succeeds.
- Axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- Proof uses maximal `B` overlap, independent conditional full-law completions, and a common prescribed `A` assignment.
- No plane geometry or stopping argument is part of this reusable leaf.
- Four harmless deprecation warnings remain for `if_true`/`if_false` simplification lemmas.
- No open proof obligations or orchestration decisions remain.
