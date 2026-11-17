STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_MOM033/AKLT/W/MOM033/Main.lean`

## Exported declarations

- `AKLT.W.MOM033.main : AKLT.Blueprint.Mom.OneSiteConditionalReductionStatement`
- `AKLT.W.MOM033.normalized_indicator_sum`, the finite normalized indicator-sum identity used to cancel the global partition function:
  ```lean
  ∀ {α : Type} [Fintype α] (E : α → Prop) [DecidablePred E]
    (w g : α → ℝ), (∑ y, w y) ≠ 0 →
    (∑ x, if E x then normalize w x * g x else 0) =
      (∑ x, if E x then w x * g x else 0) / (∑ y, w y)
  ```

The proof enumerates the incident bonds as `Fin k`, with `k ≤ 3`, and assigns each its exterior spin vector. Distinct endpoints from `D.Valid` make every incident factor depend on the varying spin and a fixed neighbour. All remaining site, bond, and pin factors are collected into a common constant on the fibre. Direct coordinate estimates establish nonnegativity; positive fibre mass then gives a positive local normalizer and permits cancellation.

## Axiom audit

`#print axioms AKLT.W.MOM033.main`:

```text
'AKLT.W.MOM033.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.MOM033.Main` — succeeded; Lake reported module build time 7.1s (wall time 11.9s).
- `lake env lean /tmp/mom033_axioms.lean` — succeeded; confirmed the exported type and axiom list above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/MOM033/Main.lean` with the exact requested theorem and type.
- Status is `PROVED`; the requested Lake target builds.
- Axiom footprint: `propext`, `Classical.choice`, `Quot.sound`.
- The finite normalization identity is also exported as `AKLT.W.MOM033.normalized_indicator_sum`.
- No open proof obligations or deviations remain.
