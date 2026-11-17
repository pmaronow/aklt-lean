STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP001/AKLT/W/GAP001/Main.lean)

## Exported declaration

`AKLT.W.GAP001.main : AKLT.Blueprint.Gap.FibreNormalizationStatement`

The exact target type is the frozen statement:

```lean
∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : ι → Type)
  [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
  (p : Weight (Config S)), PositiveProbability p → ∀ U σ,
  Probability (fibre p U σ) ∧ PositiveProbability (blockLaw p U σ) ∧
    ∀ f, conditionalExpectation p U f σ = complexMean (fibre p U σ) f
```

The proof shows that the exterior fibre contains the input configuration, so its normalizing sum is positive. It proves the fibre law is a probability, constructs a full configuration extending each block assignment to prove every block atom has positive mass, and sums the pushforward back to establish block normalization. The conditional expectation identity follows by expanding both finite sums over the same exterior fibre.

## Axioms

Output of `#print axioms AKLT.W.GAP001.main`:

```text
'AKLT.W.GAP001.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `lake build AKLT.W.GAP001.Main`

Result: successful. Lake reported the module build at 4.4 seconds (wall time 9.7 seconds including command startup).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP001.main` with the exact requested type in `AKLT/W/GAP001/Main.lean`.
- Proved the fibre normalization, strict block atom positivity, block normalization, and conditional mean identity from the statement hypotheses.
- `lake build AKLT.W.GAP001.Main` succeeds.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, helper files, or deviations remain.
