STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_GAP025/AKLT/W/GAP025/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP025/report.md`

## Exported declaration

```lean
theorem AKLT.W.GAP025.main : AKLT.Blueprint.Gap.ProductPoincareTransportStatement
```

The proof transports an arbitrary test function by precomposition with the inverse configuration equivalence. It proves equality of the means and variances by finite-sum reindexing, proves the singleton conditional expectation identity using `coordinate_eq`, reindexes each singleton Dirichlet form, and finally reindexes the site sum.

## Axioms

Output of `#print axioms AKLT.W.GAP025.main`:

```text
'AKLT.W.GAP025.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's standard permitted axioms.

## Build

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.GAP025.Main`
- Result: successful (`Built AKLT.W.GAP025.Main`)
- Reported module build time: 3.5 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP025.main` with the exact requested type.
- The requested module builds successfully.
- Axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements or deviations remain.
