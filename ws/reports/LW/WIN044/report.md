STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN044/AKLT/W/WIN044/Main.lean) — proof of the requested theorem.
- [report.md](/home/ubuntu/aklt/reports/LW/WIN044/report.md) — this report.

## Exported declaration

`AKLT.W.WIN044.main : AKLT.Blueprint.Win.NearSeriesStatement`, where the statement is

```lean
∀ θ : ℝ, 0 < θ → θ < 1 →
  Summable (fun j : ℕ => θ ^ (max j 16 - 2)) ∧
  48 * (∑' j : ℕ, θ ^ (max j 16 - 2)) ≤ AKLT.Blueprint.Win.nearCost θ
```

The proof uses geometric summability after shifting the tail by 17. It evaluates the first 17 terms as `17 * θ^14`, writes the tail as `θ^15 / (1 - θ)`, and applies `θ / (1 - θ) ≤ 1 / (1 - θ)`.

## Axioms

Output of `#print axioms AKLT.W.WIN044.main`:

```text
'AKLT.W.WIN044.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.WIN044.Main`
- Result: successful; module reported `Built AKLT.W.WIN044.Main (4.7s)` (10.3s wall time for the build command).
- Axiom check command: `PATH="$HOME/.elan/bin:$PATH" lake env lean /tmp/WIN044Axioms.lean` (5.9s).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.WIN044.main` with the exact requested type.
- Added only `AKLT/W/WIN044/Main.lean` in the worktree and this report.
- The requested module build succeeded.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- No open issues or deviations.
