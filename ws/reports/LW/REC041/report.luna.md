STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC041/AKLT/W/REC041/Main.lean)

## Delivered declarations

- `AKLT.W.REC041.Residual_tracePrefixNormalizersPositive : Prop`: for every admissible auxiliary network, stopped trail, pin choice, and prefix index `j ≤ n`, the prefix partition is strictly positive.
- `AKLT.W.REC041.main_of_positive_prefixes (hPos : Residual_tracePrefixNormalizersPositive) : AKLT.Blueprint.Rec.TraceTelescopeStatement`.
- `AKLT.W.REC041.main (hPositivePrefixes : Residual_tracePrefixNormalizersPositive) : AKLT.Blueprint.Rec.TraceTelescopeStatement`.

The proof reduces the identity to a list telescope and cancels consecutive partition normalizers. The `j ≤ n` residual includes the length-zero case, where the left side is `Z / Z` and the product is empty.

## Axioms

`#print axioms main`:

```text
'AKLT.W.REC041.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC041.Main` — succeeded, 5.0 s.
- No tests were run.

## Open issue

The required unconditional declaration `AKLT.W.REC041.main : AKLT.Blueprint.Rec.TraceTelescopeStatement` is not proved. The remaining obligation is exactly `Residual_tracePrefixNormalizersPositive`. `AKLT.Blueprint.Rec.NetworkPositiveStatement` is only a `def` in the imported blueprint, not a proved lemma available to this leaf. Proving strict positivity for every traced prefix from the explicit auxiliary-network hypotheses remains open.

## ORCH-SUMMARY

- Delivered a compiled conditional telescope proof in `AKLT/W/REC041/Main.lean`.
- The exported `main` still takes `Residual_tracePrefixNormalizersPositive`; it therefore does not yet have the requested unconditional type.
- The residual states strict positivity of every prefix partition, including the initial partition in the zero-length case.
- Build succeeded with Lean 4.35.0-rc2 using `lake build AKLT.W.REC041.Main` (5.0 s).
- Axioms for conditional `main`: `propext`, `Classical.choice`, `Quot.sound`.
- No existing files were modified; no tests were run.
- Open exact name: `AKLT.W.REC041.Residual_tracePrefixNormalizersPositive`.
- Orchestrator decision: prove that residual or pass its proof into this leaf before accepting it as complete.
