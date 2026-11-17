STATUS: PROVED

## Files

- `AKLT/W/H1M058/Main.lean` — contains the proof. No existing project files were changed.

## Exported declaration

```lean
theorem AKLT.W.H1M058.main :
  AKLT.Blueprint.H1.InversionPolynomialStatementV2
```

The proof represents inversion as a ring homomorphism sending each variable to its signed copy. The image of each monomial keeps its exponent vector, so its support is contained in the original support; this transfers vector-affineness and the `J` support condition. Evaluating the substituted polynomial on the sign-substituted vectors cancels the signs. The argument does not require `I ⊆ J`.

## Axioms

Output of `#print axioms AKLT.W.H1M058.main`:

```text
'AKLT.W.H1M058.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H1M058.Main`
- Result: successful; module build reported 13s (command completed in about 18s, including Lake overhead).

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/H1M058/Main.lean`.
- Build succeeds with `lake build AKLT.W.H1M058.Main`.
- Axioms are `[propext, Classical.choice, Quot.sound]`.
- No `I ⊆ J` premise is used; no limitations or follow-up decisions remain.
