STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M024/AKLT/W/H1M024/Main.lean)

## Exported declarations

- `AKLT.W.H1M024.main : AKLT.Blueprint.H1.ReducedFactorStructureStatement`
- Supporting declarations in `AKLT.W.H1M024`: token degree/support predicates and multiplication lemmas; formal-dot support lemmas; single-factor, bond-product, and group-product structure lemmas; local evaluation homomorphism lemmas; and `dot_mulVec_orthogonal`. These establish the three conjuncts of the target directly from the definitions.

## Proof outline

Each formal dot product has support only on its two coordinate variables. For a token factor, every supported monomial has total token degree at most one. The retained corner pairs use two distinct tokens, and distinct template groups use disjoint token sets. Induction over the finite products therefore proves local vector affineness and support inclusion in `reductionVectors`. The invariance conjunct follows by evaluating the factors and applying `R.transpose * R = 1` to each dot product.

## Axioms

`#print axioms AKLT.W.H1M024.main`:

```text
'AKLT.W.H1M024.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H1M024.Main` — succeeded; initial build reported 11 s for the module and 18.869 s total, followed by a final cached build in 5.307 s.
- `lake env lean /tmp/h1m024-axioms.lean` — succeeded; printed the axiom list above.
- Scanned the delivered directory for forbidden proof escapes (`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque`, `implemented_by`, `extern`, `macro_rules`, `debug.skipKernelTC`, and `maxHeartbeats 0`); no matches.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1M024/Main.lean` with `AKLT.W.H1M024.main` at the exact requested type.
- Proved local vector affineness, orthogonal invariance, and support inclusion from the reduced integrand's definitions.
- Build passed with `lake build AKLT.W.H1M024.Main`.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements, limitations, or deviations remain.
