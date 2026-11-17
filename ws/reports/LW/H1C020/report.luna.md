STATUS: PARTIAL

## Files

- `/home/ubuntu/aklt/wt/LW_H1C020/AKLT/W/H1C020/Main.lean`

## Exported declarations

- `AKLT.W.H1C020.Residual_reducedCurrent`: the moment-polynomial identity restricted to `Representation.reduced` and `next = false`.
- `AKLT.W.H1C020.Residual_reducedNext`: the identity restricted to `Representation.reduced` and `next = true`.
- `AKLT.W.H1C020.Residual_unreducedCurrent`: the identity restricted to `Representation.unreduced` and `next = false`.
- `AKLT.W.H1C020.Residual_unreducedNext`: the identity restricted to `Representation.unreduced` and `next = true`.
- `AKLT.W.H1C020.main (hRC) (hRN) (hUC) (hUN) : AKLT.Cert.H1.Production.Leaves.momentPolynomial`.
  The proof composes the four residuals by cases on representation and mode. It does not prove the requested unconditional theorem.

Each residual is a closed proposition in `Main.lean`, with the same covered-pattern, group-inversion, network-geometry, and outgoing-site premises as the target, restricted to one of its four representation/mode cases.

## Axioms

`#print axioms AKLT.W.H1C020.main`:

```text
[propext, Classical.choice, Quot.sound]
```

These are Lean’s standard allowed axioms.

## Build

- `lake build AKLT.W.H1C020.Main` — passed; Lean reported `Built AKLT.W.H1C020.Main (4.8s)`.

## Open issue

The four residual identities remain unproved. Each requires comparing the packed transfer expansion `networkNumerator` with the contraction of `reducedIntegrand`, including the correct tip factors, both leaf-representation choices, the next-mode center exclusion, and the original-token inversion signs. The existing proved monomial contraction lemma does not establish this packed-network bridge. No `sorry`, `admit`, or axiom was added.

## ORCH-SUMMARY

- Delivered a compiling conditional composition theorem and four closed residual propositions in `AKLT/W/H1C020/Main.lean`.
- The requested unconditional `AKLT.W.H1C020.main : AKLT.Cert.H1.Production.Leaves.momentPolynomial` is not proved; current `main` takes all four residuals as hypotheses.
- Open declarations: `Residual_reducedCurrent`, `Residual_reducedNext`, `Residual_unreducedCurrent`, `Residual_unreducedNext`.
- Main remaining work: prove the packed-network to reduced-integrand contraction identity in all four cases, including inversion and tip/leaf factors.
- No existing files were edited; no soundness escape hatch was used.
