STATUS: PARTIAL

## Files

- `AKLT/W/H3C032/Main.lean`

## Delivered declaration

- `AKLT.W.H3C032.ResidualScaledComparator : Prop` is a closed arithmetic residual. It states that, given `ExactValid` and the two item-to-word equalities for time, straightness, and normalized reward, `itemLE` agrees with `shortOrderLE`.
- `AKLT.W.H3C032.main_of_residual (hcore : ResidualScaledComparator) : CertData.H3.Bridge.ShortComparatorLeaf` reduces the requested leaf to that residual. The proof extracts the relevant scalar facts from `PrefixRepresents`.

The requested closed declaration `AKLT.W.H3C032.main : CertData.H3.Bridge.ShortComparatorLeaf` is not delivered. The natural-number cross-product versus rational-score equivalence in `ResidualScaledComparator` remains unproved, including its zero-reward and chronological-tie cases.

## Axioms

`#print axioms AKLT.W.H3C032.main_of_residual`:

```text
[propext, Classical.choice, Quot.sound]
```

These are the permitted Lean axioms. The residual itself is a `def`, not an axiom or theorem hypothesis hidden in a claimed closed proof.

## Build

- `lake build AKLT.W.H3C032.Main` — successful; target reported 9.1s, full command wall time 20.44s.
- An earlier compile caught and removed an invalid attempt to use the residual proposition itself as evidence. The successful build has no errors.

## Open issue and limitation

The trap note requires the first written proof attempt to come from a different cheaper model, while this session provides no model-routing tool and explicitly disallows sub-agents. I therefore did not write the residual arithmetic proof. The repository's exact edge cases must be preserved when completing it: zero reward has infinity ordering, equal rational scores use chronological index, and Nat subtraction/cross-products must be shown to match the rational comparison under `ExactValid`.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C032/Main.lean` with the compiled reduction `AKLT.W.H3C032.main_of_residual`.
- Open: prove `AKLT.W.H3C032.ResidualScaledComparator`.
- Open: export the exact requested `AKLT.W.H3C032.main : CertData.H3.Bridge.ShortComparatorLeaf` after that residual is proved.
- The representation extraction is proved from `PrefixRepresents`; the exact comparator arithmetic is not.
- No `sorry`, `admit`, `axiom`, or `native_decide` is used.
- No sub-agent was used. The required cheaper-model first attempt could not be routed in this session; pass the residual to that model before further written proof work.
- Successful build: `lake build AKLT.W.H3C032.Main`; `main_of_residual` uses only `propext`, `Classical.choice`, and `Quot.sound`.
