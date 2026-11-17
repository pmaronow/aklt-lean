STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_H3C033/AKLT/W/H3C033/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3C033/report.md`

## Exported declaration

`AKLT.W.H3C033.main : CertData.H3.Bridge.ShortValueLeaf`

This proves the closed `d:prefix-bound` statement for all valid exact data, represented prefixes of length at most 12, including zero-length prefixes.

## Proof outline

- Prove the exact item comparator agrees with `shortOrderLE`, including zero-reward infinity and chronological tie breaking; expose this as the internal `shortComparator : ShortComparatorLeaf`.
- Transport merge-sort order and membership from reward items to first visits, using pairwise transitivity, totality, and antisymmetry.
- Prove the exact rational scaling recurrence for `exposureNumerator`, then split the common denominator exponent 36 into prefix depth, twice the item count, and the remaining padding exponent.
- Use the represented trail base weight and `kernelOrdering` to identify the resulting value with `closedContribution`.

No whole-certificate normalization or `native_decide` is used.

## Axioms

`#print axioms AKLT.W.H3C033.main`:

```text
'AKLT.W.H3C033.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H3C033.Main`
- Result: success (`Built AKLT.W.H3C033.Main`)
- Wall time: 13.5 seconds; Lake reported 7.8 seconds for the module.

## Open issues and deviations

- The brief requested the first attempt use a different cheaper model. The available runtime did not provide a direct model-switch control, and the task forbids sub-agents, so the proof was completed with the active model.
- No mathematical residuals remain.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C033/Main.lean` with `AKLT.W.H3C033.main : CertData.H3.Bridge.ShortValueLeaf`.
- The proof reuses the comparator leaf proved internally, exact merge-sort facts, and the represented prefix hypotheses.
- `lake build AKLT.W.H3C033.Main` passed; module build time 7.8s (13.5s wall time).
- `#print axioms`: `[propext, Classical.choice, Quot.sound]` only.
- No residual statements or mathematical open issues.
- Deviation: no direct control for selecting the requested cheaper model was available; sub-agents were prohibited.
- Orchestrator action: accept the proof; note the model-selection deviation if campaign policy requires it.
