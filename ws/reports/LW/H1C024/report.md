STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C024/AKLT/W/H1C024/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H1C024/report.md`

## Exported declaration

`AKLT.W.H1C024.main : AKLT.Cert.H1.Production.Leaves.metadataFacts`

The proof unpacks `MetadataAccepted` and `parametersCheck`. It derives the only
possible production outgoing indices, `0` and `2`, from the raw cases `0` and
`1`; the raw case `2` would give production index `4` and contradicts
`parametersCheck`. The site coordinates are discharged with named east and
north lookup lemmas. The denominator and positive width follow directly from
the corresponding checker components.

## Axioms

`#print axioms AKLT.W.H1C024.main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H1C024.Main`
- Result: success
- Elapsed time: 10.495 s real (reported by `time`)

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1C024.Main` with the exact requested theorem name and type.
- The raw west case is excluded because its doubled production index is `4`.
- Build succeeded; exported theorem uses only permitted axioms.
- No deviations or open issues.
