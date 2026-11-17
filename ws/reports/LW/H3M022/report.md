STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3M022/AKLT/W/H3M022/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H3M022/report.md`

## Exported declaration

`AKLT.W.H3M022.main : AKLT.Blueprint.H3.LongRowRegroupingStatement`

`#print axioms AKLT.W.H3M022.main` output:

```text
'AKLT.W.H3M022.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H3M022.Main` — passed; Lean module compile time reported as 7.4 seconds (12.9 seconds command elapsed).
- A separate `lake env lean /tmp/h3m022_axioms.lean` confirmed the declaration and axiom list.
- The build emitted nonblocking linter/deprecation warnings only.

## Proof outline and open issues

Split the length interval at 12 and shift the long lengths by `n = 12 + r`. For each long length, reindex words using its supplied equivalence, apply the supplied survival and contribution hypotheses, and reorder the finite sums. The extra `r = 0` continuation term vanishes because the surviving prefix endpoint avoids the target. No open issues or deviations.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3M022.main` with the requested type in `AKLT/W/H3M022/Main.lean`.
- Build passed; axioms are `[propext, Classical.choice, Quot.sound]`.
- No residual statements, limitations, or deviations.
- Orchestrator action: none.
