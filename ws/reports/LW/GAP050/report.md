STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP050/AKLT/W/GAP050/Main.lean) — finite pushforward identity and the requested proof.
- [report.md](/home/ubuntu/aklt/reports/LW/GAP050/report.md) — this report.

## Exported declaration

`AKLT.W.GAP050.main : AKLT.Blueprint.Gap.TraceDisagreementStatement`

The proof first rewrites disagreement under `c` as the path-law sum of endpoint disagreement indicators, using the supplied equality `c.mass = marginal w endpoint` with exactly `endpoint t = t (Fin.last m)`. It then compares each path summand with its no-success indicator. For positive-mass paths, the assumed success implication gives endpoint agreement; zero-mass paths contribute zero by nonnegativity of `w`.

Private helper: `AKLT.W.GAP050.sum_not_event_marginal`, which identifies an event sum under a finite pushforward with the corresponding source-space sum.

## Axioms

`#print axioms AKLT.W.GAP050.main`:

```text
'AKLT.W.GAP050.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are within the permitted axiom set.

## Build

- Command: `lake build AKLT.W.GAP050.Main`
- Result: successful; module compile reported 4.2 s, command wall time 9.35 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered and compiled `AKLT.W.GAP050.main` at the exact requested name and type.
- Endpoint coupling is used through the supplied exact pushforward equality.
- Positive-mass paths use the success implication; zero atoms vanish by `Probability w` nonnegativity.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound` only.
- Open issues: none; no deviations.
