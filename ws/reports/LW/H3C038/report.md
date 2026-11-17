STATUS: PROVED

## Files

- `AKLT/W/H3C038/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3C038/report.md`

## Declarations

- `AKLT.W.H3C038.main : CertData.H3.Bridge.RationalCeilingLeaf`
- Private helper `numericScale : CertData.H3.Bridge.NumericScaleLeaf`

The helper puts `resultValue` over `finalDenominator`. The main proof unfolds `ceilingCheck`, casts its checked Nat inequality to `ℚ`, and divides by the positive final denominator.

## Axioms

`#print axioms main`:

```text
'AKLT.W.H3C038.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are allowed axioms. No forbidden proof escapes or computation tactics are used.

## Build

- `lake build AKLT.W.H3C038.Main` — succeeded; command wall time 19.4 s, target build reported 7.6 s.

## Open issues

None. The requested first attempt on a different cheaper model could not be carried out: no model-switch tool is available in this session, and the brief also prohibits sub-agents.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C038.main` with the exact requested type.
- Proved the reusable numeric-scale identity as a private helper, then used the ceiling check's Nat inequality.
- Build succeeded with `lake build AKLT.W.H3C038.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- No remaining proof issues.
- Limitation: first attempt on a different cheaper model was unavailable in-session; no sub-agents were used, respecting the brief's rule.
- Orchestrator action: none required.
