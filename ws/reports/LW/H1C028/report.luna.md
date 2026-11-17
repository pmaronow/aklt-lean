STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C028/AKLT/W/H1C028/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H1C028/report.md`

## Delivered declarations

- `patternStatusDigits (π : PatternData) (reflect : Bool) : List Nat`
- `patternEdgeDigits (π : PatternData) (reflect : Bool) : List Nat`
- `Residual_unreflectedEdgeDigits : Prop`: every checked input's unreflected pattern edge digits equal `rawEdges.map Bool.toNat`.
- `Residual_unreflectedStatusDigits : Prop`: every checked input's unreflected pattern status digits, with zero-degree deletion, equal `rawStatusDigits`.
- `Residual_reflectedEdgeDigits : Prop`: reflected pattern edge digits equal the `reflectEdges` permutation of raw edge digits.
- `Residual_reflectedStatusDigits : Prop`: reflected pattern status digits equal the `reflectSites` permutation of raw status digits.
- `main_of_residuals` has type
  `Residual_unreflectedEdgeDigits → Residual_unreflectedStatusDigits → Residual_reflectedEdgeDigits → Residual_reflectedStatusDigits → AKLT.Cert.H1.Production.Leaves.representativeCode`.

The local proofs also establish the center, all eight cycle, and all four tip bond correspondences individually. In particular, the center proof retains the south-bond omission, and the tip proof uses the covering-tip exception. The paper’s `d:pattern` definition in `sec6-walks.tex` states the corresponding non-arrival, bond-agreement, and tip rules.

The exact requested declaration `AKLT.W.H1C028.main : AKLT.Cert.H1.Production.Leaves.representativeCode` is not delivered: the four list-level residuals remain unproved. The largest remaining gap is the status-list residual, which must connect deletion of zero-degree compiled sites to the raw incident-edge test.

## Axioms and build

`#print axioms AKLT.W.H1C028.main_of_residuals` reports:

```text
'AKLT.W.H1C028.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Build command: `lake build AKLT.W.H1C028.Main` — succeeded, 19.2 seconds wall time (the task module reported 13 seconds). No forbidden proof escape hatches are present. `Main.lean` is the only file in the task directory and is transitively imported by the module target.

## Open issues

- Prove `Residual_unreflectedEdgeDigits` by assembling the sixteen proved local bond facts into the list equality.
- Prove `Residual_unreflectedStatusDigits` by matching `patternDegree = 0` to the raw incident-edge disjunction after isolated-site deletion.
- Prove `Residual_reflectedEdgeDigits` and `Residual_reflectedStatusDigits` with the fixed outgoing-reflection convention.
- Then export the exact requested `AKLT.W.H1C028.main` theorem.

## ORCH-SUMMARY

- Delivered a compiling partial module and `main_of_residuals`.
- Proved local correspondence for 4 center, 8 cycle, and 4 tip bonds.
- Residual names still open: `Residual_unreflectedEdgeDigits`, `Residual_unreflectedStatusDigits`, `Residual_reflectedEdgeDigits`, `Residual_reflectedStatusDigits`.
- The requested exact theorem `AKLT.W.H1C028.main` remains open.
- `main_of_residuals` uses only `[propext, Classical.choice, Quot.sound]`.
- Orchestrator should pass on the four residuals or continue the list/status/reflection proofs.
