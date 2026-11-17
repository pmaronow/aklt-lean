STATUS: PARTIAL

## Files

- `AKLT/W/H3C035/Main.lean`

## Delivered declarations

- `AKLT.W.H3C035.earlySound_depth_zero` proves the depth-zero instance of `CertData.H3.Bridge.EarlySoundLeaf`.
- `AKLT.W.H3C035.ResidualDepth1` through `ResidualDepth12` are closed, fixed-depth instances of the remaining leaf obligation.
- `AKLT.W.H3C035.main_of_residuals` proves `CertData.H3.Bridge.EarlySoundLeaf` from those twelve fixed-depth residuals and the proved depth-zero case. The required unconditional declaration `AKLT.W.H3C035.main : CertData.H3.Bridge.EarlySoundLeaf` is not delivered.

## Axioms

`#print axioms AKLT.W.H3C035.earlySound_depth_zero`:

```text
[propext, Classical.choice, Quot.sound]
```

`#print axioms AKLT.W.H3C035.main_of_residuals`:

```text
[propext, Classical.choice, Quot.sound]
```

No forbidden proof escape or `sorry` is used.

## Build

- Command: `lake build AKLT.W.H3C035.Main`
- Result: success
- Timing: 13.9 seconds wall time in the final successful build

## Open issues

The fixed-depth residuals for depths 1 through 12 remain unproved. Closing them requires, among other things, proofs of `CertData.H3.Bridge.PrefixStepLeaf` and `CertData.H3.Bridge.ShortValueLeaf`; in this worktree those are only definitions of closed propositions, not available theorems. The remaining DFS argument must establish that the accepted early-DFS paths enumerate exactly the first-direction closed trails counted by `firstDirectionPartialRow`, with their integer `shortValue` values matching `closedContribution`. No whole-certificate normalization or `native_decide` route was used.

The brief requested that the first attempt use a different cheaper model. No model-switch tool is available in this session, and the brief also explicitly forbids sub-agents, so that instruction could not be carried out.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C035/Main.lean` and this report.
- Proved depth zero; `main_of_residuals` assembles the target from `ResidualDepth1` through `ResidualDepth12`.
- Open: all twelve positive-depth residuals and the exact unconditional theorem `AKLT.W.H3C035.main`.
- The interface defines, but does not prove, `PrefixStepLeaf` and `ShortValueLeaf`; proving them and the DFS/row enumeration relation blocks completion.
- Build: `lake build AKLT.W.H3C035.Main` succeeded in 13.9 s.
- Limitation: no alternate-model switch was available; no sub-agent was used, as explicitly forbidden.
- Orchestrator should preserve this as `PARTIAL` and pass the named residuals/helper-leaf proof obligations onward.
