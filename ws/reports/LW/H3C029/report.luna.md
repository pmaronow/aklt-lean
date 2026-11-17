STATUS: PARTIAL

## Files

- `AKLT/W/H3C029/Main.lean`

## Exported declarations

- `AKLT.W.H3C029.Residual_prefixRepresentation : Prop` — replay success implies `PrefixRepresents` for the decoded word.
- `AKLT.W.H3C029.Residual_survivingPrefix : Prop` — replay success implies `SurvivingPrefix` for the decoded word.
- `AKLT.W.H3C029.main_of_residuals` — the exact `PrefixReplaySoundLeaf` follows from those two residuals.

There is no unconditional `AKLT.W.H3C029.main` yet. The two residuals are the two conjuncts of the target, stated separately; both remain open. The central blocker is the state invariant: it must connect replay transitions to the phase numerators, base-weight numerator, chronological first-visit reward list, and reward normalization in `PrefixRepresents`. The path component also needs an induction showing that successful replay enforces trail injectivity and avoids the centre and target, including the first-direction condition.

The definitions `PrefixStepLeaf` and `CodeDecodeLeaf` are not imported theorems in this project, so they cannot be used as established proof dependencies. Proving `PrefixStepLeaf` and the decoder identity, then deriving the replay induction, remains the intended route. No other blueprint leaf or sibling worktree proof was used.

## Axioms

`#print axioms AKLT.W.H3C029.main_of_residuals`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H3C029.Main` — completed successfully; approximately 13.4 seconds wall time in the tool (Lake reported 6.8 seconds for the final module and 8,973 jobs including replayed dependencies).

## Open issues

- Prove `AKLT.W.H3C029.Residual_prefixRepresentation` from `PrefixStepLeaf` and `CodeDecodeLeaf`.
- Prove `AKLT.W.H3C029.Residual_survivingPrefix` from replay's transition checks.
- Add the unconditional declaration `AKLT.W.H3C029.main : CertData.H3.Bridge.PrefixReplaySoundLeaf` after both residuals are discharged.

## ORCH-SUMMARY

- Delivered a compiled conditional assembly theorem in `AKLT/W/H3C029/Main.lean`.
- The result proves the requested leaf from two explicit, separate residual Props.
- No unconditional `main` theorem is delivered; both residuals remain open.
- The requested cheaper-model first attempt could not be selected in this no-subagents run.
- No existing files or statement definitions were changed.
- The orchestrator must decide whether to route the two residuals to follow-up proof work.
