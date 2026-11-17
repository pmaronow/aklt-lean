STATUS: PARTIAL

## Files

- `AKLT/W/H3C031/Main.lean`

## Delivered declarations

- `AKLT.W.H3C031.ResidualPhaseNumerators : Prop` — the remaining one-step phase-counter identity, including its denominator.
- `AKLT.W.H3C031.ResidualRewardItems : Prop` — the remaining item witness identity for every item produced by the transition.
- `AKLT.W.H3C031.main_from_residuals : ResidualPhaseNumerators → ResidualRewardItems → CertData.H3.Bridge.PrefixStepLeaf`.

The proof derives the packed walk update, base-weight update, and first-visit item-time list update from the retained snoc lemmas. It does not establish inhabitants of the two residual propositions, and it does not export the requested exact theorem `AKLT.W.H3C031.main : CertData.H3.Bridge.PrefixStepLeaf`.

## Axioms

`#print axioms AKLT.W.H3C031.main_from_residuals`:

```text
[propext, Classical.choice, Quot.sound]
```

These are the permitted Lean axioms. There is no `sorry`, `admit`, `axiom`, or `native_decide` in the delivered file.

## Build

- `lake env lean AKLT/W/H3C031/Main.lean` — succeeded.
- `lake build AKLT.W.H3C031.Main` — succeeded; 12.1 s total, target module reported 7.6 s.

The build reports only linter/deprecation warnings in `Main.lean` for unused simp arguments and legacy `if_pos`/`dif_pos` names.

## Open issues

- Prove `AKLT.W.H3C031.ResidualPhaseNumerators`. The missing argument is the exact rational phase update for revisit, straight, and turn transitions, including the response term tied to the normalized reward.
- Prove `AKLT.W.H3C031.ResidualRewardItems`. This requires showing the production `deadMaskAt` reward, normalized by `ExactValid`, equals `witnessKappa` for the appended word, while transporting old item witnesses.
- Consequently, the exact declaration `AKLT.W.H3C031.main` remains open.
- The task’s “different cheaper model” first-attempt instruction was not met: the common leaf brief also forbids sub-agents, and no model-switch tool is available in this session.

## ORCH-SUMMARY

- Delivered a compiled partial module at `AKLT/W/H3C031/Main.lean`.
- Proved walk, base-weight, and first-visit time-list transition accounting.
- `main_from_residuals` derives `PrefixStepLeaf` from two explicit closed residual Props.
- Open exact residuals: `ResidualPhaseNumerators`, `ResidualRewardItems`.
- Requested exact declaration `AKLT.W.H3C031.main` is not yet proved.
- Build command succeeded: `lake build AKLT.W.H3C031.Main` (12.1 s).
- Axioms for the exported conditional theorem: `[propext, Classical.choice, Quot.sound]`.
- No sub-agent or alternate cheaper-model attempt was used; this limitation is recorded above.
- Orchestrator should pass on or assign proofs of both residuals before marking the leaf proved.
