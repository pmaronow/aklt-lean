STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC054/AKLT/W/REC054/Main.lean): the exact requested theorem and protected-site preservation proofs reused from the earlier attempt.
- [LocalRules.lean](/home/ubuntu/aklt/wt/LW_REC054/AKLT/W/REC054/LocalRules.lean): the completed local-rule induction.
- [Check.lean](/home/ubuntu/aklt/wt/LW_REC054/AKLT/W/REC054/Check.lean): exact-type import check and axiom checks for all exported theorems.

The previous residual definition and conditional theorem have been replaced by an unconditional proof.

## Exported declarations

All three declarations are in namespace `AKLT.W.REC054`. In the statements below, `AKLT.Defs` and `AKLT.Blueprint.Rec` are open.

```lean
theorem main : AKLT.Blueprint.Rec.TerminalDefectStatement

theorem trace_localRules_of_fresh_bonds {G : Finset Plane}
    (D : Network G) (f : ℕ → Plane) (n : ℕ)
    (hD : D.LocalRules)
    (hstart : D.status (f 0) = .U → (D.kept (f 0)).card ≤ 3)
    (hne : ∀ i < n, f i ≠ f (i + 1))
    (hflags : ∀ i < n,
      f (i + 1) ∈ D.kept (f i) ∧ f i ∈ D.kept (f (i + 1)))
    (hinj : ∀ i < n, ∀ k < n,
      ({f i, f (i + 1)} : Finset Plane) = {f k, f (k + 1)} → i = k) :
    (traceNetwork D ((List.range (n + 1)).map f)).LocalRules

theorem terminal_localRules (p : PairSetup) {n : ℕ}
    (w : DirectionWord n)
    (htrail : StoppedNetworkTrail p.normalized p.u (protectedSites p.G) w) :
    (traceNetwork p.normalized (wordVertices p.u w)).LocalRules
```

## Proof

The induction tracks local rules, at most three kept flags at the live U site, and both flags of every unused trail bond. Distinct unoriented bonds ensure earlier erasures do not erase an unused flag. A U departure erases an existing outgoing flag, leaving at most two kept flags and hence present degree at most two. An arrival erases an existing incoming flag from a set of size at most four, establishing the live bound for the next step. Active sites and present bonds only decrease, preserving the remaining degree bounds, including the unchanged original-leg counts.

Normalization establishes the initial bound by erasing the flag to the designated centre. Protected sites never occur in the strict prefix; the terminal protected endpoint therefore retains status U, and every other protected site retains its full original kept set. These facts combine with the proved local rules to give the auxiliary terminal network.

No other blueprint leaf is used as a lemma. No residual proposition or additional premise remains.

## Axioms

Output from `#print axioms` in `Check.lean`:

```text
'AKLT.W.REC054.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC054.trace_localRules_of_fresh_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC054.terminal_localRules' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Validation

With `PATH="$HOME/.elan/bin:$PATH"`:

- `lake build AKLT.W.REC054.Main` — passed; 31.26 seconds wall time, with LocalRules reported at 10 seconds and Main at 9.0 seconds.
- `lake env lean AKLT/W/REC054/Check.lean` — passed; 4.98 seconds wall time. This includes `example : AKLT.Blueprint.Rec.TerminalDefectStatement := AKLT.W.REC054.main`.
- Source scan found none of the forbidden proof constructs. No existing files outside `AKLT/W/REC054/` were edited.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC054/Main.lean` with `AKLT.W.REC054.main : AKLT.Blueprint.Rec.TerminalDefectStatement`.
- Completed the earlier attempt's missing local-rule proof in `AKLT/W/REC054/LocalRules.lean`.
- Added `AKLT/W/REC054/Check.lean` for the exact type and all exported-theorem axiom checks.
- Main build and exact-type import check both pass.
- All exported theorems use only propext, Classical.choice, and Quot.sound.
- Open declarations or residual statements: none.
- Limitations or deviations: none; no other blueprint leaf was assumed.
- Orchestrator action: accept the proved leaf; no dependency handoff is required.
