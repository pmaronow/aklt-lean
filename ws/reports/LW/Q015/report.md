STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q015/AKLT/W/Q015/Main.lean)
- `/home/ubuntu/aklt/reports/LW/Q015/report.md`

## Exported declaration

`AKLT.W.Q015.main : AKLT.Blueprint.Q.TensorResolutionStatement`

The proof scales each local quartic monomial by its square-root binomial factor, tensors the supplied local Gram identities over the dependent site alphabets, then expands the physical evaluation sum. The diagonal terms reduce to the Euclidean coordinate norm. No alphabet cardinality equality or unitarity premise is used.

## Axioms

Output of `#print axioms AKLT.W.Q015.main`:

```text
'AKLT.W.Q015.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.Q015.Main`
- Result: success; Lake reported the module build in 5.4 s (10.6 s wall time).
- The compiler reports only deprecation/linter warnings for `if_pos` and `if_neg`; no proof gaps remain.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q015.main` with the exact requested type.
- Added only `AKLT/W/Q015/Main.lean` in the worktree and this report.
- Build succeeds with axioms `[propext, Classical.choice, Quot.sound]`.
- No open mathematical or proof obligations; only harmless tactic deprecation warnings remain.
