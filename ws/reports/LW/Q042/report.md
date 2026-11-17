STATUS: PROVED FROM DEPS

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q042/AKLT/W/Q042/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/Q042/report.md`

## Exported declaration

- `AKLT.W.Q042.main : AKLT.Blueprint.Q.GroundFibreFactorizationStatement`

The proof identifies the four incident bonds as the two outgoing and two incoming bonds. It compares their product with `beta` in centre-first orientation; the two incoming determinant reversals contribute two minus signs. It then splits the full bond product into incident and nonincident factors, retaining `centreSign` in `rho`. Finally, each nonincident determinant is shown invariant under updating the centre coordinate because neither endpoint equals the centre.

## Axioms

`#print axioms AKLT.W.Q042.main`:

```text
[propext, Classical.choice, Quot.sound]
```

The proof uses the proved dependency `AKLT.Challenge.small_natCast_ne_zero` for noncollision of nearest neighbours on side lengths at least three.

## Build

- Command: `time lake build AKLT.W.Q042.Main`
- Result: success; target module compiled in 7.6 s (13.1 s wall time for the command).
- The compiler emitted two nonblocking unnecessary-sequence-focus warnings.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/Q042/Main.lean` and proved the exact requested theorem.
- The factorization includes `centreSign` in `rho`; incoming orientation signs are accounted for.
- `rho` update invariance is proved by showing nonincident bonds avoid the updated site.
- `lake build AKLT.W.Q042.Main` succeeds.
- `#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound`.
- No residual statements or deviations remain.
