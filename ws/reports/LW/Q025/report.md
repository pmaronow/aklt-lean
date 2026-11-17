STATUS: PROVED FROM DEPS

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q025/AKLT/W/Q025/Main.lean)
- `/home/ubuntu/aklt/reports/LW/Q025/report.md`

## Exported declarations

- `AKLT.W.Q025.statePolynomial_eq_encode {L N : Size} (ψ : Hilbert L N) : AKLT.Blueprint.Q.statePolynomial ψ = AKLT.Uniq.encode ψ`
- `AKLT.W.Q025.main : AKLT.Blueprint.Q.SpectatorDivisibilityStatement`

The proof identifies the frozen state polynomial with the normalized `AKLT.Uniq.encode` polynomial, then applies the proved library theorem `AKLT.Uniq.edgeKernel` to each edge. The explicit pair implication in `SpectatorDivisibilityStatement` is unused. This relies on `AKLT/Uniq/Edge.lean`, an allowed proved library module, and not on another blueprint leaf.

## Axioms

`#print axioms main`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.Q025.Main`
- Result: succeeded.
- Timing: Lake reported 5.6 seconds for the target; command wall time was 12.7 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q025.main` with the requested exact type in `AKLT/W/Q025/Main.lean`.
- Build succeeded; axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- The proof reuses proved library theorem `AKLT.Uniq.edgeKernel`; the stated pair implication hypothesis is unused.
- No blueprint leaf was used as a lemma. No residual obligations or limitations remain.
