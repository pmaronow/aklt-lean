STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_REC057/AKLT/W/REC057/Main.lean`

## Exported declaration

- `AKLT.W.REC057.main : AKLT.Blueprint.Rec.UDepartureInjectiveStatement`

## Proof outline

The proof establishes a recurrence for consecutive `prefixNetwork` values: the next prefix is obtained by applying `traceStep` at the current vertex and its successor. A `traceStep` preserves a site's non-`U` status; a departure from a site whose status is `U` makes that site's status non-`U`. Induction then propagates this fact through all later prefixes. If two distinct indices had the same vertex and both departed from it with status `U`, the earlier departure would force its status at the later prefix to be non-`U`, a contradiction. The auxiliary, start, and stopped-trail hypotheses are not needed for this status-transition argument.

## Axioms

`#print axioms AKLT.W.REC057.main`:

```text
'AKLT.W.REC057.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC057.Main`
- Result: successful; module reported built in 4.8 s (whole command completed in 10.1 s).
- Axiom check: `PATH="$HOME/.elan/bin:$PATH" lake env lean /tmp/REC057Axioms.lean` (6.1 s).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC057.main` with the exact requested statement.
- Main file: `AKLT/W/REC057/Main.lean`.
- The status transition proof and requested Lake build succeeded.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No residual statements, deviations, or open issues.
