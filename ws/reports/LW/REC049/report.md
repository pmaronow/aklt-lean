STATUS: PROVED

## Files

- `AKLT/W/REC049/Main.lean`
- `/home/ubuntu/aklt/reports/LW/REC049/report.md`

## Exported declaration

- `AKLT.W.REC049.main : AKLT.Blueprint.Rec.NormalizeStartStatement`

## Proof summary

The `ResponsePair` hypothesis supplies `p.D.status p.c = .X`. The proof shows that the normalized and original networks have identical present bonds: the only changed kept flag points to `p.c`, which is inactive. Status, active sites, spin indexing, and original leg factors are unchanged, so both pinned/free partitions agree for every observable.

## Axioms

`#print axioms AKLT.W.REC049.main`:

```text
'AKLT.W.REC049.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC049.Main`
- Result: success; module build reported 5.3 s (the overall Lake invocation took about 13 s).
- Axiom inspection: `PATH="$HOME/.elan/bin:$PATH" lake env lean /tmp/REC049Axioms.lean`; success.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC049/Main.lean` with `AKLT.W.REC049.main` proving the exact frozen statement.
- Present bonds are unchanged because `p.c` has status X; partition inputs otherwise agree.
- Build succeeded with `lake build AKLT.W.REC049.Main`.
- Axioms are `[propext, Classical.choice, Quot.sound]`.
- No residual claims, limitations, or deviations.
