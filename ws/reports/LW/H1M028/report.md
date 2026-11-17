STATUS: PROVED

## Files

- `AKLT/W/H1M028/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H1M028/report.md`

## Exported declaration

`AKLT.W.H1M028.main : AKLT.Blueprint.H1.BallChordStatement`, where the closed
statement unfolds to

```lean
∀ v : AKLT.Defs.Vec3, AKLT.Defs.normSq v ≤ 1 →
  AKLT.Blueprint.H1.UnitChord v
```

Here `UnitChord v` is witnessed by unit vectors `a`, `b` and a real `t` with
`0 ≤ t`, `t ≤ 1`, and `v = t • a.val + (1 - t) • b.val`.

The proof handles zero with an explicit coordinate unit vector and its negative.
For nonzero `v`, it uses `r = sqrt (normSq v)`, the unit vectors `v / r` and
`-(v / r)`, and `t = (1 + r) / 2`. It proves `r ≤ 1` and hence the required
weight bounds.

## Axioms

`#print axioms AKLT.W.H1M028.main`:

```text
'AKLT.W.H1M028.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1M028.Main`

Result: successful. Lake reported the module built in 4.2 seconds; command wall
time was 8.93 seconds.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested theorem at the exact name and type in `AKLT/W/H1M028/Main.lean`.
- Status is PROVED; no residual statements or deviations.
- `lake build AKLT.W.H1M028.Main` succeeds.
- Exported theorem axioms: propext, Classical.choice, Quot.sound.
- No open issues or further decisions for the orchestrator.
