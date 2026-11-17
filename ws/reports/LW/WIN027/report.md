STATUS: PROVED

Files:

- `/home/ubuntu/aklt/wt/LW_WIN027/AKLT/W/WIN027/Main.lean`

Exported declaration:

- `AKLT.W.WIN027.main : AKLT.Blueprint.Win.CrossUnionStatement`

`#print axioms AKLT.W.WIN027.main` output:

```text
[propext, Classical.choice, Quot.sound]
```

Build:

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.WIN027.Main` — successful; module compilation reported 4.6s.

Open issues: none.

## ORCH-SUMMARY

- Proved `AKLT.Blueprint.Win.CrossUnionStatement` as `AKLT.W.WIN027.main`.
- Deliverable: `AKLT/W/WIN027/Main.lean`.
- The proof lifts paths inside each cross into the thickening and composes them along a star path of centres.
- The singleton case is covered by the reflexive center path.
- `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
- Build succeeded with `lake build AKLT.W.WIN027.Main` (module compile: 4.6s).
- No open issues or deviations.
