STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_GAP031/AKLT/W/GAP031/Main.lean`
- `/home/ubuntu/aklt/reports/LW/GAP031/report.md`

## Exported declaration

`AKLT.W.GAP031.main : AKLT.Blueprint.Gap.PeriodicNeighbourCouplingStatement`

All helper definitions and lemmas in `Main.lean` are private to that module.

## Proof outline

Extract the unique changed site. For each labelled square, couple the full conditional laws as follows: containing labels use an identical full configuration; adjacent exterior labels lift the assumed block coupling and add the one exterior disagreement; far labels use identical block resampling, justified by `TorusRangeOne`. Average these full-law couplings over labels. `PeriodicCounts` supplies the exact containing and adjacent counts, while `volumeCount M ≤ card (Site L N)` gives the positive averaging denominator. The finite sum of the three label costs is `card(Site L N) - volumeCount M + haloCount M * K`.

## Axioms

Output of `#print axioms AKLT.W.GAP031.main`:

```text
'AKLT.W.GAP031.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted axioms.

## Build

- `lake build AKLT.W.GAP031.Main` — passed; final Lake module build reported 5.2 s.
- `lake env lean /tmp/GAP031AxiomsOnly.lean` — passed; 3.7 s, reporting the axioms above.

No open proof obligations remain. The hypotheses `1 ≤ M` and `0 ≤ K` are accepted but not needed by this coupling estimate once `PeriodicCounts`, range one, and block influence are given.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP031.main` at the exact requested type in `AKLT/W/GAP031/Main.lean`.
- Proved the statement by per-label couplings, their uniform mixture, and the exact count identity.
- `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
- `lake build AKLT.W.GAP031.Main` passed.
- All helper declarations are private.
- No residual statements, false-premise issue, or open Lean obligations.
- The supplied `1 ≤ M` and `0 ≤ K` premises are unused in the proof.
- Orchestrator action: none required.
