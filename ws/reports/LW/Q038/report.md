STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_Q038/AKLT/W/Q038/Main.lean`
- `/home/ubuntu/aklt/reports/LW/Q038/report.md`

## Exported declarations

- `AKLT.W.Q038.main : AKLT.Blueprint.Q.StarProjectorTransportStatement`
- `AKLT.W.Q038.StarChart (n : ℕ) := EuclideanSpace ℂ (Fin n × (Fin 5 → Fin 5))`
- `AKLT.W.Q038.starRow v r`: extracts the `r`-th five-site star vector.
- `AKLT.W.Q038.starFibreSpace n j`: submodule of chart vectors whose rows lie in the eigenvalue-20 eigenspace of `starCasimir j`.
- `AKLT.W.Q038.starRowProjection j v`: applies the fixed-star orthogonal projector independently to each row.
- `AKLT.W.Q038.starRowProjection_mem`: rowwise projection belongs to `starFibreSpace n j`.
- `AKLT.W.Q038.starRowProjection_orthogonal`: its residual is orthogonal to `starFibreSpace n j`.
- `AKLT.W.Q038.starFibreProjection_apply`: the chart-space projector has the stated rowwise coordinate formula.

The proof uses `casimirCopies` to show that the chart equivalence sends the bond eigenspace onto the full rowwise fixed-star eigenspace. Surjectivity of the equivalence is used to obtain the reverse inclusion. Uniqueness of orthogonal projection then identifies the transported source projection, with the rowwise formula established by the finite-sum inner product decomposition.

## Axioms

`#print axioms AKLT.W.Q038.main`:

```text
'AKLT.W.Q038.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are permitted axioms; there are no residual statements or admitted facts.

## Build

- `lake env lean AKLT/W/Q038/Main.lean` — passed (12.5 s wall time).
- `lake build AKLT.W.Q038.Main` — passed; Lake reported `Built AKLT.W.Q038.Main (8.8s)` (14.6 s wall time for the command).

## Open issues

None.

## ORCH-SUMMARY

- Delivered the requested theorem with the exact name and type in `AKLT/W/Q038/Main.lean`.
- The chart equivalence's surjectivity is used to identify the entire eigenspace fibrewise.
- The projection equality follows from uniqueness of orthogonal projection and rowwise inner products.
- Kernel axiom output: `[propext, Classical.choice, Quot.sound]`.
- The requested Lake build passed.
- No residual declarations, limitations, or deviations remain.
