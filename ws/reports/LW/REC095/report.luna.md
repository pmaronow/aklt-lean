STATUS: PARTIAL

## Files

- `AKLT/W/REC095/Main.lean`
- `AKLT/W/REC095/Audit.lean`

## Delivered declarations

- `AKLT.W.REC095.Residual_OnePointPointwise : Prop` aliases
  `AKLT.Blueprint.Rec.OnePointPointwiseStatementV2`. This is the outstanding
  per-trail comparison under H1 and the twelve-exception bound.
- `AKLT.W.REC095.Residual_StoppedTrailGeometry : Prop` states that a stopped
  trail is an H2 open trail and its length is at least the protected distance.
- `AKLT.W.REC095.stoppedTrailGeometry : Residual_StoppedTrailGeometry` proves
  those trail and lattice-distance facts directly from the frozen definitions.
- `AKLT.W.REC095.main_of_residuals (hpoint : Residual_OnePointPointwise)
  (hgeo : Residual_StoppedTrailGeometry) :
  AKLT.Blueprint.Rec.OnePointSumStatementV2` proves the finite length grouping,
  inclusion into the H2 sum with the same incoming direction, and the
  geometric tail bound.
- `AKLT.W.REC095.main_of_pointwise (hpoint : Residual_OnePointPointwise) :
  AKLT.Blueprint.Rec.OnePointSumStatementV2` uses the proved geometry theorem.

The requested unconditional declaration
`AKLT.W.REC095.main : AKLT.Blueprint.Rec.OnePointSumStatementV2` is not
delivered. The remaining blocker is a proof of
`AKLT.W.REC095.Residual_OnePointPointwise` from H1 and the stated hypotheses.
The imported blueprint contains this pointwise result only as a `def` and
provides no theorem proving it. I did not assume another open leaf.

## Axiom audit

`#print axioms AKLT.W.REC095.stoppedTrailGeometry`:

```text
[propext, Classical.choice, Quot.sound]
```

`#print axioms AKLT.W.REC095.main_of_residuals`:

```text
[propext, Classical.choice, Quot.sound]
```

`#print axioms AKLT.W.REC095.main_of_pointwise`:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.REC095.Main` — succeeded, 8.2 s.
- `lake build AKLT.W.REC095.Audit` — succeeded, 10.0 s.

No `sorry`, `admit`, custom axiom, or other prohibited escape hatch is used.

## ORCH-SUMMARY

- Delivered a compiled conditional proof of `OnePointSumStatementV2` and its finite H2/geometric-tail summation.
- Proved `AKLT.W.REC095.stoppedTrailGeometry` from definitions.
- Open residual: `AKLT.W.REC095.Residual_OnePointPointwise` (`OnePointPointwiseStatementV2`).
- The exact unconditional `AKLT.W.REC095.main` declaration remains open because the pointwise residual is unproved.
- No statement was shown false or under-premised; this is a proof gap, not a counterexample.
- The orchestrator should pass on the pointwise estimate proof or its concrete local response dependencies.
