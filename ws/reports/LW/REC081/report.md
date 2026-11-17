STATUS: PROVED FROM DEPS

## Files

All Lean sources are under `AKLT/W/REC081/`:

- `Main.lean`: the exact requested closed theorem, the specialization of REC096 to all first hits of the original protected set, and the reused conditional assembly.
- `Geometry.lean`: original protected-set finiteness, depth projection, interior endpoints, and stopped-trail geometry; reused from the earlier attempt.
- `Normalization.lean`: admissibility and the absent incoming bond of the normalized ordinary response pair; reused.
- `Positivity.lean`: nonnegativity of the finite trace weights and partition ratios; reused.
- `Summation.lean`: the first-trail sum of pointwise maxima, its H2 geometric tail, and the boundary-term enlargement; reused.
- `Audit.lean`: declaration types and `#print axioms` for all 46 exported theorems.

No statement-layer or other leaf source files were changed. The previous report remains in `report.luna.md`.

## Exported result

```lean
theorem AKLT.W.REC081.main :
    AKLT.Blueprint.Rec.SecondTermBoundStatement
```

Its unfolded statement is:

```lean
AKLT.Blueprint.Top.H1Statement →
  ∀ CV q : ℝ, AKLT.Defs.OpenTrailBound CV q →
  ∀ p : AKLT.Blueprint.Rec.PairData, ∀ d : ℕ,
    1 ≤ d → (d : ℕ∞) ≤ p.depth →
    |AKLT.Blueprint.Rec.secondTerm p| ≤
      AKLT.Blueprint.Rec.sourceConstant CV q * q ^ (2 * d)
```

The other added theorem is
`AKLT.W.REC081.firstTrailCoverage : AKLT.W.REC081.ResidualFirstTrailCoverage`.
This asserts shared-matcher coverage of every U departure in every stopped trail from the normalized first endpoint to the original protected set. All reused helper statements and their axiom output appear in the complete audit below.

## Dependencies and proof

The following proved leaves appear in `/home/ubuntu/aklt/state/lw/proved-index.tsv` and are imported as lemmas:

| Theorem | Statement |
| --- | --- |
| `AKLT.W.REC080.main` | `AKLT.Blueprint.Rec.ResidualTargetBoundStatement` |
| `AKLT.W.REC094.main` | `AKLT.Blueprint.Rec.OnePointPointwiseStatementV2` |
| `AKLT.W.REC096.main` | `AKLT.Blueprint.Rec.CoveredClosureStatementV2` |

Write `du`, `dv` for the natural distances of the two original endpoints to the original protected set, and `K = onePointConstant CV q`. Finiteness of these distances and the pair-depth premise give `d ≤ du` and `d ≤ dv`; since `d ≥ 1`, both endpoints are interior.

REC080 bounds each terminal residual in the first boundary expansion by `K * q^dv`, uniformly in the trail and pin choice. Nonnegative trace coefficients and ratios then bound each signed summand by `2 * K * q^dv` times its trace coefficient and the pointwise maximum of its two ratios. Dropping avoidance of the second endpoint enlarges this finite sum to all first hits of the original protected set.

REC096 applies to this larger class with the same incoming direction and gives zero uncovered U departures. The incoming bond from the removed centre is absent, and the normalized network satisfies the auxiliary and admissible-start premises. REC094 therefore supplies the shared-matcher pointwise majorant. The existing H2 length summation starts at `du` and gives the all-first-hits sum at most `K * q^du`. The maximum remains inside the sum throughout.

Multiplication yields `2 * K^2 * q^(du + dv) ≤ 2 * K^2 * q^(2*d)`. The algebraic identity
`2 * K^2 = sourceConstant CV q`
retains exactly `2 * (12/5)^24 * (CV/(1-q))^2`. No changed protected set, additional decay loss, or unproved residual premise is used by `main`.

## Validation

- `export PATH="$HOME/.elan/bin:$PATH"`
- `lake build AKLT.W.REC081.Main` — passed, **85.11 s** wall time including imported leaf dependencies; `Main.lean` itself compiled in **3.8 s**. Build output: `build.log`, timing: `build.time`.
- `lake env lean AKLT/W/REC081/Audit.lean` — passed, **4.77 s** wall time. Full output: `audit.log`, timing: `audit.time`.
- All 46 exported theorem names were matched against their `#print axioms` results. Every axiom set is a subset of the permitted `{propext, Classical.choice, Quot.sound}`.
- Source scan found none of the forbidden proof shortcuts or commands.

Exact requested theorem audit:

```text
AKLT.W.REC081.main : AKLT.Blueprint.Rec.SecondTermBoundStatement
'AKLT.W.REC081.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Complete declaration and axiom audit

```text
AKLT.W.REC081.setDistance_le_of_mem (x y : AKLT.Defs.Plane) (S : Set AKLT.Defs.Plane) (hy : y ∈ S) :
  AKLT.Defs.setDistance AKLT.Defs.latticeDist x S ≤ ↑(AKLT.Defs.latticeDist x y)
'AKLT.W.REC081.setDistance_le_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.protectedSites_nonempty (G : Finset AKLT.Defs.Plane) (hG : G.Nonempty) :
  (AKLT.Defs.protectedSites G).Nonempty
'AKLT.W.REC081.protectedSites_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.protectedDistance_finite (G : Finset AKLT.Defs.Plane) (hG : G.Nonempty) (x : AKLT.Defs.Plane) :
  AKLT.Defs.setDistance AKLT.Defs.latticeDist x ↑(AKLT.Defs.protectedSites G) ≠ ⊤
'AKLT.W.REC081.protectedDistance_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.pair_volume_nonempty (p : AKLT.Blueprint.Rec.PairData) : p.G.Nonempty
'AKLT.W.REC081.pair_volume_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.protectedDepthProjection (p : AKLT.Blueprint.Rec.PairData) (d : ℕ) (hdepth : ↑d ≤ p.depth) :
  d ≤ AKLT.Blueprint.Rec.protectedDistance p.G p.u ∧ d ≤ AKLT.Blueprint.Rec.protectedDistance p.G p.v
'AKLT.W.REC081.protectedDepthProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.pair_interior (p : AKLT.Blueprint.Rec.PairData) (d : ℕ) (hd : 1 ≤ d) (hdepth : ↑d ≤ p.depth) :
  p.u ∉ AKLT.Defs.protectedSites p.G ∧ p.v ∉ AKLT.Defs.protectedSites p.G
'AKLT.W.REC081.pair_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.latticeDist_triangle (x y z : AKLT.Defs.Plane) :
  AKLT.Defs.latticeDist x z ≤ AKLT.Defs.latticeDist x y + AKLT.Defs.latticeDist y z
'AKLT.W.REC081.latticeDist_triangle' depends on axioms: [propext, Quot.sound]
AKLT.W.REC081.wordVertex_zero {n : ℕ} (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) :
  AKLT.Defs.wordVertex u w 0 = u
'AKLT.W.REC081.wordVertex_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.wordVertex_step {n : ℕ} (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) (j : Fin n) :
  AKLT.Defs.wordVertex u w (↑j + 1) = AKLT.Defs.wordVertex u w ↑j + (w j).step
'AKLT.W.REC081.wordVertex_step' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.wordVertex_distance_le {n : ℕ} (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n) (j : ℕ) :
  j ≤ n → AKLT.Defs.latticeDist u (AKLT.Defs.wordVertex u w j) ≤ j
'AKLT.W.REC081.wordVertex_distance_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.stopped_length_ge_distance {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G)
  (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n)
  (hw : AKLT.Defs.StoppedNetworkTrail D u (AKLT.Defs.protectedSites G) w) : AKLT.Blueprint.Rec.protectedDistance G u ≤ n
'AKLT.W.REC081.stopped_length_ge_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.adjacent_compass (u c : AKLT.Defs.Plane) (h : AKLT.Defs.Adjacent u c) : ∃ incoming, u = c + incoming.step
'AKLT.W.REC081.adjacent_compass' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.present_symm {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (x y : AKLT.Defs.Plane)
  (h : D.Present x y) : D.Present y x
'AKLT.W.REC081.present_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.stopped_isTrail {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G) (u : AKLT.Defs.Plane)
  (incoming : AKLT.Defs.Compass) (T : Finset AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n)
  (habs : ¬D.Present (u - incoming.step) u) (hw : AKLT.Defs.StoppedNetworkTrail D u T w) :
  AKLT.Defs.IsTrail u incoming w
'AKLT.W.REC081.stopped_isTrail' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.normalized_incoming_absent (p : AKLT.Blueprint.Rec.PairData) (incoming : AKLT.Defs.Compass)
  (hin : p.u = p.c + incoming.step) : ¬p.normalized.Present (p.u - incoming.step) p.u
'AKLT.W.REC081.normalized_incoming_absent' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.icoVector_unit (j : AKLT.Defs.IcoLetter) : AKLT.Defs.normSq (AKLT.Defs.icoVector j) = 1
'AKLT.W.REC081.icoVector_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.spinVector_ball (j : AKLT.Defs.SpinLetter) : AKLT.Defs.normSq (AKLT.Defs.spinVector j) ≤ 1
'AKLT.W.REC081.spinVector_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.interaction_nonneg (a b : AKLT.Defs.Vec3) (ha : AKLT.Defs.normSq a ≤ 1) (hb : AKLT.Defs.normSq b ≤ 1) :
  0 ≤ 1 + AKLT.Defs.dot a b
'AKLT.W.REC081.interaction_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.spinWeight_nonneg (s : AKLT.Defs.Status) (j : AKLT.Defs.SpinLetter) : 0 ≤ AKLT.Defs.spinWeight s j
'AKLT.W.REC081.spinWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.network_spins_ball {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (n : ↥D.active → AKLT.Defs.SpinLetter) (x : AKLT.Defs.Plane) : AKLT.Defs.normSq (D.spins n x) ≤ 1
'AKLT.W.REC081.network_spins_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.network_normalizer_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) : 0 ≤ D.partition τ b fun x => 1
'AKLT.W.REC081.network_normalizer_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.traceRatio_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (w : List AKLT.Defs.Plane) : 0 ≤ AKLT.Defs.traceRatio D τ b w
'AKLT.W.REC081.traceRatio_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.traceCoefficient_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (w : List AKLT.Defs.Plane) : 0 ≤ AKLT.Defs.traceCoefficient D w
'AKLT.W.REC081.traceCoefficient_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.traceCoefficient_cast_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (w : List AKLT.Defs.Plane) : 0 ≤ ↑(AKLT.Defs.traceCoefficient D w)
'AKLT.W.REC081.traceCoefficient_cast_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.trace_max_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (w : List AKLT.Defs.Plane) : 0 ≤ max (AKLT.Defs.traceRatio D τ true w) (AKLT.Defs.traceRatio D τ false w)
'AKLT.W.REC081.trace_max_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.normalized_kept_subset (p : AKLT.Blueprint.Rec.PairData) (x : AKLT.Defs.Plane) :
  p.normalized.kept x ⊆ p.D.kept x
'AKLT.W.REC081.normalized_kept_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.normalized_present_iff (p : AKLT.Blueprint.Rec.PairData) (x y : AKLT.Defs.Plane) :
  p.normalized.Present x y ↔ p.D.Present x y
'AKLT.W.REC081.normalized_present_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.normalized_presentNeighbours (p : AKLT.Blueprint.Rec.PairData) (x : AKLT.Defs.Plane) :
  p.normalized.presentNeighbours x = p.D.presentNeighbours x
'AKLT.W.REC081.normalized_presentNeighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.normalized_auxiliary (p : AKLT.Blueprint.Rec.PairData) : p.normalized.Auxiliary
'AKLT.W.REC081.normalized_auxiliary' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.adjacent_mem_neighbours (x y : AKLT.Defs.Plane) (h : AKLT.Defs.Adjacent x y) : y ∈ AKLT.Defs.neighbours x
'AKLT.W.REC081.adjacent_mem_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.neighbours_card_le (x : AKLT.Defs.Plane) : (AKLT.Defs.neighbours x).card ≤ 4
'AKLT.W.REC081.neighbours_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.normalized_start (p : AKLT.Blueprint.Rec.PairData) (hinterior : p.u ∉ AKLT.Defs.protectedSites p.G) :
  p.normalized.AdmissibleStart p.u
'AKLT.W.REC081.normalized_start' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.pairSetup_of_interior (p : AKLT.Blueprint.Rec.PairData) (hu : p.u ∉ AKLT.Defs.protectedSites p.G) :
  ∃ setup, setup.toPairData = p
'AKLT.W.REC081.pairSetup_of_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.exceptionFactor_pos : 0 < AKLT.Blueprint.Rec.exceptionFactor
'AKLT.W.REC081.exceptionFactor_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.onePointConstant_nonneg (CV q : ℝ) (h : AKLT.Defs.OpenTrailBound CV q) :
  0 ≤ AKLT.Blueprint.Rec.onePointConstant CV q
'AKLT.W.REC081.onePointConstant_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.trailWeight_nonneg {n : ℕ} (u : AKLT.Defs.Plane) (incoming : AKLT.Defs.Compass)
  (w : AKLT.Defs.DirectionWord n) : 0 ≤ AKLT.Defs.trailWeight u incoming w
'AKLT.W.REC081.trailWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.onePointSum_le_of_pointwise {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (u : AKLT.Defs.Plane) (incoming : AKLT.Defs.Compass) (CV q : ℝ)
  (hOpen : AKLT.Defs.OpenTrailBound CV q) (habs : ¬D.Present (u - incoming.step) u)
  (hpoint :
    ∀ (n : ℕ) (w : AKLT.Defs.DirectionWord n),
      AKLT.Defs.StoppedNetworkTrail D u (AKLT.Defs.protectedSites G) w →
        ↑(AKLT.Defs.traceCoefficient D (AKLT.Defs.wordVertices u w)) *
            max (AKLT.Defs.traceRatio D τ true (AKLT.Defs.wordVertices u w))
              (AKLT.Defs.traceRatio D τ false (AKLT.Defs.wordVertices u w)) ≤
          AKLT.Blueprint.Rec.exceptionFactor * ↑(AKLT.Defs.trailWeight u incoming w)) :
  AKLT.Blueprint.Rec.onePointSum D τ u ≤
    AKLT.Blueprint.Rec.onePointConstant CV q * q ^ AKLT.Blueprint.Rec.protectedDistance G u
'AKLT.W.REC081.onePointSum_le_of_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.weighted_response_bound (a r s x y K : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) (hs : 0 ≤ s) (hK : 0 ≤ K)
  (hx : |x| ≤ K) (hy : |y| ≤ K) : |a * (r * x - s * y)| ≤ 2 * K * (a * max r s)
'AKLT.W.REC081.weighted_response_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.stopped_boundary_trail {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G)
  (u v : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n)
  (hw : AKLT.Defs.StoppedNetworkTrail D u (insert v (AKLT.Defs.protectedSites G)) w)
  (he : AKLT.Defs.wordVertex u w n ≠ v) : AKLT.Defs.StoppedNetworkTrail D u (AKLT.Defs.protectedSites G) w
'AKLT.W.REC081.stopped_boundary_trail' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.secondTerm_le_onePointSum (p : AKLT.Blueprint.Rec.PairData) (K : ℝ) (hK : 0 ≤ K)
  (hterminal :
    ∀ (n : ℕ) (w : AKLT.Defs.DirectionWord n),
      AKLT.Defs.StoppedNetworkTrail p.normalized p.u (insert p.v (AKLT.Defs.protectedSites p.G)) w →
        AKLT.Defs.wordVertex p.u w n ∈ AKLT.Defs.protectedSites p.G →
          ∀ (b : Bool),
            |(AKLT.Defs.traceNetwork p.normalized (AKLT.Defs.wordVertices p.u w)).expectation p.τ b fun a =>
                  AKLT.Defs.dot (a (AKLT.Defs.wordVertex p.u w n)) (a p.v)| ≤
              K) :
  |AKLT.Blueprint.Rec.secondTerm p| ≤ 2 * K * AKLT.Blueprint.Rec.onePointSum p.normalized p.τ p.u
'AKLT.W.REC081.secondTerm_le_onePointSum' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.ResidualSharedMatcherPointwise : Prop
AKLT.W.REC081.ResidualFirstTrailCoverage : Prop
AKLT.W.REC081.ResidualTerminalTarget : Prop
AKLT.W.REC081.onePointSumV2_of_pointwise (hpoint : AKLT.W.REC081.ResidualSharedMatcherPointwise) :
  AKLT.Blueprint.Rec.OnePointSumStatementV2
'AKLT.W.REC081.onePointSumV2_of_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.uncoveredCountV2_eq_zero {G : Finset AKLT.Defs.Plane} {n : ℕ} (D : AKLT.Defs.Network G)
  (u : AKLT.Defs.Plane) (incoming : AKLT.Defs.Compass) (w : AKLT.Defs.DirectionWord n)
  (hcovered :
    ∀ (i : Fin n),
      (AKLT.Blueprint.Rec.prefixNetwork D u w ↑i).status (AKLT.Defs.wordVertex u w ↑i) = AKLT.Defs.Status.U →
        AKLT.Defs.CoveredDepartureV2 (AKLT.Blueprint.Rec.prefixNetwork D u w ↑i) (AKLT.Defs.wordVertex u w ↑i)
          (AKLT.Defs.wordIncoming incoming w i) (w i)) :
  AKLT.Blueprint.Rec.uncoveredCountV2 D u incoming w = 0
'AKLT.W.REC081.uncoveredCountV2_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.normalized_onePointSum_of_residuals (hpoint : AKLT.W.REC081.ResidualSharedMatcherPointwise)
  (hcover : AKLT.W.REC081.ResidualFirstTrailCoverage) (hH1 : AKLT.Blueprint.Top.H1Statement) (CV q : ℝ)
  (hOpen : AKLT.Defs.OpenTrailBound CV q) (p : AKLT.Blueprint.Rec.PairData) (hu : p.u ∉ AKLT.Defs.protectedSites p.G) :
  AKLT.Blueprint.Rec.onePointSum p.normalized p.τ p.u ≤
    AKLT.Blueprint.Rec.onePointConstant CV q * q ^ AKLT.Blueprint.Rec.protectedDistance p.G p.u
'AKLT.W.REC081.normalized_onePointSum_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.main_of_residuals (hpoint : AKLT.W.REC081.ResidualSharedMatcherPointwise)
  (hcover : AKLT.W.REC081.ResidualFirstTrailCoverage) (hterminal : AKLT.W.REC081.ResidualTerminalTarget) :
  AKLT.Blueprint.Rec.SecondTermBoundStatement
'AKLT.W.REC081.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.firstTrailCoverage : AKLT.W.REC081.ResidualFirstTrailCoverage
'AKLT.W.REC081.firstTrailCoverage' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC081.main : AKLT.Blueprint.Rec.SecondTermBoundStatement
'AKLT.W.REC081.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Open issues

None. The three transparent `Residual...` definitions and `main_of_residuals` are retained as reusable proof interfaces; `main` supplies proofs for all three. There are no remaining blueprint dependencies requiring proof.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC081.main : AKLT.Blueprint.Rec.SecondTermBoundStatement`.
- Reused the earlier finite-sum, positivity, normalization, and original-depth arguments.
- Closed the pointwise and terminal dependencies with REC094 and REC080.
- Closed all-first-hit coverage by specializing REC096 to original S.
- Preserved exactly `sourceConstant CV q` and `q^(2*d)`.
- Build passed: `lake build AKLT.W.REC081.Main` (85.11 s wall, 3.8 s for Main).
- Audit passed for all 46 exported theorems (4.77 s); only the three permitted axioms.
- Open statements: none.
- Limitations or deviations: uses only proved leaves authorized by the updated brief; no mathematical deviation.
- Orchestrator action: accept REC081 and add its theorem/module to the proved index after validation.
