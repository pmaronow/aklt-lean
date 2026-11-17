STATUS: PARTIAL

The requested closed theorem `AKLT.W.REC081.main : AKLT.Blueprint.Rec.SecondTermBoundStatement` is not proved and is absent. The delivered module instead proves the exact statement from three explicitly named, closed residual propositions. No residual is declared as an axiom or supplied by another unproved blueprint leaf.

## Files

All Lean files are under `/home/ubuntu/aklt/wt/LW_REC081/AKLT/W/REC081/`:

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC081/AKLT/W/REC081/Main.lean): residual definitions, shared-matcher sum bridge, and conditional final assembly.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_REC081/AKLT/W/REC081/Geometry.lean): finiteness of original protected distances, depth projection, interior endpoints, word displacement and length, absent incoming bond, and injection into the H2 trail class.
- [Positivity.lean](/home/ubuntu/aklt/wt/LW_REC081/AKLT/W/REC081/Positivity.lean): unit icosahedron vectors, nonnegative interaction factors and partition sums, nonnegative trace coefficients and ratios.
- [Normalization.lean](/home/ubuntu/aklt/wt/LW_REC081/AKLT/W/REC081/Normalization.lean): normalization preserves present bonds and degrees, produces an auxiliary network and an admissible first start.
- [Summation.lean](/home/ubuntu/aklt/wt/LW_REC081/AKLT/W/REC081/Summation.lean): finite H2 geometric-tail summation and the boundary-term enlargement to every first hit of original S.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC081/AKLT/W/REC081/Audit.lean): exact declaration types and `#print axioms` for all 44 exported theorems.

The earlier attempt's `Main.lean` was replaced within the authorized leaf directory. Its report remains in [report.luna.md](/home/ubuntu/aklt/reports/LW/REC081/report.luna.md). No statement-layer or other pre-existing project files were edited.

## What is proved

The earlier `ResidualProtectedDepthProjection` is fully discharged by `protectedDepthProjection`, with no residual premise. Finiteness follows by choosing a rightmost site of the finite nonempty volume, proving it lies in original S, and bounding distances to that site.

`onePointSum_le_of_pointwise` proves the entire finite summation step from a common pointwise estimate. It uses the absent incoming bond to obtain an `IsTrail`, proves every stopped trail has length at least the original protected distance, applies the given H2 inequality at each length, and bounds the finite geometric tail. It keeps the maximum inside the sum. `onePointSumV2_of_pointwise` packages this as the shared-matcher `OnePointSumStatementV2`, conditional only on the shared pointwise residual.

`secondTerm_le_onePointSum` proves, for any nonnegative K and a uniform bound K on both terminal expectations,

```lean
|secondTerm p| ≤ (2 * K) * onePointSum p.normalized p.τ p.u
```

The target-terminal summands vanish. Every remaining stopped trail is a first hit of original S. The proof enlarges to all such first hits, including trails that visit v before S, using nonnegativity of the extra summands. It proves the pointwise inequality using `max R_true R_false` before taking either finite sum.

`main_of_residuals` then substitutes the two original-S one-point factors, applies `protectedDepthProjection`, and proves the exact retained constant and exponent by algebra:

```lean
AKLT.W.REC081.main_of_residuals
    (hpoint : AKLT.W.REC081.ResidualSharedMatcherPointwise)
    (hcover : AKLT.W.REC081.ResidualFirstTrailCoverage)
    (hterminal : AKLT.W.REC081.ResidualTerminalTarget) :
    AKLT.Blueprint.Rec.SecondTermBoundStatement
```

Its conclusion unfolds to the requested `sourceConstant CV q * q^(2*d)`. There is no added factor, changed distance, changed pin assignment, or change to original S.

## Open residual statements and blockers

All three are transparent `def ... : Prop` declarations in `Main.lean`.

1. `AKLT.W.REC081.ResidualSharedMatcherPointwise := AKLT.Blueprint.Rec.OnePointPointwiseStatementV2`.
   This is the H1 estimate for a single stopped trail in an auxiliary network with at most twelve uncovered U departures, counted by `uncoveredCountV2` using `AKLT.Defs.CoveredDepartureV2`. Its conclusion is the common pointwise bound by `exceptionFactor * trailWeight`. The open work is the local-to-global trace comparison: trace dynamics and telescoping, covered local ratio bounds from H1, and the uniform ratio bound at exceptions. No H2 summation remains in this residual.

2. `AKLT.W.REC081.ResidualFirstTrailCoverage` says that for every `PairSetup` and every trail stopped at original S, each true U departure satisfies `AKLT.Defs.CoveredDepartureV2` with the actual incoming and outgoing directions. This is a restriction of the shared covered-closure statement to the class needed here. The open work is the evolving kept/status invariant and construction of a matching covered template. The delivered proof shows this implies zero shared-matcher exceptions, and separately proves all static start and normalization facts.

3. `AKLT.W.REC081.ResidualTerminalTarget := AKLT.Blueprint.Rec.ResidualTargetBoundStatement`.
   For a first trail that avoids v and terminates in original S, and for either pin choice, this bounds the single terminal scalar-product expectation by `onePointConstant CV q * q^(protectedDistance p.G p.v)`. The open work is the second finite pair expansion in the terminal auxiliary network, admissibility and target degree, and the shared-matcher twelve-exception one-point comparison. The outer first-trail sum, its enlargement, positivity, and the multiplication of the two original depths are all proved outside this residual.

These are smaller pointwise/geometric obligations rather than a residual restatement of the complete second-term product bound. I did not complete their proofs from the frozen definitions. No counterexample or missing premise is asserted.

## Build and soundness checks

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC081.Main` succeeded. During compilation Lake reported Geometry 4.3 s, Positivity 6.9 s, Normalization 9.5 s, Summation 8.5 s, and Main 6.1 s for their respective successful builds. The final cached verification took 5.05 s wall time; see [build.log](/home/ubuntu/aklt/reports/LW/REC081/build.log) and [build.time](/home/ubuntu/aklt/reports/LW/REC081/build.time).
- `PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/REC081/Audit.lean` succeeded in 4.65 s wall time; see [audit.log](/home/ubuntu/aklt/reports/LW/REC081/audit.log) and [audit.time](/home/ubuntu/aklt/reports/LW/REC081/audit.time).
- Every exported theorem was checked with `#print axioms`. All dependencies are subsets of `[propext, Classical.choice, Quot.sound]`. The conditional final theorem has exactly those three axioms.
- The source scan found no forbidden proof placeholders or unsafe/kernel-bypassing features.
- An exact-type check of the requested closed `main` cannot pass until the three residuals are discharged. Successful module compilation is not a claim that REC081 is proved.

## Exported declarations and complete axiom output

The following is the actual successful output of `Audit.lean`, including the statement of every exported theorem and all axiom reports:

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
```

## ORCH-SUMMARY

- Delivered compiling partial work in `AKLT/W/REC081/`, with 44 audited theorems.
- Requested closed declaration `AKLT.W.REC081.main` remains absent.
- Conditional final result: `AKLT.W.REC081.main_of_residuals`.
- Closed the earlier protected-depth residual completely.
- Proved normalization/start facts, nonnegativity, H2 finite-tail summation, and all-first-hits enlargement.
- Preserved the pointwise maximum, original pins/S/distances, sourceConstant, and q^(2*d).
- Open: `AKLT.W.REC081.ResidualSharedMatcherPointwise`.
- Open: `AKLT.W.REC081.ResidualFirstTrailCoverage`.
- Open: `AKLT.W.REC081.ResidualTerminalTarget`.
- Residuals are explicit closed Props and theorem arguments, not axioms or silently imported leaves.
- No false-statement claim or V2 replacement is made.
- Build: `lake build AKLT.W.REC081.Main` passes.
- Audit: all 44 theorem dependencies are within the permitted three axioms.
- Orchestrator must arrange proofs of the three residuals before exporting the required closed `main`.
