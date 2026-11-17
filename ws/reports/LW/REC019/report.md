STATUS: PARTIAL

The requested closed declaration `AKLT.W.REC019.main : AKLT.Blueprint.Rec.AlphaUniformStatement` is **not proved or exported**. The delivered `Main.lean` compiles and derives the exact target from smaller, closed, transparent residual propositions. This is a substantial extension of the previous conditional proof: the logarithmic-mean estimates, free positivity, explicit moments, local three-factor mean bound, relevant departure geometry, and finite averaging are now proved.

## Files

All Lean files are under `/home/ubuntu/aklt/wt/LW_REC019/AKLT/W/REC019/`.

| File | Content |
| --- | --- |
| `Main.lean` | Exact target from two finite moment bounds, or from one common conditional-mixture residual. |
| `LogMean.lean` | Integral formula including the diagonal; positivity; monotonicity; interval bounds; exact reciprocal estimate at `41/50`. |
| `FreePositive.lean` | Nonnegative monomial averages from coordinate sign symmetries; nonnegative natural-coefficient polynomial product averages; concrete free pair positivity. |
| `SpinGeometry.lean` | Unit icosahedron atoms, support bounds, Cauchy–Schwarz, small-mean pair and triple inequalities. |
| `SiteMoments.lean` | Exact moments through degree four and the U/D site functional formulas. |
| `ThreeMean.lean` | Explicit integrated three-factor normalizer and vector numerator. |
| `LocalBound.lean` | The `3/5` local mean bound for three unit fields and for actual spin/zero fields, for U and D sites. |
| `NetworkBounds.lean` | Concrete nonnegative network weights, normalized pair bounds even at zero mass, and unconditional positivity of `responseJ`. |
| `DepartureGeometry.lean` | Neighbour nonadjacency, absence of original legs, and degree at most three after removal. |
| `Conditioning.lean` | Finite mixture averaging with zero weights and zero total mass; pair and triple moment bounds. |
| `Audit.lean` | `#print axioms` on every one of the 59 public theorems. |

Complete exported statements and transparent definitions are recorded in [declarations.md](/home/ubuntu/aklt/reports/LW/REC019/declarations.md). Raw audit output is in [audit.log](/home/ubuntu/aklt/reports/LW/REC019/audit.log).

## Principal exported declarations

All names below have prefix `AKLT.W.REC019`.

```lean
theorem main_of_residuals
    (hT : Residual_TripleLower) (hP : Residual_PairUpper) :
    AKLT.Blueprint.Rec.AlphaUniformStatement

theorem main_of_conditional_mixture
    (h : Residual_ConditionalMixture) :
    AKLT.Blueprint.Rec.AlphaUniformStatement

theorem residuals_of_conditional_mixture
    (h : Residual_ConditionalMixture) :
    Residual_TripleLower ∧ Residual_PairUpper

theorem alpha_bound_of_intervals {Iτ I₀ Jτ J₀ : ℝ}
    (hIτ : 41 / 50 ≤ Iτ) (hI₀ : 1 ≤ I₀)
    (hJτp : 0 < Jτ) (hJ₀p : 0 < J₀)
    (hJτ' : Jτ ≤ 134 / 125) (hJ₀' : J₀ ≤ 134 / 125) :
    1 / (3 * logarithmicMean Iτ I₀) -
      1 / (5 * logarithmicMean Jτ J₀) ≤ (18094 / 100000 : ℝ)
```

`Residual_TripleLower` asks only for the pinned sum of the three removed pair means to be at least `-27/50`, for the eligible departures of the frozen target. `Residual_PairUpper` asks for the removed `f,g` pair mean to be at most `9/25` for both pin choices. Neither contains logarithms or response coefficients. Their complete closed definitions are in `Main.lean` and the declaration appendix.

`Residual_ConditionalMixture` asks for the three removed pair means to be represented by one finite nonnegative mixture of pairwise scalar products of three conditional vectors, each with squared norm at most `9/25`. Its finite averaging consequences are proved, including zero-mass cases. It is an alternative structural residual sufficient to discharge both moment residuals.

## What remains open

The unresolved step is proving `AKLT.W.REC019.Residual_ConditionalMixture` from the concrete `Network.partition` definition. It requires an explicit finite reindexing into the three selected spins and the complement, grouping all site, bond and original-leg factors, and identifying the three pair insertions with the same mixture. The needed no-leg, nonadjacency and degree bounds are proved in `DepartureGeometry.lean`; the required local normalizer and mean bounds are proved in `LocalBound.lean`. The exact finite-sum factorization linking those facts to the network expectation is not proved.

Alternatively, a future proof may discharge `AKLT.W.REC019.Residual_TripleLower` and `AKLT.W.REC019.Residual_PairUpper` directly. No counterexample or missing mathematical premise was found. No closed `main` is claimed, and the requested exact-type check therefore remains unsatisfied.

## Validation and limitations

Commands use `PATH="$HOME/.elan/bin:$PATH"`.

- `lake build AKLT.W.REC019.Main` — successful, final measured wall time **19.01 s**; this imports and checks all delivered helper modules. The final build had no warnings.
- `lake build AKLT.W.REC019.Audit` — successful, measured wall time **9.63 s**; the module itself reported **3.4 s**.
- The initial build of the explicit fourth-moment module reported about **113 s**. It uses a local finite heartbeat bound of `800000`, never an unlimited bound.
- Static scan found none of the forbidden proof escapes or effectful commands in the delivered sources.
- No existing files outside the assigned REC019 directory were edited. The previous `Main.lean` was replaced within the authorized directory. No sub-agents, other blueprint leaves as lemmas, network access, or external certificates were used.
- The logarithm estimate uses Mathlib's proved odd-series estimate with four terms and its geometric remainder, followed by exact rational arithmetic. It obtains the same `367502/1000000` bound without proving the paper's general `crudeLogUpper` enclosure.
- The three-factor mean theorem is specialized to actual spin fields and zero padding, which is sufficient for the proposed conditioning bridge. The full arbitrary-ball-field theorem is not exported.
- Free positivity is proved directly for the discrete icosahedron model using coordinate sign symmetries, without a degree restriction or a finite-network positivity hypothesis. Strict positivity of arbitrary network normalizers is not claimed or needed for the delivered inequalities.

## Axiom audit

All 59 exported theorems depend only on subsets of `[propext, Classical.choice, Quot.sound]`. In particular:

```text
'AKLT.W.REC019.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC019.main_of_conditional_mixture' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The complete `#print axioms` output follows.

```text
AKLT/W/REC019/Audit.lean:4:0: 'AKLT.W.REC019.finite_weighted_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:5:0: 'AKLT.W.REC019.mixture_pair_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:6:0: 'AKLT.W.REC019.mixture_triple_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:7:0: 'AKLT.W.REC019.latticeDist_triangle' depends on axioms: [propext, Quot.sound]
AKLT/W/REC019/Audit.lean:8:0: 'AKLT.W.REC019.adjacent_symmetric' depends on axioms: [propext, Quot.sound]
AKLT/W/REC019/Audit.lean:9:0: 'AKLT.W.REC019.adjacent_of_mem_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:10:0: 'AKLT.W.REC019.neighbours_nonadjacent' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:11:0: 'AKLT.W.REC019.interior_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:12:0: 'AKLT.W.REC019.departure_neighbour_no_leg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:13:0: 'AKLT.W.REC019.remove_presentNeighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:14:0: 'AKLT.W.REC019.present_symmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:15:0: 'AKLT.W.REC019.departure_neighbour_removed_degree' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:16:0: 'AKLT.W.REC019.ico_monomial_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:17:0: 'AKLT.W.REC019.site_monomial_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:18:0: 'AKLT.W.REC019.product_polynomial_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:19:0: 'AKLT.W.REC019.free_partition_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:20:0: 'AKLT.W.REC019.free_pair_partition_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:21:0: 'AKLT.W.REC019.free_removedPairMean_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:22:0: 'AKLT.W.REC019.three_unit_mean_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:23:0: 'AKLT.W.REC019.zero_field_mean_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:24:0: 'AKLT.W.REC019.three_spin_mean_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:25:0: 'AKLT.W.REC019.three_spin_local_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:26:0: 'AKLT.W.REC019.logMean_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:27:0: 'AKLT.W.REC019.logMean_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:28:0: 'AKLT.W.REC019.logMean_monotone' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:29:0: 'AKLT.W.REC019.logMean_le_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:30:0: 'AKLT.W.REC019.lower_le_logMean' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:31:0: 'AKLT.W.REC019.reciprocal_logMean_41_50' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:32:0: 'AKLT.W.REC019.residuals_of_conditional_mixture' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:33:0: 'AKLT.W.REC019.alpha_bound_of_intervals' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:34:0: 'AKLT.W.REC019.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:35:0: 'AKLT.W.REC019.main_of_conditional_mixture' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:36:0: 'AKLT.W.REC019.network_spins_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:37:0: 'AKLT.W.REC019.partition_as_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:38:0: 'AKLT.W.REC019.networkWeight_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:39:0: 'AKLT.W.REC019.network_partition_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:40:0: 'AKLT.W.REC019.network_pair_expectation_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:41:0: 'AKLT.W.REC019.responseJ_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:42:0: 'AKLT.W.REC019.moment_constant' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:43:0: 'AKLT.W.REC019.moment_first' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:44:0: 'AKLT.W.REC019.moment_second' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:45:0: 'AKLT.W.REC019.moment_third' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:46:0: 'AKLT.W.REC019.moment_fourth' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:47:0: 'AKLT.W.REC019.site_U_eq_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:48:0: 'AKLT.W.REC019.site_D_eq_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:49:0: 'AKLT.W.REC019.goldenRatio_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:50:0: 'AKLT.W.REC019.goldenRatio_square' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:51:0: 'AKLT.W.REC019.icoRadius_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:52:0: 'AKLT.W.REC019.icoRadius_square' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:53:0: 'AKLT.W.REC019.icoVector_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:54:0: 'AKLT.W.REC019.spinVector_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:55:0: 'AKLT.W.REC019.normSq_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:56:0: 'AKLT.W.REC019.dot_square_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:57:0: 'AKLT.W.REC019.dot_ball_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:58:0: 'AKLT.W.REC019.spinWeight_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:59:0: 'AKLT.W.REC019.sum_three_dot_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:60:0: 'AKLT.W.REC019.dot_small_ball_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:61:0: 'AKLT.W.REC019.moment_threeProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/REC019/Audit.lean:62:0: 'AKLT.W.REC019.moment_coord_threeProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## ORCH-SUMMARY

- STATUS: PARTIAL; no closed `AKLT.W.REC019.main` is exported.
- `Main.lean` compiles and proves the exact frozen target from transparent finite moment residuals.
- Open direct residuals: `AKLT.W.REC019.Residual_TripleLower`, `AKLT.W.REC019.Residual_PairUpper`.
- Open sufficient structural residual: `AKLT.W.REC019.Residual_ConditionalMixture`.
- Proved: logarithmic-mean analysis, reciprocal rational bound, final coefficient subtraction.
- Proved: concrete free pair positivity and general support/weight bounds, including zero mass.
- Proved: explicit moments through degree four and integrated three-factor formulas.
- Proved: local U/D `3/5` mean bound for actual spin fields and zero padding.
- Proved: relevant departure geometry and finite-mixture moment aggregation.
- Missing: concrete network-to-common-fibre factorization and reindexing.
- Deviation: four-term Mathlib logarithm enclosure replaces the paper's general crude enclosure.
- Limitation: arbitrary-ball-field mean bound and strict normalizer positivity are not exported.
- All 59 public theorems audited; only the three permitted logical axioms occur.
- Final builds: Main 19.01 s wall; Audit 9.63 s wall.
- No files outside REC019 were changed; no sub-agents were used.
- Orchestrator must assign the conditioning bridge or the two direct finite moment bounds.
