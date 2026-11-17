STATUS: PROVED

## Delivery

The exact requested declaration is proved without residual assumptions:

```lean
theorem AKLT.W.REC016.main : AKLT.Blueprint.Rec.BetaPrimeUniformStatement
```

Its source is [Main.lean](/home/ubuntu/aklt/wt/LW_REC016/AKLT/W/REC016/Main.lean:8). Only files under `AKLT/W/REC016/` were written in the worktree; existing statement and library files were not changed.

## Files

- [`Analysis.lean`](/home/ubuntu/aklt/wt/LW_REC016/AKLT/W/REC016/Analysis.lean)
- [`Audit.lean`](/home/ubuntu/aklt/wt/LW_REC016/AKLT/W/REC016/Audit.lean)
- [`Bridge.lean`](/home/ubuntu/aklt/wt/LW_REC016/AKLT/W/REC016/Bridge.lean)
- [`Conditioning.lean`](/home/ubuntu/aklt/wt/LW_REC016/AKLT/W/REC016/Conditioning.lean)
- [`Free.lean`](/home/ubuntu/aklt/wt/LW_REC016/AKLT/W/REC016/Free.lean)
- [`Geometry.lean`](/home/ubuntu/aklt/wt/LW_REC016/AKLT/W/REC016/Geometry.lean)
- [`Graph.lean`](/home/ubuntu/aklt/wt/LW_REC016/AKLT/W/REC016/Graph.lean)
- [`Intervals.lean`](/home/ubuntu/aklt/wt/LW_REC016/AKLT/W/REC016/Intervals.lean)
- [`Main.lean`](/home/ubuntu/aklt/wt/LW_REC016/AKLT/W/REC016/Main.lean)
- [`Model.lean`](/home/ubuntu/aklt/wt/LW_REC016/AKLT/W/REC016/Model.lean)
- [`Moments.lean`](/home/ubuntu/aklt/wt/LW_REC016/AKLT/W/REC016/Moments.lean)

`Audit.lean` imports `Main`, checks an anonymous term of exactly the frozen target type, and runs `#check` and `#print axioms` on every exported theorem. It also checks the nine transparent supporting definitions. The complete transcript is [audit.txt](/home/ubuntu/aklt/reports/LW/REC016/audit.txt).

## Proof

- `Analysis.lean` proves the reciprocal logarithmic-mean integral and its monotonicity. Mathlib's two-term logarithm-series remainder at `t = 3/47` and exact rational arithmetic prove the required numerical row.
- `Moments.lean` evaluates the finite icosahedron sums for the triple normalizer and numerator. A polynomial sum-of-squares identity, including three nonnegative length-deficit terms, proves the mean bound directly for ball fields. Zero padding handles fewer than three fields; the D law follows from its explicit mixture with the zero atom.
- `Free.lean` proves nonnegativity of every coordinate monomial under the actual site law, in all degrees. Evaluating polynomials with natural-number coefficients then proves free pair numerators nonnegative in `Model.lean`.
- `Conditioning.lean` and `Graph.lean` sum refreshed coordinates explicitly. Incident products factor on the two-site fibre, and the two local means give the pair lower bound `-9/25`. The argument uses unnormalized sums: zero-mass fibres contribute zero, and a zero total normalizer is treated separately using Lean's total division.
- `Geometry.lean` and `Bridge.lean` prove that distinct departure neighbours are nonadjacent, have no original legs, and have at most three bonds after deleting the departure. They identify the actual network partition with the indexed finite graph while retaining every original leg.
- `Intervals.lean` obtains `22/25 ≤ I₂ᵗ` and `1 ≤ I₂⁰`; `Main.lean` applies the proved coefficient comparison.

No other blueprint leaf is assumed as a lemma. No residual propositions remain.

## Axioms

```text
'AKLT.W.REC016.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All 80 exported theorems were checked individually. Every axiom list is a subset of the three permitted axioms; none contains `sorryAx`. The full statements and individual axiom outputs appear below.

## Build and validation

Commands, with `PATH="$HOME/.elan/bin:$PATH"`:

```sh
lake build AKLT.W.REC016.Main
lake env lean AKLT/W/REC016/Audit.lean
```

- The first successful final compilation reported `Bridge` 4.5 s, `Intervals` 3.6 s, and `Main` 3.3 s; the earlier exact-moment module compiled in approximately 22 s.
- The final required build succeeded in 5.32 s wall time with compiled dependencies. Its transcript is [build.txt](/home/ubuntu/aklt/reports/LW/REC016/build.txt).
- The independent exact-type and 80-theorem axiom audit succeeded in 4.47 s wall time.
- A source scan found none of the forbidden proof constructs. Git status shows only the assigned new directory.

## Open issues and route differences

None. The implementation uses a generic finite graph indexed directly by active-site and bond subtypes, instead of translating through `FiniteSpinNetwork (n : ℕ)`. Its partition is proved equal to the actual `Network.partition`.

The numerical proof uses Mathlib's slightly looser two-term remainder rather than proving the paper's full `crudeLogUpper` interface; this still proves the exact requested `35510/100000` bound. The direct ball-field sum-of-squares identity replaces the paper's unit-field mixture step. Free positivity is proved in all degrees from sign symmetry, so no separate degree-four expansion premise is needed. A finite heartbeat limit of 1,200,000 is set only for the free-polynomial bridge theorem; no unlimited setting is used.

## Exported declarations and complete axiom output

```text
AKLT.W.REC016.affine_pos {x y t : ℝ} (hx : 0 < x) (hy : 0 < y) (ht : t ∈ Set.Icc 0 1) : 0 < (1 - t) * x + t * y
'AKLT.W.REC016.affine_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.inv_affine_continuous {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
  ContinuousOn (fun t => ((1 - t) * x + t * y)⁻¹) (Set.Icc 0 1)
'AKLT.W.REC016.inv_affine_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.reciprocal_integral {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
  (AKLT.Defs.logarithmicMean x y)⁻¹ = ∫ (t : ℝ) in 0..1, ((1 - t) * x + t * y)⁻¹
'AKLT.W.REC016.reciprocal_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.logarithmicMean_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < AKLT.Defs.logarithmicMean x y
'AKLT.W.REC016.logarithmicMean_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.reciprocal_antitone {x x' y y' : ℝ} (hx : 0 < x) (hxx : x ≤ x') (hy : 0 < y) (hyy : y ≤ y') :
  (AKLT.Defs.logarithmicMean x' y')⁻¹ ≤ (AKLT.Defs.logarithmicMean x y)⁻¹
'AKLT.W.REC016.reciprocal_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.logarithmicMean_mono : AKLT.Blueprint.Rec.LogMeanMonotoneStatement
'AKLT.W.REC016.logarithmicMean_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.base_coefficient_bound : (AKLT.Defs.logarithmicMean (22 / 25) 1)⁻¹ / 3 ≤ 35510 / 100000
'AKLT.W.REC016.base_coefficient_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.coefficient_bound_of_intervals {x y : ℝ} (hx : 22 / 25 ≤ x) (hy : 1 ≤ y) :
  1 / (3 * AKLT.Defs.logarithmicMean x y) ≤ 35510 / 100000
'AKLT.W.REC016.coefficient_bound_of_intervals' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.spins_at {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (σ : ↥D.active → AKLT.Defs.SpinLetter)
  (x : ↥D.active) : D.spins σ ↑x = AKLT.Defs.spinVector (σ x)
'AKLT.W.REC016.spins_at' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.spins_ball {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (σ : ↥D.active → AKLT.Defs.SpinLetter)
  (x : AKLT.Defs.Plane) : AKLT.Defs.normSq (D.spins σ x) ≤ 1
'AKLT.W.REC016.spins_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.legWeight_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (σ : ↥D.active → AKLT.Defs.SpinLetter) : 0 ≤ AKLT.W.REC016.legWeight D τ b σ
'AKLT.W.REC016.legWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.bond_product {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (σ : ↥D.active → AKLT.Defs.SpinLetter) :
  ∏ e,
      (1 +
        AKLT.Defs.dot (AKLT.Defs.spinVector (σ (AKLT.W.REC016.bondLeft D e)))
          (AKLT.Defs.spinVector (σ (AKLT.W.REC016.bondRight D e)))) =
    ∏ e ∈ D.bonds, (1 + AKLT.Defs.dot (D.spins σ e.1) (D.spins σ e.2))
'AKLT.W.REC016.bond_product' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.partition_graph {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ b f =
    ∑ σ,
      AKLT.W.REC016.FiniteGraph.weight (fun x => D.status ↑x) (AKLT.W.REC016.bondLeft D) (AKLT.W.REC016.bondRight D)
          (AKLT.W.REC016.legWeight D τ b) σ *
        f (D.spins σ)
'AKLT.W.REC016.partition_graph' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.partition_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) : 0 ≤ D.partition τ b fun x => 1
'AKLT.W.REC016.partition_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.legWeight_refresh {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (x y : ↥D.active) (hx : ∀ (e : ↥(AKLT.Defs.originalLegs G)), (↑e).1 ≠ ↑x)
  (hy : ∀ (e : ↥(AKLT.Defs.originalLegs G)), (↑e).1 ≠ ↑y) (σ : ↥D.active → AKLT.Defs.SpinLetter)
  (a c : AKLT.Defs.SpinLetter) :
  AKLT.W.REC016.legWeight D τ b (Function.update (Function.update σ x a) y c) = AKLT.W.REC016.legWeight D τ b σ
'AKLT.W.REC016.legWeight_refresh' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.incident_other_injective {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (x : ↥D.active) :
  Function.Injective fun e =>
    ↑(AKLT.W.REC016.FiniteGraph.other (AKLT.W.REC016.bondLeft D) (AKLT.W.REC016.bondRight D) x ↑e)
'AKLT.W.REC016.incident_other_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.incident_card_le {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (hkept : ∀ (z : AKLT.Defs.Plane), D.kept z ⊆ AKLT.Defs.neighbours z ∩ G) (x : ↥D.active) :
  Fintype.card { e // AKLT.W.REC016.FiniteGraph.Inc (AKLT.W.REC016.bondLeft D) (AKLT.W.REC016.bondRight D) x e } ≤
    (D.presentNeighbours ↑x).card
'AKLT.W.REC016.incident_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.bond_separate {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) {x y : ↥D.active} (hxy : x ≠ y)
  (hnot : ¬AKLT.Defs.Adjacent ↑x ↑y) (e : ↥D.bonds) :
  AKLT.W.REC016.FiniteGraph.Inc (AKLT.W.REC016.bondLeft D) (AKLT.W.REC016.bondRight D) x e →
    ¬AKLT.W.REC016.FiniteGraph.Inc (AKLT.W.REC016.bondLeft D) (AKLT.W.REC016.bondRight D) y e
'AKLT.W.REC016.bond_separate' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.active_status {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (x : ↥D.active) :
  D.status ↑x = AKLT.Defs.Status.U ∨ D.status ↑x = AKLT.Defs.Status.D
'AKLT.W.REC016.active_status' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.spinWeight_nonneg (s : AKLT.Defs.Status) (a : AKLT.Defs.SpinLetter) : 0 ≤ AKLT.Defs.spinWeight s a
'AKLT.W.REC016.spinWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.finite_local_bound.{u_1} {ι : Type u_1} [Fintype ι] (hk : Fintype.card ι ≤ 3) (a : ι → AKLT.Defs.Vec3)
  (ha : ∀ (i : ι), AKLT.Defs.normSq (a i) ≤ 1) (s : AKLT.Defs.Status)
  (hs : s = AKLT.Defs.Status.U ∨ s = AKLT.Defs.Status.D) :
  have W := fun v => ∏ j, (1 + AKLT.Defs.dot v (a j));
  0 < AKLT.Defs.siteFunctional s W ∧
    (AKLT.Defs.normSq fun i => (AKLT.Defs.siteFunctional s fun v => v i * W v) / AKLT.Defs.siteFunctional s W) ≤
      (3 / 5) ^ 2
'AKLT.W.REC016.finite_local_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.double_sum_dot (u v : AKLT.Defs.SpinLetter → ℝ) :
  ∑ a, ∑ b, u a * v b * AKLT.Defs.dot (AKLT.Defs.spinVector a) (AKLT.Defs.spinVector b) =
    AKLT.Defs.dot (fun i => ∑ a, u a * AKLT.Defs.spinVector a i) fun i => ∑ b, v b * AKLT.Defs.spinVector b i
'AKLT.W.REC016.double_sum_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.local_pair_lower.{u_1, u_2} {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
  (hi : Fintype.card ι ≤ 3) (hj : Fintype.card κ ≤ 3) (a : ι → AKLT.Defs.Vec3) (b : κ → AKLT.Defs.Vec3)
  (ha : ∀ (i : ι), AKLT.Defs.normSq (a i) ≤ 1) (hb : ∀ (i : κ), AKLT.Defs.normSq (b i) ≤ 1) (s t : AKLT.Defs.Status)
  (hs : s = AKLT.Defs.Status.U ∨ s = AKLT.Defs.Status.D) (ht : t = AKLT.Defs.Status.U ∨ t = AKLT.Defs.Status.D) :
  0 ≤
    ∑ n,
      ∑ m,
        (AKLT.Defs.spinWeight s n * ∏ j, (1 + AKLT.Defs.dot (AKLT.Defs.spinVector n) (a j))) *
            (AKLT.Defs.spinWeight t m * ∏ j, (1 + AKLT.Defs.dot (AKLT.Defs.spinVector m) (b j))) *
          (AKLT.Defs.dot (AKLT.Defs.spinVector n) (AKLT.Defs.spinVector m) + 9 / 25)
'AKLT.W.REC016.local_pair_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.sum_refresh.{u_1, u_2} {α : Type u_1} {S : Type u_2} [Fintype α] [DecidableEq α] [Fintype S] (x : α)
  (H : (α → S) → ℝ) : ∑ σ, ∑ a, H (Function.update σ x a) = ↑(Fintype.card S) * ∑ σ, H σ
'AKLT.W.REC016.sum_refresh' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.sum_refresh_pair.{u_1, u_2} {α : Type u_1} {S : Type u_2} [Fintype α] [DecidableEq α] [Fintype S]
  (x y : α) (H : (α → S) → ℝ) :
  ∑ σ, ∑ a, ∑ b, H (Function.update (Function.update σ x a) y b) = ↑(Fintype.card S) ^ 2 * ∑ σ, H σ
'AKLT.W.REC016.sum_refresh_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.prod_subtype_ite.{u_1} {β : Type u_1} [Fintype β] (P : β → Prop) [DecidablePred P] (f : β → ℝ) :
  ∏ e, f ↑e = ∏ e, if P e then f e else 1
'AKLT.W.REC016.prod_subtype_ite' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.prod_partition3.{u_1} {β : Type u_1} [Fintype β] (P Q : β → Prop) [DecidablePred P] [DecidablePred Q]
  (hPQ : ∀ (e : β), P e → ¬Q e) (f : β → ℝ) : ∏ e, f e = ((∏ e, f ↑e) * ∏ e, f ↑e) * ∏ e, f ↑e
'AKLT.W.REC016.prod_partition3' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.signed_power_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ t ^ n + (-t) ^ n
'AKLT.W.REC016.signed_power_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.site_monomial_nonneg (s : AKLT.Defs.Status) (m : Fin 3 → ℕ) :
  0 ≤ AKLT.Defs.siteFunctional s fun v => ∏ i, v i ^ m i
'AKLT.W.REC016.site_monomial_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.polynomial_functional_nonneg.{u_1} {α : Type u_1} [Fintype α] (s : α → AKLT.Defs.Status)
  (p : MvPolynomial (α × Fin 3) ℕ) :
  0 ≤ AKLT.Defs.productFunctional s fun v => MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun z => v z.1 z.2) p
'AKLT.W.REC016.polynomial_functional_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.adjacent_symm {x y : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent x y) : AKLT.Defs.Adjacent y x
'AKLT.W.REC016.adjacent_symm' depends on axioms: [propext]
AKLT.W.REC016.neighbour_adjacent {x y : AKLT.Defs.Plane} (h : y ∈ AKLT.Defs.neighbours x) : AKLT.Defs.Adjacent x y
'AKLT.W.REC016.neighbour_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.neighbours_card (x : AKLT.Defs.Plane) : (AKLT.Defs.neighbours x).card = 4
'AKLT.W.REC016.neighbours_card' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.neighbours_nonadjacent {y x z : AKLT.Defs.Plane} (hx : x ∈ AKLT.Defs.neighbours y)
  (hz : z ∈ AKLT.Defs.neighbours y) : ¬AKLT.Defs.Adjacent x z
'AKLT.W.REC016.neighbours_nonadjacent' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.dist_triangle (x y z : AKLT.Defs.Plane) :
  AKLT.Defs.latticeDist x z ≤ AKLT.Defs.latticeDist x y + AKLT.Defs.latticeDist y z
'AKLT.W.REC016.dist_triangle' depends on axioms: [propext, Quot.sound]
AKLT.W.REC016.original_leg {G : Finset AKLT.Defs.Plane} {e : AKLT.Defs.Plane × AKLT.Defs.Plane}
  (he : e ∈ AKLT.Defs.originalLegs G) : e.1 ∈ G ∧ e.2 ∈ AKLT.Defs.neighbours e.1 ∧ e.2 ∉ G
'AKLT.W.REC016.original_leg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.neighbour_no_leg {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {y x : AKLT.Defs.Plane}
  (hy : D.AdmissibleStart y) (hx : x ∈ AKLT.Defs.neighbours y) (e : AKLT.Defs.Plane × AKLT.Defs.Plane) :
  e ∈ AKLT.Defs.originalLegs G → e.1 ≠ x
'AKLT.W.REC016.neighbour_no_leg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.removed_active {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y x : AKLT.Defs.Plane) :
  x ∈ (AKLT.Defs.removeSite D y).active ↔ x ∈ D.active ∧ x ≠ y
'AKLT.W.REC016.removed_active' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.present_symm {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {x y : AKLT.Defs.Plane}
  (h : D.Present x y) : D.Present y x
'AKLT.W.REC016.present_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.present_neighbour {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} (hD : D.LocalRules)
  {x y : AKLT.Defs.Plane} (h : D.Present x y) : y ∈ D.presentNeighbours x
'AKLT.W.REC016.present_neighbour' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.removed_degree {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {y x : AKLT.Defs.Plane}
  (hD : D.LocalRules) (hx : x ∈ D.presentNeighbours y) : ((AKLT.Defs.removeSite D y).presentNeighbours x).card ≤ 3
'AKLT.W.REC016.removed_degree' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.FiniteGraph.weight_nonneg.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [DecidableEq α] [Fintype β]
  (s : α → AKLT.Defs.Status) (l r : β → α) (P : (α → AKLT.Defs.SpinLetter) → ℝ)
  (hP : ∀ (σ : α → AKLT.Defs.SpinLetter), 0 ≤ P σ) (σ : α → AKLT.Defs.SpinLetter) :
  0 ≤ AKLT.W.REC016.FiniteGraph.weight s l r P σ
'AKLT.W.REC016.FiniteGraph.weight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.FiniteGraph.other_ne.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [DecidableEq α] [Fintype β]
  (l r : β → α) (hloop : ∀ (e : β), l e ≠ r e) (x : α) (e : { e // AKLT.W.REC016.FiniteGraph.Inc l r x e }) :
  AKLT.W.REC016.FiniteGraph.other l r x ↑e ≠ x
'AKLT.W.REC016.FiniteGraph.other_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.FiniteGraph.other_ne_second.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [DecidableEq α]
  [Fintype β] (l r : β → α) (x y : α)
  (hsep : ∀ (e : β), AKLT.W.REC016.FiniteGraph.Inc l r x e → ¬AKLT.W.REC016.FiniteGraph.Inc l r y e)
  (e : { e // AKLT.W.REC016.FiniteGraph.Inc l r x e }) : AKLT.W.REC016.FiniteGraph.other l r x ↑e ≠ y
'AKLT.W.REC016.FiniteGraph.other_ne_second' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.FiniteGraph.refresh_other.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [DecidableEq α] [Fintype β]
  (l r : β → α) (hloop : ∀ (e : β), l e ≠ r e) {x y : α}
  (hsep : ∀ (e : β), AKLT.W.REC016.FiniteGraph.Inc l r x e → ¬AKLT.W.REC016.FiniteGraph.Inc l r y e)
  (σ : α → AKLT.Defs.SpinLetter) (a b : AKLT.Defs.SpinLetter) (e : { e // AKLT.W.REC016.FiniteGraph.Inc l r x e }) :
  Function.update (Function.update σ x a) y b (AKLT.W.REC016.FiniteGraph.other l r x ↑e) =
    σ (AKLT.W.REC016.FiniteGraph.other l r x ↑e)
'AKLT.W.REC016.FiniteGraph.refresh_other' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.FiniteGraph.vertex_product.{u_1} {α : Type u_1} [Fintype α] [DecidableEq α] (s : α → AKLT.Defs.Status)
  {x y : α} (hxy : x ≠ y) (σ : α → AKLT.Defs.SpinLetter) (a b : AKLT.Defs.SpinLetter) :
  ∏ z, AKLT.Defs.spinWeight (s z) (Function.update (Function.update σ x a) y b z) =
    AKLT.Defs.spinWeight (s x) a * AKLT.Defs.spinWeight (s y) b *
      ∏ z ∈ (Finset.univ.erase x).erase y, AKLT.Defs.spinWeight (s z) (σ z)
'AKLT.W.REC016.FiniteGraph.vertex_product' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.FiniteGraph.fibre_factorization.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [DecidableEq α]
  [Fintype β] (s : α → AKLT.Defs.Status) (l r : β → α) (hloop : ∀ (e : β), l e ≠ r e) {x y : α} (hxy : x ≠ y)
  (hsep : ∀ (e : β), AKLT.W.REC016.FiniteGraph.Inc l r x e → ¬AKLT.W.REC016.FiniteGraph.Inc l r y e)
  (P : (α → AKLT.Defs.SpinLetter) → ℝ) (hP : ∀ (σ : α → AKLT.Defs.SpinLetter), 0 ≤ P σ)
  (hrefresh :
    ∀ (σ : α → AKLT.Defs.SpinLetter) (a b : AKLT.Defs.SpinLetter),
      P (Function.update (Function.update σ x a) y b) = P σ)
  (σ : α → AKLT.Defs.SpinLetter) :
  ∃ C,
    0 ≤ C ∧
      ∀ (a b : AKLT.Defs.SpinLetter),
        AKLT.W.REC016.FiniteGraph.weight s l r P (Function.update (Function.update σ x a) y b) =
          C *
              (AKLT.Defs.spinWeight (s x) a *
                ∏ e,
                  (1 +
                    AKLT.Defs.dot (AKLT.Defs.spinVector a)
                      (AKLT.Defs.spinVector (σ (AKLT.W.REC016.FiniteGraph.other l r x ↑e))))) *
            (AKLT.Defs.spinWeight (s y) b *
              ∏ e,
                (1 +
                  AKLT.Defs.dot (AKLT.Defs.spinVector b)
                    (AKLT.Defs.spinVector (σ (AKLT.W.REC016.FiniteGraph.other l r y ↑e)))))
'AKLT.W.REC016.FiniteGraph.fibre_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.FiniteGraph.pair_lower.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [DecidableEq α] [Fintype β]
  (s : α → AKLT.Defs.Status) (l r : β → α) (hloop : ∀ (e : β), l e ≠ r e) {x y : α} (hxy : x ≠ y)
  (hsep : ∀ (e : β), AKLT.W.REC016.FiniteGraph.Inc l r x e → ¬AKLT.W.REC016.FiniteGraph.Inc l r y e)
  (hxdeg : Fintype.card { e // AKLT.W.REC016.FiniteGraph.Inc l r x e } ≤ 3)
  (hydeg : Fintype.card { e // AKLT.W.REC016.FiniteGraph.Inc l r y e } ≤ 3)
  (hsx : s x = AKLT.Defs.Status.U ∨ s x = AKLT.Defs.Status.D)
  (hsy : s y = AKLT.Defs.Status.U ∨ s y = AKLT.Defs.Status.D) (P : (α → AKLT.Defs.SpinLetter) → ℝ)
  (hP : ∀ (σ : α → AKLT.Defs.SpinLetter), 0 ≤ P σ)
  (hrefresh :
    ∀ (σ : α → AKLT.Defs.SpinLetter) (a b : AKLT.Defs.SpinLetter),
      P (Function.update (Function.update σ x a) y b) = P σ) :
  -(9 / 25) ≤
    (∑ σ,
        AKLT.W.REC016.FiniteGraph.weight s l r P σ *
          AKLT.Defs.dot (AKLT.Defs.spinVector (σ x)) (AKLT.Defs.spinVector (σ y))) /
      ∑ σ, AKLT.W.REC016.FiniteGraph.weight s l r P σ
'AKLT.W.REC016.FiniteGraph.pair_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.neighbour_survives {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) {y x : AKLT.Defs.Plane}
  (hx : x ∈ D.presentNeighbours y) : x ∈ (AKLT.Defs.removeSite D y).active
'AKLT.W.REC016.neighbour_survives' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.network_pair_lower {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (x y : ↥D.active) (hxy : x ≠ y) (hnonadj : ¬AKLT.Defs.Adjacent ↑x ↑y)
  (hxdeg :
    Fintype.card { e // AKLT.W.REC016.FiniteGraph.Inc (AKLT.W.REC016.bondLeft D) (AKLT.W.REC016.bondRight D) x e } ≤ 3)
  (hydeg :
    Fintype.card { e // AKLT.W.REC016.FiniteGraph.Inc (AKLT.W.REC016.bondLeft D) (AKLT.W.REC016.bondRight D) y e } ≤ 3)
  (hxleg : ∀ (e : ↥(AKLT.Defs.originalLegs G)), (↑e).1 ≠ ↑x)
  (hyleg : ∀ (e : ↥(AKLT.Defs.originalLegs G)), (↑e).1 ≠ ↑y) :
  -(9 / 25) ≤ D.expectation τ b fun v => AKLT.Defs.dot (v ↑x) (v ↑y)
'AKLT.W.REC016.network_pair_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.removed_pair_lower (a : AKLT.Blueprint.Rec.Departure) {x z : AKLT.Defs.Plane}
  (hx : x ∈ a.D.presentNeighbours a.y) (hz : z ∈ a.D.presentNeighbours a.y) (hxz : x ≠ z) (b : Bool) :
  -(9 / 25) ≤ AKLT.Defs.removedPairMean a.D a.τ b a.y x z
'AKLT.W.REC016.removed_pair_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.removed_pair_free_nonneg (a : AKLT.Blueprint.Rec.Departure) {x z : AKLT.Defs.Plane}
  (hx : x ∈ a.D.presentNeighbours a.y) (hz : z ∈ a.D.presentNeighbours a.y) :
  0 ≤ AKLT.Defs.removedPairMean a.D a.τ false a.y x z
'AKLT.W.REC016.removed_pair_free_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.two_mean_lower (a : AKLT.Blueprint.Rec.Departure) (f : AKLT.Defs.Plane)
  (hPresent : a.D.presentNeighbours a.y = {a.o, f}) (hne : a.o ≠ f) :
  22 / 25 ≤ AKLT.Blueprint.Rec.responseI₂ a.D a.τ true a.y a.o f ∧
    1 ≤ AKLT.Blueprint.Rec.responseI₂ a.D a.τ false a.y a.o f
'AKLT.W.REC016.two_mean_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.main : AKLT.Blueprint.Rec.BetaPrimeUniformStatement
'AKLT.W.REC016.main' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.bond_present {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} (e : ↥D.bonds) :
  D.Present (↑e).1 (↑e).2
'AKLT.W.REC016.bond_present' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.bond_left_active {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} (e : ↥D.bonds) : (↑e).1 ∈ D.active
'AKLT.W.REC016.bond_left_active' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.bond_right_active {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} (e : ↥D.bonds) :
  (↑e).2 ∈ D.active
'AKLT.W.REC016.bond_right_active' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.bond_positive {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} (e : ↥D.bonds) :
  (↑e).2.1 + (↑e).2.2 = (↑e).1.1 + (↑e).1.2 + 1
'AKLT.W.REC016.bond_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.bond_no_loop {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} (e : ↥D.bonds) :
  AKLT.W.REC016.bondLeft D e ≠ AKLT.W.REC016.bondRight D e
'AKLT.W.REC016.bond_no_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.free_pair_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (x y : ↥D.active) : 0 ≤ D.partition τ false fun v => AKLT.Defs.dot (v ↑x) (v ↑y)
'AKLT.W.REC016.free_pair_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.golden_sq : AKLT.Defs.goldenRatio ^ 2 = AKLT.Defs.goldenRatio + 1
'AKLT.W.REC016.golden_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.radius_pos : 0 < AKLT.Defs.icoRadius
'AKLT.W.REC016.radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.radius_sq : AKLT.Defs.icoRadius ^ 2 = AKLT.Defs.goldenRatio + 2
'AKLT.W.REC016.radius_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.radius_four : AKLT.Defs.icoRadius ^ 4 = 5 * AKLT.Defs.goldenRatio ^ 2
'AKLT.W.REC016.radius_four' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.radius_cube : AKLT.Defs.icoRadius ^ 3 = AKLT.Defs.icoRadius * (AKLT.Defs.goldenRatio + 2)
'AKLT.W.REC016.radius_cube' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.golden_four : AKLT.Defs.goldenRatio ^ 4 = 3 * AKLT.Defs.goldenRatio + 2
'AKLT.W.REC016.golden_four' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.ico_unit (j : AKLT.Defs.IcoLetter) : AKLT.Defs.normSq (AKLT.Defs.icoVector j) = 1
'AKLT.W.REC016.ico_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.spin_ball (j : AKLT.Defs.SpinLetter) : AKLT.Defs.normSq (AKLT.Defs.spinVector j) ≤ 1
'AKLT.W.REC016.spin_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.dot_comm (a b : AKLT.Defs.Vec3) : AKLT.Defs.dot a b = AKLT.Defs.dot b a
'AKLT.W.REC016.dot_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.dot_sq_le (a b : AKLT.Defs.Vec3) : AKLT.Defs.dot a b ^ 2 ≤ AKLT.Defs.normSq a * AKLT.Defs.normSq b
'AKLT.W.REC016.dot_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.normSq_nonneg (a : AKLT.Defs.Vec3) : 0 ≤ AKLT.Defs.normSq a
'AKLT.W.REC016.normSq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.ball_dot (a b : AKLT.Defs.Vec3) (ha : AKLT.Defs.normSq a ≤ 1) (hb : AKLT.Defs.normSq b ≤ 1) :
  -1 ≤ AKLT.Defs.dot a b ∧ AKLT.Defs.dot a b ≤ 1
'AKLT.W.REC016.ball_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.triple_normalizer (a b c : AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun v =>
      (1 + AKLT.Defs.dot v a) * (1 + AKLT.Defs.dot v b) * (1 + AKLT.Defs.dot v c)) =
    1 + (AKLT.Defs.dot a b + AKLT.Defs.dot a c + AKLT.Defs.dot b c) / 3
'AKLT.W.REC016.triple_normalizer' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.triple_numerator (a b c : AKLT.Defs.Vec3) (i : Fin 3) :
  (15 *
      AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun v =>
        v i * ((1 + AKLT.Defs.dot v a) * (1 + AKLT.Defs.dot v b) * (1 + AKLT.Defs.dot v c))) =
    5 * (a i + b i + c i) + a i * AKLT.Defs.dot b c + b i * AKLT.Defs.dot a c + c i * AKLT.Defs.dot a b
'AKLT.W.REC016.triple_numerator' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.triple_sos (a b c : AKLT.Defs.Vec3) :
  (9 + 3 * (AKLT.Defs.dot a b + AKLT.Defs.dot a c + AKLT.Defs.dot b c)) ^ 2 -
      AKLT.Defs.normSq (AKLT.W.REC016.tripleVector a b c) =
    4 *
              ((AKLT.Defs.dot b c - AKLT.Defs.dot a c) ^ 2 + (AKLT.Defs.dot b c - AKLT.Defs.dot a b) ^ 2 +
                (AKLT.Defs.dot a c - AKLT.Defs.dot a b) ^ 2) +
            6 * (1 - AKLT.Defs.dot a b) * (1 - AKLT.Defs.dot a c) * (1 - AKLT.Defs.dot b c) +
          (1 - AKLT.Defs.normSq a) * (5 + AKLT.Defs.dot b c) ^ 2 +
        (1 - AKLT.Defs.normSq b) * (5 + AKLT.Defs.dot a c) ^ 2 +
      (1 - AKLT.Defs.normSq c) * (5 + AKLT.Defs.dot a b) ^ 2
'AKLT.W.REC016.triple_sos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.triple_bound (a b c : AKLT.Defs.Vec3) (ha : AKLT.Defs.normSq a ≤ 1) (hb : AKLT.Defs.normSq b ≤ 1)
  (hc : AKLT.Defs.normSq c ≤ 1) :
  have W := fun v => (1 + AKLT.Defs.dot v a) * (1 + AKLT.Defs.dot v b) * (1 + AKLT.Defs.dot v c);
  1 / 2 ≤ AKLT.Defs.siteFunctional AKLT.Defs.Status.U W ∧
    (AKLT.Defs.normSq fun i => AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun v => v i * W v) ≤
      (3 / 5 * AKLT.Defs.siteFunctional AKLT.Defs.Status.U W) ^ 2
'AKLT.W.REC016.triple_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.normSq_div (v : AKLT.Defs.Vec3) (d : ℝ) : (AKLT.Defs.normSq fun i => v i / d) = AKLT.Defs.normSq v / d ^ 2
'AKLT.W.REC016.normSq_div' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.site_mixture (f : AKLT.Defs.Vec3 → ℝ) :
  AKLT.Defs.siteFunctional AKLT.Defs.Status.D f = 3 / 5 * AKLT.Defs.siteFunctional AKLT.Defs.Status.U f + 2 / 5 * f 0
'AKLT.W.REC016.site_mixture' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.local_bound {k : ℕ} (hk : k ≤ 3) (a : Fin k → AKLT.Defs.Vec3)
  (ha : ∀ (i : Fin k), AKLT.Defs.normSq (a i) ≤ 1) (s : AKLT.Defs.Status)
  (hs : s = AKLT.Defs.Status.U ∨ s = AKLT.Defs.Status.D) :
  0 < AKLT.Defs.siteFunctional s (AKLT.Defs.localProduct a) ∧ AKLT.Defs.normSq (AKLT.Defs.localMean s a) ≤ (3 / 5) ^ 2
'AKLT.W.REC016.local_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.small_dot (a b : AKLT.Defs.Vec3) (ha : AKLT.Defs.normSq a ≤ (3 / 5) ^ 2)
  (hb : AKLT.Defs.normSq b ≤ (3 / 5) ^ 2) : -(9 / 25) ≤ AKLT.Defs.dot a b
'AKLT.W.REC016.small_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC016.legWeight {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (σ : ↥D.active → AKLT.Defs.SpinLetter) : ℝ
AKLT.W.REC016.FiniteGraph.Inc.{u_1, u_2} {α : Type u_1} {β : Type u_2} (l r : β → α) (x : α) (e : β) : Prop
AKLT.W.REC016.FiniteGraph.other.{u_1, u_2} {α : Type u_1} {β : Type u_2} [DecidableEq α] (l r : β → α) (x : α) (e : β) :
  α
AKLT.W.REC016.FiniteGraph.weight.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Fintype α] [Fintype β]
  (s : α → AKLT.Defs.Status) (l r : β → α) (P : (α → AKLT.Defs.SpinLetter) → ℝ) (σ : α → AKLT.Defs.SpinLetter) : ℝ
AKLT.W.REC016.bondLeft {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (e : ↥D.bonds) : ↥D.active
AKLT.W.REC016.bondRight {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (e : ↥D.bonds) : ↥D.active
AKLT.W.REC016.dotPoly.{u_1} {α : Type u_1} (x y : α) : MvPolynomial (α × Fin 3) ℕ
AKLT.W.REC016.freePoly {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) : MvPolynomial (↥D.active × Fin 3) ℕ
AKLT.W.REC016.tripleVector (a b c : AKLT.Defs.Vec3) : AKLT.Defs.Vec3
```

## ORCH-SUMMARY

- Delivered `AKLT/W/REC016/Main.lean` and ten helper/audit modules in the assigned directory.
- Exact export: `AKLT.W.REC016.main : AKLT.Blueprint.Rec.BetaPrimeUniformStatement`.
- Required module build and an independent exact-type example both pass.
- All 80 exported theorem axiom lists contain only permitted axioms.
- No residual statements, missing premises, or open proof obligations remain.
- No existing statement/library files were edited; no other leaf is used as an assumption.
- Route changes: direct finite graph indexing, direct ball-field SOS, all-degree free positivity, and a sufficient Mathlib log remainder.
- Only finite heartbeat adjustment: 1,200,000 for `free_pair_nonneg`.
- Orchestrator action: accept the unconditional proof; no additional dependencies are required.
