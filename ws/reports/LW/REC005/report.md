STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC005/AKLT/W/REC005/Main.lean) — Exact requested theorem.
- [Free.lean](/home/ubuntu/aklt/wt/LW_REC005/AKLT/W/REC005/Free.lean) — Coordinate-monomial positivity, polynomial expansion, and free pair positivity.
- [Local.lean](/home/ubuntu/aklt/wt/LW_REC005/AKLT/W/REC005/Local.lean) — Icosahedron norm and moment tensors through degree four.
- [Means.lean](/home/ubuntu/aklt/wt/LW_REC005/AKLT/W/REC005/Means.lean) — Integrated three-factor scalar and vector formulas.
- [Bounds.lean](/home/ubuntu/aklt/wt/LW_REC005/AKLT/W/REC005/Bounds.lean) — Unit-field SOS bound, zero fields, U/D laws, and lists of at most three spin fields.
- [Fibres.lean](/home/ubuntu/aklt/wt/LW_REC005/AKLT/W/REC005/Fibres.lean) — Explicit double sums, coordinate-update averaging, and the pair bound from unnormalized fibres.
- [Graph.lean](/home/ubuntu/aklt/wt/LW_REC005/AKLT/W/REC005/Graph.lean) — Two-site factorization for arbitrary finite vertex and edge types.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_REC005/AKLT/W/REC005/Geometry.lean) — Lattice adjacency, protected-layer exclusion of original legs, and removal geometry.
- [Network.lean](/home/ubuntu/aklt/wt/LW_REC005/AKLT/W/REC005/Network.lean) — Active-site/bond reindexing, the three-bond degree bound, and the removed pair interval.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC005/AKLT/W/REC005/Audit.lean) — Exact-type example and type/axiom checks for all 122 exported declarations.

## Result and proof

```lean
theorem AKLT.W.REC005.main :
    AKLT.Blueprint.Rec.TwoMeanIntervalsStatement
```

The theorem has no additional hypotheses or residual statements. It proves both pin-choice bounds `22/25 ≤ responseI₂ ≤ 28/25` and the free lower bound `1 ≤ responseI₂`.

The pinned estimate is obtained from explicit finite fibres. The second and fourth moment tensors give the integrated local numerator and denominator. The three-unit-field sum-of-squares identity bounds the local mean by `3/5`; zero fields and the depleted law are handled directly. Each deleted-network fibre then has pair mean between `-9/25` and `9/25`. Summing unnormalized fibres avoids dividing by zero-mass fibres. The global zero-denominator case is handled explicitly using the actual Lean definition of division.

The lattice bridge indexes vertices by the actual finite active subtype and edges by the actual bond subtype. Distinct neighbours of the removed departure are nonadjacent; each loses the bond slot toward the removed site and has at most three remaining bonds. The protected-layer definition proves that both endpoints have no original legs. All original leg factors elsewhere remain in the weight.

For the free estimate, the concrete common icosahedral alphabet has nonnegative coordinate-monomial averages in every degree. Expanding the bond product and inserted scalar product with nonnegative coefficients proves free pair positivity directly. The final response bounds are exact rational arithmetic.

No other blueprint leaf is used as an assumed lemma. All new proof files are inside the assigned directory; existing project files and frozen definitions were not changed.

## Exported declarations and axioms

All 122 declarations, including the helper definitions and every helper theorem, are listed with their exact Lean-printed types and `#print axioms` output in the appendix below. The reproducible checks are in `Audit.lean`; the raw output is also saved as [audit.log](/home/ubuntu/aklt/reports/LW/REC005/audit.log), and the name/file index is [exports.tsv](/home/ubuntu/aklt/reports/LW/REC005/exports.tsv).

The required theorem reports:

```text
'AKLT.W.REC005.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The union of axioms across all 122 declarations is exactly `{propext, Classical.choice, Quot.sound}`. The audit found no missing declarations or Lean errors. The source scan found none of the forbidden constructs.

## Build and validation

- `lake build AKLT.W.REC005.Main` — success. Final incremental verification: **6.18 seconds**, saved in [build-main.log](/home/ubuntu/aklt/reports/LW/REC005/build-main.log) and [build-main.time](/home/ubuntu/aklt/reports/LW/REC005/build-main.time). The first successful compilation reported 4.4 seconds for `Network` and 3.4 seconds for `Main`; the moment calculation module `Local` previously compiled in 83 seconds.
- `lake env lean AKLT/W/REC005/Audit.lean` — success in **4.34 seconds**. This includes `example : AKLT.Blueprint.Rec.TwoMeanIntervalsStatement := AKLT.W.REC005.main`, and checks all exported declarations and axioms.
- [audit-summary.json](/home/ubuntu/aklt/reports/LW/REC005/audit-summary.json): 122 expected, 122 audited, no missing declarations, no errors, only the three allowed axioms.
- There are nonfatal style/linter warnings in some helpers. No proof or compilation warnings indicate missing proofs.

## Open issues

None. There are no residual statements and no dependency proofs to supply.

## Complete declaration and axiom appendix

```text
AKLT.W.REC005.golden_pos : 0 < AKLT.Defs.goldenRatio
'AKLT.W.REC005.golden_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.radius_pos : 0 < AKLT.Defs.icoRadius
'AKLT.W.REC005.radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.signed_power_sum_nonneg (t : ℝ) (ht : 0 ≤ t) (n : ℕ) : 0 ≤ t ^ n + (-t) ^ n
'AKLT.W.REC005.signed_power_sum_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.ico_monomial_nonneg (m : Fin 3 → ℕ) : 0 ≤ AKLT.Defs.moment fun v => ∏ i, v i ^ m i
'AKLT.W.REC005.ico_monomial_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.site_monomial_nonneg (s : AKLT.Defs.Status) (m : Fin 3 → ℕ) :
  0 ≤ AKLT.Defs.siteFunctional s fun v => ∏ i, v i ^ m i
'AKLT.W.REC005.site_monomial_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.product_monomial_nonneg.{u_1} {ι : Type u_1} [Fintype ι] (s : ι → AKLT.Defs.Status) (m : ι × Fin 3 →₀ ℕ) :
  0 ≤ AKLT.Defs.productFunctional s fun v => ∏ z, v z.1 z.2 ^ m z
'AKLT.W.REC005.product_monomial_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.NonnegCoeffs.{u_1} {ι : Type u_1} (p : MvPolynomial ι ℝ) : Prop
'AKLT.W.REC005.NonnegCoeffs' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.nonnegCoeffs_one.{u_1} {ι : Type u_1} : AKLT.W.REC005.NonnegCoeffs 1
'AKLT.W.REC005.nonnegCoeffs_one' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.nonnegCoeffs_zero.{u_1} {ι : Type u_1} : AKLT.W.REC005.NonnegCoeffs 0
'AKLT.W.REC005.nonnegCoeffs_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.nonnegCoeffs_X.{u_1} {ι : Type u_1} (i : ι) : AKLT.W.REC005.NonnegCoeffs (MvPolynomial.X i)
'AKLT.W.REC005.nonnegCoeffs_X' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.nonnegCoeffs_add.{u_1} {ι : Type u_1} {p q : MvPolynomial ι ℝ} (hp : AKLT.W.REC005.NonnegCoeffs p)
  (hq : AKLT.W.REC005.NonnegCoeffs q) : AKLT.W.REC005.NonnegCoeffs (p + q)
'AKLT.W.REC005.nonnegCoeffs_add' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.nonnegCoeffs_mul.{u_1} {ι : Type u_1} {p q : MvPolynomial ι ℝ} (hp : AKLT.W.REC005.NonnegCoeffs p)
  (hq : AKLT.W.REC005.NonnegCoeffs q) : AKLT.W.REC005.NonnegCoeffs (p * q)
'AKLT.W.REC005.nonnegCoeffs_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.nonnegCoeffs_sum.{u_1, u_2} {ι : Type u_1} {α : Type u_2} (t : Finset α) (p : α → MvPolynomial ι ℝ)
  (hp : ∀ a ∈ t, AKLT.W.REC005.NonnegCoeffs (p a)) : AKLT.W.REC005.NonnegCoeffs (∑ a ∈ t, p a)
'AKLT.W.REC005.nonnegCoeffs_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.nonnegCoeffs_prod.{u_1, u_2} {ι : Type u_1} {α : Type u_2} (t : Finset α) (p : α → MvPolynomial ι ℝ)
  (hp : ∀ a ∈ t, AKLT.W.REC005.NonnegCoeffs (p a)) : AKLT.W.REC005.NonnegCoeffs (∏ a ∈ t, p a)
'AKLT.W.REC005.nonnegCoeffs_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.product_polynomial_nonneg.{u_1} {ι : Type u_1} [Fintype ι] (s : ι → AKLT.Defs.Status)
  (p : MvPolynomial (ι × Fin 3) ℝ) (hp : AKLT.W.REC005.NonnegCoeffs p) :
  0 ≤ AKLT.Defs.productFunctional s fun v => (MvPolynomial.eval fun z => v z.1 z.2) p
'AKLT.W.REC005.product_polynomial_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.coordinatePoly {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (x : AKLT.Defs.Plane) (i : Fin 3) :
  MvPolynomial (↥D.active × Fin 3) ℝ
'AKLT.W.REC005.coordinatePoly' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.pairPoly {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (a b : AKLT.Defs.Plane) :
  MvPolynomial (↥D.active × Fin 3) ℝ
'AKLT.W.REC005.pairPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.bondPoly {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) : MvPolynomial (↥D.active × Fin 3) ℝ
'AKLT.W.REC005.bondPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.coordinatePoly_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (x : AKLT.Defs.Plane)
  (i : Fin 3) : AKLT.W.REC005.NonnegCoeffs (AKLT.W.REC005.coordinatePoly D x i)
'AKLT.W.REC005.coordinatePoly_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.pairPoly_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (a b : AKLT.Defs.Plane) :
  AKLT.W.REC005.NonnegCoeffs (AKLT.W.REC005.pairPoly D a b)
'AKLT.W.REC005.pairPoly_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.bondPoly_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) :
  AKLT.W.REC005.NonnegCoeffs (AKLT.W.REC005.bondPoly D)
'AKLT.W.REC005.bondPoly_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.eval_coordinatePoly {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (n : ↥D.active → AKLT.Defs.SpinLetter) (x : AKLT.Defs.Plane) (i : Fin 3) :
  (MvPolynomial.eval fun z => AKLT.Defs.spinVector (n z.1) z.2) (AKLT.W.REC005.coordinatePoly D x i) = D.spins n x i
'AKLT.W.REC005.eval_coordinatePoly' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.eval_pairPoly {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (n : ↥D.active → AKLT.Defs.SpinLetter) (a b : AKLT.Defs.Plane) :
  (MvPolynomial.eval fun z => AKLT.Defs.spinVector (n z.1) z.2) (AKLT.W.REC005.pairPoly D a b) =
    AKLT.Defs.dot (D.spins n a) (D.spins n b)
'AKLT.W.REC005.eval_pairPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.free_partition_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) : 0 ≤ D.partition τ false fun x => 1
'AKLT.W.REC005.free_partition_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.free_pair_partition_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (a b : AKLT.Defs.Plane) : 0 ≤ D.partition τ false fun n => AKLT.Defs.dot (n a) (n b)
'AKLT.W.REC005.free_pair_partition_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.free_pair_mean_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (a b : AKLT.Defs.Plane) : 0 ≤ D.expectation τ false fun n => AKLT.Defs.dot (n a) (n b)
'AKLT.W.REC005.free_pair_mean_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.golden_sq : AKLT.Defs.goldenRatio ^ 2 = AKLT.Defs.goldenRatio + 1
'AKLT.W.REC005.golden_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.radius_sq : AKLT.Defs.icoRadius ^ 2 = AKLT.Defs.goldenRatio + 2
'AKLT.W.REC005.radius_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.radius_four : AKLT.Defs.icoRadius ^ 4 = 5 * AKLT.Defs.goldenRatio ^ 2
'AKLT.W.REC005.radius_four' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.ico_unit (j : AKLT.Defs.IcoLetter) : AKLT.Defs.normSq (AKLT.Defs.icoVector j) = 1
'AKLT.W.REC005.ico_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.normSq_nonneg (v : AKLT.Defs.Vec3) : 0 ≤ AKLT.Defs.normSq v
'AKLT.W.REC005.normSq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.dot_sq_le (v w : AKLT.Defs.Vec3) : AKLT.Defs.dot v w ^ 2 ≤ AKLT.Defs.normSq v * AKLT.Defs.normSq w
'AKLT.W.REC005.dot_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.dot_unit_bounds (v w : AKLT.Defs.Vec3) (hv : AKLT.Defs.normSq v = 1) (hw : AKLT.Defs.normSq w = 1) :
  -1 ≤ AKLT.Defs.dot v w ∧ AKLT.Defs.dot v w ≤ 1
'AKLT.W.REC005.dot_unit_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.moment_second (i j : Fin 3) : (AKLT.Defs.moment fun v => v i * v j) = if i = j then 1 / 3 else 0
'AKLT.W.REC005.moment_second' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.moment_first (i : Fin 3) : (AKLT.Defs.moment fun v => v i) = 0
'AKLT.W.REC005.moment_first' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.moment_third (i j k : Fin 3) : (AKLT.Defs.moment fun v => v i * v j * v k) = 0
'AKLT.W.REC005.moment_third' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.moment_fourth (i j k l : Fin 3) :
  (AKLT.Defs.moment fun v => v i * v j * v k * v l) =
    (((if i = j ∧ k = l then 1 else 0) + if i = k ∧ j = l then 1 else 0) + if i = l ∧ j = k then 1 else 0) / 15
'AKLT.W.REC005.moment_fourth' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.moment_add (f g : AKLT.Defs.Vec3 → ℝ) :
  (AKLT.Defs.moment fun v => f v + g v) = AKLT.Defs.moment f + AKLT.Defs.moment g
'AKLT.W.REC005.moment_add' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.moment_const_mul (r : ℝ) (f : AKLT.Defs.Vec3 → ℝ) :
  (AKLT.Defs.moment fun v => r * f v) = r * AKLT.Defs.moment f
'AKLT.W.REC005.moment_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.moment_mul_const (f : AKLT.Defs.Vec3 → ℝ) (r : ℝ) :
  (AKLT.Defs.moment fun v => f v * r) = AKLT.Defs.moment f * r
'AKLT.W.REC005.moment_mul_const' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.moment_sum.{u_1} {ι : Type u_1} [Fintype ι] (f : ι → AKLT.Defs.Vec3 → ℝ) :
  (AKLT.Defs.moment fun v => ∑ i, f i v) = ∑ i, AKLT.Defs.moment (f i)
'AKLT.W.REC005.moment_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.moment_one : (AKLT.Defs.moment fun x => 1) = 1
'AKLT.W.REC005.moment_one' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.moment_dot (a : AKLT.Defs.Vec3) : (AKLT.Defs.moment fun v => AKLT.Defs.dot v a) = 0
'AKLT.W.REC005.moment_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.moment_dot_two (a b : AKLT.Defs.Vec3) :
  (AKLT.Defs.moment fun v => AKLT.Defs.dot v a * AKLT.Defs.dot v b) = AKLT.Defs.dot a b / 3
'AKLT.W.REC005.moment_dot_two' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.moment_dot_three (a b c : AKLT.Defs.Vec3) :
  (AKLT.Defs.moment fun v => AKLT.Defs.dot v a * AKLT.Defs.dot v b * AKLT.Defs.dot v c) = 0
'AKLT.W.REC005.moment_dot_three' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.moment_coord_dot (i : Fin 3) (a : AKLT.Defs.Vec3) :
  (AKLT.Defs.moment fun v => v i * AKLT.Defs.dot v a) = a i / 3
'AKLT.W.REC005.moment_coord_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.moment_coord_dot_two (i : Fin 3) (a b : AKLT.Defs.Vec3) :
  (AKLT.Defs.moment fun v => v i * AKLT.Defs.dot v a * AKLT.Defs.dot v b) = 0
'AKLT.W.REC005.moment_coord_dot_two' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.moment_coord_dot_three (i : Fin 3) (a b c : AKLT.Defs.Vec3) :
  (AKLT.Defs.moment fun v => v i * AKLT.Defs.dot v a * AKLT.Defs.dot v b * AKLT.Defs.dot v c) =
    (a i * AKLT.Defs.dot b c + b i * AKLT.Defs.dot a c + c i * AKLT.Defs.dot a b) / 15
'AKLT.W.REC005.moment_coord_dot_three' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.tripleWeight (a b c v : AKLT.Defs.Vec3) : ℝ
'AKLT.W.REC005.tripleWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.tripleP (a b c : AKLT.Defs.Vec3) : ℝ
'AKLT.W.REC005.tripleP' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.tripleV (a b c : AKLT.Defs.Vec3) : AKLT.Defs.Vec3
'AKLT.W.REC005.tripleV' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.triple_normalizer (a b c : AKLT.Defs.Vec3) :
  AKLT.Defs.moment (AKLT.W.REC005.tripleWeight a b c) = 1 + AKLT.W.REC005.tripleP a b c / 3
'AKLT.W.REC005.triple_normalizer' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.triple_numerator (a b c : AKLT.Defs.Vec3) (i : Fin 3) :
  (15 * AKLT.Defs.moment fun v => v i * AKLT.W.REC005.tripleWeight a b c v) = AKLT.W.REC005.tripleV a b c i
'AKLT.W.REC005.triple_numerator' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.dot_comm (a b : AKLT.Defs.Vec3) : AKLT.Defs.dot a b = AKLT.Defs.dot b a
'AKLT.W.REC005.dot_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.normSq_div (v : AKLT.Defs.Vec3) (r : ℝ) : (AKLT.Defs.normSq fun i => v i / r) = AKLT.Defs.normSq v / r ^ 2
'AKLT.W.REC005.normSq_div' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.normSq_smul (r : ℝ) (v : AKLT.Defs.Vec3) :
  (AKLT.Defs.normSq fun i => r * v i) = r ^ 2 * AKLT.Defs.normSq v
'AKLT.W.REC005.normSq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.tripleV_norm (a b c : AKLT.Defs.Vec3) :
  AKLT.Defs.normSq (AKLT.W.REC005.tripleV a b c) =
    (5 + AKLT.Defs.dot b c) ^ 2 * AKLT.Defs.normSq a + (5 + AKLT.Defs.dot a c) ^ 2 * AKLT.Defs.normSq b +
            (5 + AKLT.Defs.dot a b) ^ 2 * AKLT.Defs.normSq c +
          2 * (5 + AKLT.Defs.dot b c) * (5 + AKLT.Defs.dot a c) * AKLT.Defs.dot a b +
        2 * (5 + AKLT.Defs.dot b c) * (5 + AKLT.Defs.dot a b) * AKLT.Defs.dot a c +
      2 * (5 + AKLT.Defs.dot a c) * (5 + AKLT.Defs.dot a b) * AKLT.Defs.dot b c
'AKLT.W.REC005.tripleV_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.unit_triple_sos (a b c : AKLT.Defs.Vec3) (ha : AKLT.Defs.normSq a = 1) (hb : AKLT.Defs.normSq b = 1)
  (hc : AKLT.Defs.normSq c = 1) :
  (9 + 3 * AKLT.W.REC005.tripleP a b c) ^ 2 - AKLT.Defs.normSq (AKLT.W.REC005.tripleV a b c) =
    4 *
        ((1 - AKLT.Defs.dot b c - (1 - AKLT.Defs.dot a c)) ^ 2 + (1 - AKLT.Defs.dot b c - (1 - AKLT.Defs.dot a b)) ^ 2 +
          (1 - AKLT.Defs.dot a c - (1 - AKLT.Defs.dot a b)) ^ 2) +
      6 * (1 - AKLT.Defs.dot b c) * (1 - AKLT.Defs.dot a c) * (1 - AKLT.Defs.dot a b)
'AKLT.W.REC005.unit_triple_sos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.triple_denominator_lower (a b c : AKLT.Defs.Vec3) (ha : AKLT.Defs.normSq a = 1)
  (hb : AKLT.Defs.normSq b = 1) (hc : AKLT.Defs.normSq c = 1) :
  1 / 2 ≤ AKLT.Defs.moment (AKLT.W.REC005.tripleWeight a b c)
'AKLT.W.REC005.triple_denominator_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.unit_triple_bound (a b c : AKLT.Defs.Vec3) (ha : AKLT.Defs.normSq a = 1) (hb : AKLT.Defs.normSq b = 1)
  (hc : AKLT.Defs.normSq c = 1) :
  0 ≤ AKLT.Defs.moment (AKLT.W.REC005.tripleWeight a b c) ∧
    (AKLT.Defs.normSq fun i => AKLT.Defs.moment fun v => v i * AKLT.W.REC005.tripleWeight a b c v) ≤
      (3 / 5) ^ 2 * AKLT.Defs.moment (AKLT.W.REC005.tripleWeight a b c) ^ 2
'AKLT.W.REC005.unit_triple_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.dot_ball_bounds (a b : AKLT.Defs.Vec3) (ha : AKLT.Defs.normSq a ≤ 1) (hb : AKLT.Defs.normSq b ≤ 1) :
  -1 ≤ AKLT.Defs.dot a b ∧ AKLT.Defs.dot a b ≤ 1
'AKLT.W.REC005.dot_ball_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.zero_triple_bound (a b : AKLT.Defs.Vec3) (ha : AKLT.Defs.normSq a ≤ 1) (hb : AKLT.Defs.normSq b ≤ 1) :
  0 ≤ AKLT.Defs.moment (AKLT.W.REC005.tripleWeight a b 0) ∧
    (AKLT.Defs.normSq fun i => AKLT.Defs.moment fun v => v i * AKLT.W.REC005.tripleWeight a b 0 v) ≤
      (3 / 5) ^ 2 * AKLT.Defs.moment (AKLT.W.REC005.tripleWeight a b 0) ^ 2
'AKLT.W.REC005.zero_triple_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.spin_norm_le (j : AKLT.Defs.SpinLetter) : AKLT.Defs.normSq (AKLT.Defs.spinVector j) ≤ 1
'AKLT.W.REC005.spin_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.letter_triple_bound (a b c : AKLT.Defs.SpinLetter) :
  0 ≤
      AKLT.Defs.moment
        (AKLT.W.REC005.tripleWeight (AKLT.Defs.spinVector a) (AKLT.Defs.spinVector b) (AKLT.Defs.spinVector c)) ∧
    (AKLT.Defs.normSq fun i =>
        AKLT.Defs.moment fun v =>
          v i *
            AKLT.W.REC005.tripleWeight (AKLT.Defs.spinVector a) (AKLT.Defs.spinVector b) (AKLT.Defs.spinVector c) v) ≤
      (3 / 5) ^ 2 *
        AKLT.Defs.moment
            (AKLT.W.REC005.tripleWeight (AKLT.Defs.spinVector a) (AKLT.Defs.spinVector b) (AKLT.Defs.spinVector c)) ^
          2
'AKLT.W.REC005.letter_triple_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.site_U (f : AKLT.Defs.Vec3 → ℝ) : AKLT.Defs.siteFunctional AKLT.Defs.Status.U f = AKLT.Defs.moment f
'AKLT.W.REC005.site_U' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.site_D (f : AKLT.Defs.Vec3 → ℝ) :
  AKLT.Defs.siteFunctional AKLT.Defs.Status.D f = 3 / 5 * AKLT.Defs.moment f + 2 / 5 * f 0
'AKLT.W.REC005.site_D' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.site_letter_triple_bound (s : AKLT.Defs.Status) (a b c : AKLT.Defs.SpinLetter) :
  0 ≤
      AKLT.Defs.siteFunctional s
        (AKLT.W.REC005.tripleWeight (AKLT.Defs.spinVector a) (AKLT.Defs.spinVector b) (AKLT.Defs.spinVector c)) ∧
    (AKLT.Defs.normSq fun i =>
        AKLT.Defs.siteFunctional s fun v =>
          v i *
            AKLT.W.REC005.tripleWeight (AKLT.Defs.spinVector a) (AKLT.Defs.spinVector b) (AKLT.Defs.spinVector c) v) ≤
      (3 / 5) ^ 2 *
        AKLT.Defs.siteFunctional s
            (AKLT.W.REC005.tripleWeight (AKLT.Defs.spinVector a) (AKLT.Defs.spinVector b) (AKLT.Defs.spinVector c)) ^
          2
'AKLT.W.REC005.site_letter_triple_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.letterProduct (l : List AKLT.Defs.SpinLetter) (v : AKLT.Defs.Vec3) : ℝ
'AKLT.W.REC005.letterProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.local_bound (s : AKLT.Defs.Status) (l : List AKLT.Defs.SpinLetter) (hl : l.length ≤ 3) :
  0 ≤ AKLT.Defs.siteFunctional s (AKLT.W.REC005.letterProduct l) ∧
    (AKLT.Defs.normSq fun i => AKLT.Defs.siteFunctional s fun v => v i * AKLT.W.REC005.letterProduct l v) ≤
      (3 / 5) ^ 2 * AKLT.Defs.siteFunctional s (AKLT.W.REC005.letterProduct l) ^ 2
'AKLT.W.REC005.local_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.localWeight (s : AKLT.Defs.Status) (l : List AKLT.Defs.SpinLetter) (j : AKLT.Defs.SpinLetter) : ℝ
'AKLT.W.REC005.localWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.localMass (s : AKLT.Defs.Status) (l : List AKLT.Defs.SpinLetter) : ℝ
'AKLT.W.REC005.localMass' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.localNumerator (s : AKLT.Defs.Status) (l : List AKLT.Defs.SpinLetter) : AKLT.Defs.Vec3
'AKLT.W.REC005.localNumerator' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.local_mass_bound (s : AKLT.Defs.Status) (l : List AKLT.Defs.SpinLetter) (hl : l.length ≤ 3) :
  0 ≤ AKLT.W.REC005.localMass s l ∧
    AKLT.Defs.normSq (AKLT.W.REC005.localNumerator s l) ≤ 9 / 25 * AKLT.W.REC005.localMass s l ^ 2
'AKLT.W.REC005.local_mass_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.local_pair_bound (s t : AKLT.Defs.Status) (l r : List AKLT.Defs.SpinLetter) (hl : l.length ≤ 3)
  (hr : r.length ≤ 3) :
  -(9 / 25) * AKLT.W.REC005.localMass s l * AKLT.W.REC005.localMass t r ≤
      AKLT.Defs.dot (AKLT.W.REC005.localNumerator s l) (AKLT.W.REC005.localNumerator t r) ∧
    AKLT.Defs.dot (AKLT.W.REC005.localNumerator s l) (AKLT.W.REC005.localNumerator t r) ≤
      9 / 25 * AKLT.W.REC005.localMass s l * AKLT.W.REC005.localMass t r
'AKLT.W.REC005.local_pair_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.sum_pair_mass (C : ℝ) (u v : AKLT.Defs.SpinLetter → ℝ) :
  ∑ a, ∑ b, C * u a * v b = (C * ∑ a, u a) * ∑ b, v b
'AKLT.W.REC005.sum_pair_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.sum_pair_dot (C : ℝ) (u v : AKLT.Defs.SpinLetter → ℝ) :
  ∑ a, ∑ b, C * u a * v b * AKLT.Defs.dot (AKLT.Defs.spinVector a) (AKLT.Defs.spinVector b) =
    C * AKLT.Defs.dot (fun i => ∑ a, u a * AKLT.Defs.spinVector a i) fun i => ∑ b, v b * AKLT.Defs.spinVector b i
'AKLT.W.REC005.sum_pair_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.fibre_bound (C : ℝ) (hC : 0 ≤ C) (s t : AKLT.Defs.Status) (l r : List AKLT.Defs.SpinLetter)
  (hl : l.length ≤ 3) (hr : r.length ≤ 3) :
  have A := ∑ a, ∑ b, C * AKLT.W.REC005.localWeight s l a * AKLT.W.REC005.localWeight t r b;
  have B :=
    ∑ a,
      ∑ b,
        C * AKLT.W.REC005.localWeight s l a * AKLT.W.REC005.localWeight t r b *
          AKLT.Defs.dot (AKLT.Defs.spinVector a) (AKLT.Defs.spinVector b);
  0 ≤ A ∧ -(9 / 25) * A ≤ B ∧ B ≤ 9 / 25 * A
'AKLT.W.REC005.fibre_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.exchangeCoordinate.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [DecidableEq ι] (x : ι) :
  (ι → α) × α ≃ (ι → α) × α
'AKLT.W.REC005.exchangeCoordinate' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.sum_updates.{u_1, u_2} {ι : Type u_1} {α : Type u_2} [Fintype ι] [Fintype α] [DecidableEq ι] (x : ι)
  (f : (ι → α) → ℝ) : ∑ σ, ∑ a, f (Function.update σ x a) = ↑(Fintype.card α) * ∑ σ, f σ
'AKLT.W.REC005.sum_updates' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.updatePair.{u_1} {ι : Type u_1} [DecidableEq ι] (x y : ι) (σ : ι → AKLT.Defs.SpinLetter)
  (a b : AKLT.Defs.SpinLetter) : ι → AKLT.Defs.SpinLetter
'AKLT.W.REC005.updatePair' does not depend on any axioms
AKLT.W.REC005.sum_pair_updates.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι] (x y : ι)
  (f : (ι → AKLT.Defs.SpinLetter) → ℝ) : ∑ σ, ∑ a, ∑ b, f (AKLT.W.REC005.updatePair x y σ a b) = 169 * ∑ σ, f σ
'AKLT.W.REC005.sum_pair_updates' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.pair_bound_of_fibres.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι] (w : (ι → AKLT.Defs.SpinLetter) → ℝ)
  (x y : ι) (hxy : x ≠ y) (s t : AKLT.Defs.Status)
  (hF :
    ∀ (σ : ι → AKLT.Defs.SpinLetter),
      ∃ C l r,
        0 ≤ C ∧
          l.length ≤ 3 ∧
            r.length ≤ 3 ∧
              ∀ (a b : AKLT.Defs.SpinLetter),
                w (AKLT.W.REC005.updatePair x y σ a b) =
                  C * AKLT.W.REC005.localWeight s l a * AKLT.W.REC005.localWeight t r b) :
  -(9 / 25) ≤ (∑ σ, w σ * AKLT.Defs.dot (AKLT.Defs.spinVector (σ x)) (AKLT.Defs.spinVector (σ y))) / ∑ σ, w σ ∧
    (∑ σ, w σ * AKLT.Defs.dot (AKLT.Defs.spinVector (σ x)) (AKLT.Defs.spinVector (σ y))) / ∑ σ, w σ ≤ 9 / 25
'AKLT.W.REC005.pair_bound_of_fibres' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.spinWeight_nonneg (s : AKLT.Defs.Status) (j : AKLT.Defs.SpinLetter) : 0 ≤ AKLT.Defs.spinWeight s j
'AKLT.W.REC005.spinWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.spin_factor_nonneg (a b : AKLT.Defs.SpinLetter) :
  0 ≤ 1 + AKLT.Defs.dot (AKLT.Defs.spinVector a) (AKLT.Defs.spinVector b)
'AKLT.W.REC005.spin_factor_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.incident.{u_1, u_2} {ι : Type u_1} {κ : Type u_2} [Fintype κ] [DecidableEq ι] (L R : κ → ι) (x : ι) :
  Finset κ
'AKLT.W.REC005.incident' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.otherEnd.{u_1, u_2} {ι : Type u_1} {κ : Type u_2} [DecidableEq ι] (L R : κ → ι) (x : ι) (e : κ) : ι
'AKLT.W.REC005.otherEnd' does not depend on any axioms
AKLT.W.REC005.graphWeight.{u_1, u_2} {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] (s : ι → AKLT.Defs.Status)
  (L R : κ → ι) (outside : (ι → AKLT.Defs.SpinLetter) → ℝ) (σ : ι → AKLT.Defs.SpinLetter) : ℝ
'AKLT.W.REC005.graphWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.graphFields.{u_1, u_2} {ι : Type u_1} {κ : Type u_2} [Fintype κ] [DecidableEq ι] (L R : κ → ι) (x : ι)
  (σ : ι → AKLT.Defs.SpinLetter) : List AKLT.Defs.SpinLetter
'AKLT.W.REC005.graphFields' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.graphFields_length.{u_1, u_2} {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι]
  [DecidableEq κ] (L R : κ → ι) (x : ι) (σ : ι → AKLT.Defs.SpinLetter) :
  (AKLT.W.REC005.graphFields L R x σ).length = (AKLT.W.REC005.incident L R x).card
'AKLT.W.REC005.graphFields_length' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.graphFields_product.{u_1, u_2} {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι]
  [DecidableEq κ] (L R : κ → ι) (x : ι) (σ : ι → AKLT.Defs.SpinLetter) (v : AKLT.Defs.Vec3) :
  AKLT.W.REC005.letterProduct (AKLT.W.REC005.graphFields L R x σ) v =
    ∏ e ∈ AKLT.W.REC005.incident L R x,
      (1 + AKLT.Defs.dot v (AKLT.Defs.spinVector (σ (AKLT.W.REC005.otherEnd L R x e))))
'AKLT.W.REC005.graphFields_product' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.graph_site_factorization.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι] (s : ι → AKLT.Defs.Status)
  (x y : ι) (hxy : x ≠ y) (σ : ι → AKLT.Defs.SpinLetter) (a b : AKLT.Defs.SpinLetter) :
  ∏ i, AKLT.Defs.spinWeight (s i) (AKLT.W.REC005.updatePair x y σ a b i) =
    (∏ i, if i = x ∨ i = y then 1 else AKLT.Defs.spinWeight (s i) (σ i)) * AKLT.Defs.spinWeight (s x) a *
      AKLT.Defs.spinWeight (s y) b
'AKLT.W.REC005.graph_site_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.graph_edge_factorization.{u_1, u_2} {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι]
  [DecidableEq κ] (L R : κ → ι) (x y : ι) (hxy : x ≠ y) (hloop : ∀ (e : κ), L e ≠ R e)
  (hcross : ∀ (e : κ), ¬(L e = x ∧ R e = y) ∧ ¬(L e = y ∧ R e = x)) (σ : ι → AKLT.Defs.SpinLetter)
  (a b : AKLT.Defs.SpinLetter) :
  ∏ e,
      (1 +
        AKLT.Defs.dot (AKLT.Defs.spinVector (AKLT.W.REC005.updatePair x y σ a b (L e)))
          (AKLT.Defs.spinVector (AKLT.W.REC005.updatePair x y σ a b (R e)))) =
    (∏ e,
          if e ∈ AKLT.W.REC005.incident L R x ∨ e ∈ AKLT.W.REC005.incident L R y then 1
          else 1 + AKLT.Defs.dot (AKLT.Defs.spinVector (σ (L e))) (AKLT.Defs.spinVector (σ (R e)))) *
        AKLT.W.REC005.letterProduct (AKLT.W.REC005.graphFields L R x σ) (AKLT.Defs.spinVector a) *
      AKLT.W.REC005.letterProduct (AKLT.W.REC005.graphFields L R y σ) (AKLT.Defs.spinVector b)
'AKLT.W.REC005.graph_edge_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.graph_fibre_reduction.{u_1, u_2} {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι]
  [DecidableEq κ] (s : ι → AKLT.Defs.Status) (L R : κ → ι) (outside : (ι → AKLT.Defs.SpinLetter) → ℝ)
  (hout : ∀ (σ : ι → AKLT.Defs.SpinLetter), 0 ≤ outside σ) (x y : ι) (hxy : x ≠ y) (hloop : ∀ (e : κ), L e ≠ R e)
  (hcross : ∀ (e : κ), ¬(L e = x ∧ R e = y) ∧ ¬(L e = y ∧ R e = x)) (hdegx : (AKLT.W.REC005.incident L R x).card ≤ 3)
  (hdegy : (AKLT.W.REC005.incident L R y).card ≤ 3)
  (hfixed :
    ∀ (σ : ι → AKLT.Defs.SpinLetter) (a b : AKLT.Defs.SpinLetter),
      outside (AKLT.W.REC005.updatePair x y σ a b) = outside σ)
  (σ : ι → AKLT.Defs.SpinLetter) :
  ∃ C l r,
    0 ≤ C ∧
      l.length ≤ 3 ∧
        r.length ≤ 3 ∧
          ∀ (a b : AKLT.Defs.SpinLetter),
            AKLT.W.REC005.graphWeight s L R outside (AKLT.W.REC005.updatePair x y σ a b) =
              C * AKLT.W.REC005.localWeight (s x) l a * AKLT.W.REC005.localWeight (s y) r b
'AKLT.W.REC005.graph_fibre_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.mem_neighbours (x z : AKLT.Defs.Plane) : z ∈ AKLT.Defs.neighbours x ↔ ∃ d, x + d.step = z
'AKLT.W.REC005.mem_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.dist_symm (x y : AKLT.Defs.Plane) : AKLT.Defs.latticeDist x y = AKLT.Defs.latticeDist y x
'AKLT.W.REC005.dist_symm' depends on axioms: [propext, Quot.sound]
AKLT.W.REC005.dist_triangle (x y z : AKLT.Defs.Plane) :
  AKLT.Defs.latticeDist x z ≤ AKLT.Defs.latticeDist x y + AKLT.Defs.latticeDist y z
'AKLT.W.REC005.dist_triangle' depends on axioms: [propext, Quot.sound]
AKLT.W.REC005.neighbour_dist (x z : AKLT.Defs.Plane) (hz : z ∈ AKLT.Defs.neighbours x) : AKLT.Defs.latticeDist x z = 1
'AKLT.W.REC005.neighbour_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.neighbours_nonadjacent (x a b : AKLT.Defs.Plane) (ha : a ∈ AKLT.Defs.neighbours x)
  (hb : b ∈ AKLT.Defs.neighbours x) : ¬AKLT.Defs.Adjacent a b
'AKLT.W.REC005.neighbours_nonadjacent' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.adjacent_mem_neighbours (x z : AKLT.Defs.Plane) (h : AKLT.Defs.Adjacent x z) : z ∈ AKLT.Defs.neighbours x
'AKLT.W.REC005.adjacent_mem_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.neighbour_card (x : AKLT.Defs.Plane) : (AKLT.Defs.neighbours x).card = 4
'AKLT.W.REC005.neighbour_card' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.originalLeg_mem {G : Finset AKLT.Defs.Plane} (e : AKLT.Defs.Plane × AKLT.Defs.Plane) :
  e ∈ AKLT.Defs.originalLegs G ↔ e.1 ∈ G ∧ e.2 ∈ AKLT.Defs.neighbours e.1 ∧ e.2 ∉ G
'AKLT.W.REC005.originalLeg_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.no_neighbour_legs {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y x : AKLT.Defs.Plane)
  (hy : y ∈ D.active) (hprotected : y ∉ AKLT.Defs.protectedSites G) (hx : x ∈ AKLT.Defs.neighbours y)
  (e : AKLT.Defs.Plane × AKLT.Defs.Plane) : e ∈ AKLT.Defs.originalLegs G → e.1 ≠ x
'AKLT.W.REC005.no_neighbour_legs' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.removed_active {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite D y).active = D.active.erase y
'AKLT.W.REC005.removed_active' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.present_mem_active {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) {x z : AKLT.Defs.Plane}
  (h : z ∈ D.presentNeighbours x) : x ∈ D.active ∧ z ∈ D.active ∧ z ∈ AKLT.Defs.neighbours x
'AKLT.W.REC005.present_mem_active' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.bond_present {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (e : ↥D.bonds) :
  D.Present (↑e).1 (↑e).2
'AKLT.W.REC005.bond_present' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.netL {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (e : ↥D.bonds) : ↥D.active
'AKLT.W.REC005.netL' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.netR {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (e : ↥D.bonds) : ↥D.active
'AKLT.W.REC005.netR' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.bond_increases {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (e : ↥D.bonds) :
  (↑e).1.1 + (↑e).1.2 < (↑e).2.1 + (↑e).2.2
'AKLT.W.REC005.bond_increases' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.net_no_loop {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (e : ↥D.bonds) :
  AKLT.W.REC005.netL D e ≠ AKLT.W.REC005.netR D e
'AKLT.W.REC005.net_no_loop' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.other_injective {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (x : ↥D.active) :
  Set.InjOn (fun e => ↑(AKLT.W.REC005.otherEnd (AKLT.W.REC005.netL D) (AKLT.W.REC005.netR D) x e))
    ↑(AKLT.W.REC005.incident (AKLT.W.REC005.netL D) (AKLT.W.REC005.netR D) x)
'AKLT.W.REC005.other_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.other_neighbour {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (x : ↥D.active) (e : ↥D.bonds)
  (he : e ∈ AKLT.W.REC005.incident (AKLT.W.REC005.netL D) (AKLT.W.REC005.netR D) x) :
  ↑(AKLT.W.REC005.otherEnd (AKLT.W.REC005.netL D) (AKLT.W.REC005.netR D) x e) ∈ AKLT.Defs.neighbours ↑x
'AKLT.W.REC005.other_neighbour' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.net_degree_le_three {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (x : ↥D.active)
  (y : AKLT.Defs.Plane) (hy : y ∉ D.active) (hx : ↑x ∈ AKLT.Defs.neighbours y) :
  (AKLT.W.REC005.incident (AKLT.W.REC005.netL D) (AKLT.W.REC005.netR D) x).card ≤ 3
'AKLT.W.REC005.net_degree_le_three' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.netPins {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (pinned : Bool) (σ : ↥D.active → AKLT.Defs.SpinLetter) : ℝ
'AKLT.W.REC005.netPins' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.spins_norm_le {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (σ : ↥D.active → AKLT.Defs.SpinLetter) (x : AKLT.Defs.Plane) : AKLT.Defs.normSq (D.spins σ x) ≤ 1
'AKLT.W.REC005.spins_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.netPins_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (pinned : Bool) (σ : ↥D.active → AKLT.Defs.SpinLetter) : 0 ≤ AKLT.W.REC005.netPins D τ pinned σ
'AKLT.W.REC005.netPins_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.spins_updatePair {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (x y : ↥D.active)
  (σ : ↥D.active → AKLT.Defs.SpinLetter) (a b : AKLT.Defs.SpinLetter) (z : AKLT.Defs.Plane) (hzx : z ≠ ↑x)
  (hzy : z ≠ ↑y) : D.spins (AKLT.W.REC005.updatePair x y σ a b) z = D.spins σ z
'AKLT.W.REC005.spins_updatePair' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.netPins_fixed {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (pinned : Bool) (x y : ↥D.active) (hx : ∀ e ∈ AKLT.Defs.originalLegs G, e.1 ≠ ↑x)
  (hy : ∀ e ∈ AKLT.Defs.originalLegs G, e.1 ≠ ↑y) (σ : ↥D.active → AKLT.Defs.SpinLetter) (a b : AKLT.Defs.SpinLetter) :
  AKLT.W.REC005.netPins D τ pinned (AKLT.W.REC005.updatePair x y σ a b) = AKLT.W.REC005.netPins D τ pinned σ
'AKLT.W.REC005.netPins_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.partition_graph {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (pinned : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ pinned f =
    ∑ σ,
      AKLT.W.REC005.graphWeight (fun x => D.status ↑x) (AKLT.W.REC005.netL D) (AKLT.W.REC005.netR D)
          (AKLT.W.REC005.netPins D τ pinned) σ *
        f (D.spins σ)
'AKLT.W.REC005.partition_graph' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.spins_at {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (σ : ↥D.active → AKLT.Defs.SpinLetter)
  (x : ↥D.active) : D.spins σ ↑x = AKLT.Defs.spinVector (σ x)
'AKLT.W.REC005.spins_at' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.network_pair_bound {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (pinned : Bool) (x y : ↥D.active) (hxy : x ≠ y) (hnonadj : ¬AKLT.Defs.Adjacent ↑x ↑y)
  (hlegx : ∀ e ∈ AKLT.Defs.originalLegs G, e.1 ≠ ↑x) (hlegy : ∀ e ∈ AKLT.Defs.originalLegs G, e.1 ≠ ↑y)
  (hdegx : (AKLT.W.REC005.incident (AKLT.W.REC005.netL D) (AKLT.W.REC005.netR D) x).card ≤ 3)
  (hdegy : (AKLT.W.REC005.incident (AKLT.W.REC005.netL D) (AKLT.W.REC005.netR D) y).card ≤ 3) :
  (-(9 / 25) ≤ D.expectation τ pinned fun n => AKLT.Defs.dot (n ↑x) (n ↑y)) ∧
    (D.expectation τ pinned fun n => AKLT.Defs.dot (n ↑x) (n ↑y)) ≤ 9 / 25
'AKLT.W.REC005.network_pair_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.removed_pair_bound {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (y a b : AKLT.Defs.Plane) (hy : y ∈ D.active) (hp : y ∉ AKLT.Defs.protectedSites G) (ha : a ∈ D.presentNeighbours y)
  (hb : b ∈ D.presentNeighbours y) (hab : a ≠ b) (pinned : Bool) :
  -(9 / 25) ≤ AKLT.Defs.removedPairMean D τ pinned y a b ∧ AKLT.Defs.removedPairMean D τ pinned y a b ≤ 9 / 25
'AKLT.W.REC005.removed_pair_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC005.main : AKLT.Blueprint.Rec.TwoMeanIntervalsStatement
'AKLT.W.REC005.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## ORCH-SUMMARY

- Delivered `AKLT/W/REC005/Main.lean` and nine helper/audit files in the same directory.
- Exact theorem: `AKLT.W.REC005.main : AKLT.Blueprint.Rec.TwoMeanIntervalsStatement`.
- Status: PROVED; no residual hypotheses or unproved dependencies.
- All 122 exported declarations audited; axioms contained in `{propext, Classical.choice, Quot.sound}`.
- Required Lake build and independent exact-type/audit file both pass.
- Active vertices and bonds are reindexed by finite subtypes rather than `Fin n`; all actual factors are retained.
- Free positivity uses the concrete common alphabet sign symmetry; no arbitrary-function covariance is asserted.
- Nonfatal helper style warnings remain; no mathematical limitations or open issues.
- Orchestrator action: import `AKLT.W.REC005.Main` and use `AKLT.W.REC005.main`.
