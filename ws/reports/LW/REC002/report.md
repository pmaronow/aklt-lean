STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC002/AKLT/W/REC002/Main.lean): Exact requested theorem and the final normalized factorization.
- [Moments.lean](/home/ubuntu/aklt/wt/LW_REC002/AKLT/W/REC002/Moments.lean): Coordinate moments, support norm bound, and the explicit U/D site integrals.
- [Sums.lean](/home/ubuntu/aklt/wt/LW_REC002/AKLT/W/REC002/Sums.lean): Active-spin configurations, the one-site bijection, and finite product-sum reindexing.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_REC002/AKLT/W/REC002/Geometry.lean): Oriented bond indexing, site deletion, and absence of original legs at an admissible start.
- [Bonds.lean](/home/ubuntu/aklt/wt/LW_REC002/AKLT/W/REC002/Bonds.lean): Incident bond product and unchanged original-leg product after deleting the departure.
- [Integration.lean](/home/ubuntu/aklt/wt/LW_REC002/AKLT/W/REC002/Integration.lean): General one-site partition integration, nonnegative weights, zero-mass cancellation, and linearity.
- [Trace.lean](/home/ubuntu/aklt/wt/LW_REC002/AKLT/W/REC002/Trace.lean): The two retained neighbours and equality of the two departure-deleted partition functionals.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC002/AKLT/W/REC002/Audit.lean): Exact-type example, declaration statements, and axiom checks for all 80 named declarations.

The earlier report remains preserved as `report.luna.md`. No existing source outside `AKLT/W/REC002/` was changed.

## Exported result

```lean
theorem AKLT.W.REC002.main :
    AKLT.Blueprint.Rec.ThreeFactorizationStatement
```

This is the exact closed statement in `AKLT.Blueprint.Rec.NodesResponse`, with both equalities and no additional hypotheses. There are no residual statements and no dependencies on unproved blueprint leaves. All 72 named theorems and 8 transparent helper definitions have their full checked types and axiom output in the appendix below, also preserved in [audit.log](/home/ubuntu/aklt/reports/LW/REC002/audit.log).

## Proof

The active-spin configuration space splits by an explicit equivalence into the departure letter and the configuration on the departure-deleted active sites. Reindexing the finite sum and product gives `partition_integrate`. The bond product splits into the deleted-network bond product and one factor per present neighbour. The original-leg product is unchanged: an admissible start lies outside the protected layer, and an original leg would put it at distance one from the exterior.

The explicit icosahedral coordinates give the vanishing first and third moments and the second tensor `δᵢⱼ/3`. They yield the U-site integral

```text
1 + (dot(n_f,n_g) + dot(n_f,n_o) + dot(n_g,n_o))/3.
```

The D law is the `3/5` U-law mixture with a `2/5` zero atom. Its two-factor integral is `1 + dot(n_f,n_g)/5`. Tracing deletes precisely the selected outgoing bond. Deleting the departure after tracing has the same status function and bonds as deleting it before tracing, so the remaining partition functional is exactly the same.

Finite-sum linearity then gives both normalized identities. The proof does not need a strict-positivity leaf: every configuration weight is nonnegative, so if the deleted partition mass is zero, every summand and every unnormalized observable partition is zero. Thus `Z * expectation(f) = partition(f)` holds also at `Z = 0`. This directly handles Lean's total division convention.

## Verification

Required build (successful, exit 0):

```sh
PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC002.Main
```

Final timed run: **29.45 seconds**, with the moment module already built. It rebuilt `Sums`, `Bonds`, `Integration`, `Trace`, and `Main` without warnings. The moment module had compiled in approximately 26 seconds; the final geometry module compiled in approximately 9 seconds in the preceding run.

Exact-type and complete axiom audit (successful, exit 0):

```sh
PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/REC002/Audit.lean
```

Audit time: **12.18 seconds**. `Audit.lean` contains the independent exact-type check

```lean
example : AKLT.Blueprint.Rec.ThreeFactorizationStatement := AKLT.W.REC002.main
```

and `#check` / `#print axioms` for all 80 named declarations. In particular:

```text
AKLT.W.REC002.main : AKLT.Blueprint.Rec.ThreeFactorizationStatement
'AKLT.W.REC002.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All audited axiom sets are subsets of the three permitted axioms. A source scan found no forbidden proof placeholders, declarations, computation shortcuts, or options. No sub-agents were used.

## Open issues

None. The earlier `Residual_PreStep` / `Residual_PostStep` reduction has been replaced by the unconditional requested theorem. The only route deviation is direct active-site finite-sum reindexing and zero-normalizer handling, which avoids a separate common finite-network positivity proof.

## Checked exported declarations and axiom output

```text
AKLT.W.REC002.golden_sq : AKLT.Defs.goldenRatio ^ 2 = AKLT.Defs.goldenRatio + 1
'AKLT.W.REC002.golden_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.golden_pos : 0 < AKLT.Defs.goldenRatio
'AKLT.W.REC002.golden_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.radius_sq : AKLT.Defs.icoRadius ^ 2 = AKLT.Defs.goldenRatio + 2
'AKLT.W.REC002.radius_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.radius_ne : AKLT.Defs.icoRadius ≠ 0
'AKLT.W.REC002.radius_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.moment_coordinate (i : Fin 3) : (AKLT.Defs.moment fun v => v i) = 0
'AKLT.W.REC002.moment_coordinate' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.moment_pair_diag (i : Fin 3) : (AKLT.Defs.moment fun v => v i ^ 2) = 1 / 3
'AKLT.W.REC002.moment_pair_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.moment_coord_pair (i j : Fin 3) : (AKLT.Defs.moment fun v => v i * v j) = if i = j then 1 / 3 else 0
'AKLT.W.REC002.moment_coord_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.moment_coord_triple (i j k : Fin 3) : (AKLT.Defs.moment fun v => v i * v j * v k) = 0
'AKLT.W.REC002.moment_coord_triple' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.ico_unit (j : AKLT.Defs.IcoLetter) : AKLT.Defs.normSq (AKLT.Defs.icoVector j) = 1
'AKLT.W.REC002.ico_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.spin_ball (j : AKLT.Defs.SpinLetter) : AKLT.Defs.normSq (AKLT.Defs.spinVector j) ≤ 1
'AKLT.W.REC002.spin_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.norm_nonneg (a : AKLT.Defs.Vec3) : 0 ≤ AKLT.Defs.normSq a
'AKLT.W.REC002.norm_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.factor_nonneg (a b : AKLT.Defs.Vec3) (ha : AKLT.Defs.normSq a ≤ 1) (hb : AKLT.Defs.normSq b ≤ 1) :
  0 ≤ 1 + AKLT.Defs.dot a b
'AKLT.W.REC002.factor_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.dot_comm (a b : AKLT.Defs.Vec3) : AKLT.Defs.dot a b = AKLT.Defs.dot b a
'AKLT.W.REC002.dot_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.moment_add (f g : AKLT.Defs.Vec3 → ℝ) :
  (AKLT.Defs.moment fun n => f n + g n) = AKLT.Defs.moment f + AKLT.Defs.moment g
'AKLT.W.REC002.moment_add' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.moment_smul (c : ℝ) (f : AKLT.Defs.Vec3 → ℝ) :
  (AKLT.Defs.moment fun n => c * f n) = c * AKLT.Defs.moment f
'AKLT.W.REC002.moment_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.moment_sum.{u_1} {ι : Type u_1} [Fintype ι] (f : ι → AKLT.Defs.Vec3 → ℝ) :
  (AKLT.Defs.moment fun n => ∑ i, f i n) = ∑ i, AKLT.Defs.moment (f i)
'AKLT.W.REC002.moment_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.moment_one : (AKLT.Defs.moment fun x => 1) = 1
'AKLT.W.REC002.moment_one' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.moment_dot (a : AKLT.Defs.Vec3) : (AKLT.Defs.moment fun n => AKLT.Defs.dot n a) = 0
'AKLT.W.REC002.moment_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.moment_dot_pair (a b : AKLT.Defs.Vec3) :
  (AKLT.Defs.moment fun n => AKLT.Defs.dot n a * AKLT.Defs.dot n b) = AKLT.Defs.dot a b / 3
'AKLT.W.REC002.moment_dot_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.moment_dot_triple (a b c : AKLT.Defs.Vec3) :
  (AKLT.Defs.moment fun n => AKLT.Defs.dot n a * AKLT.Defs.dot n b * AKLT.Defs.dot n c) = 0
'AKLT.W.REC002.moment_dot_triple' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.siteU (f : AKLT.Defs.Vec3 → ℝ) : AKLT.Defs.siteFunctional AKLT.Defs.Status.U f = AKLT.Defs.moment f
'AKLT.W.REC002.siteU' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.siteD (f : AKLT.Defs.Vec3 → ℝ) :
  AKLT.Defs.siteFunctional AKLT.Defs.Status.D f = 3 / 5 * AKLT.Defs.moment f + 2 / 5 * f 0
'AKLT.W.REC002.siteD' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.integrate_U3 (a b c : AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun n =>
      (1 + AKLT.Defs.dot n a) * (1 + AKLT.Defs.dot n b) * (1 + AKLT.Defs.dot n c)) =
    1 + (AKLT.Defs.dot a b + AKLT.Defs.dot a c + AKLT.Defs.dot b c) / 3
'AKLT.W.REC002.integrate_U3' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.integrate_D2 (a b : AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.D fun n => (1 + AKLT.Defs.dot n a) * (1 + AKLT.Defs.dot n b)) =
    1 + AKLT.Defs.dot a b / 5
'AKLT.W.REC002.integrate_D2' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.extend (V : Finset AKLT.Defs.Plane) (n : ↥V → AKLT.Defs.SpinLetter) (x : AKLT.Defs.Plane) : AKLT.Defs.Vec3
'AKLT.W.REC002.extend' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.spinSum (V : Finset AKLT.Defs.Plane) (s : AKLT.Defs.Plane → AKLT.Defs.Status)
  (F : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) : ℝ
'AKLT.W.REC002.spinSum' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.insConf (V : Finset AKLT.Defs.Plane) (y : AKLT.Defs.Plane) (j : AKLT.Defs.SpinLetter)
  (n : ↥V → AKLT.Defs.SpinLetter) (x : ↥(insert y V)) : AKLT.Defs.SpinLetter
'AKLT.W.REC002.insConf' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.splitConf (V : Finset AKLT.Defs.Plane) (y : AKLT.Defs.Plane) (hy : y ∉ V) :
  (↥(insert y V) → AKLT.Defs.SpinLetter) ≃ AKLT.Defs.SpinLetter × (↥V → AKLT.Defs.SpinLetter)
'AKLT.W.REC002.splitConf' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.extend_ins (V : Finset AKLT.Defs.Plane) (y : AKLT.Defs.Plane) (_hy : y ∉ V) (j : AKLT.Defs.SpinLetter)
  (n : ↥V → AKLT.Defs.SpinLetter) :
  AKLT.W.REC002.extend (insert y V) (AKLT.W.REC002.insConf V y j n) =
    Function.update (AKLT.W.REC002.extend V n) y (AKLT.Defs.spinVector j)
'AKLT.W.REC002.extend_ins' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.prod_ins (V : Finset AKLT.Defs.Plane) (y : AKLT.Defs.Plane) (hy : y ∉ V)
  (s : AKLT.Defs.Plane → AKLT.Defs.Status) (j : AKLT.Defs.SpinLetter) (n : ↥V → AKLT.Defs.SpinLetter) :
  ∏ x, AKLT.Defs.spinWeight (s ↑x) (AKLT.W.REC002.insConf V y j n x) =
    AKLT.Defs.spinWeight (s y) j * ∏ x, AKLT.Defs.spinWeight (s ↑x) (n x)
'AKLT.W.REC002.prod_ins' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.spinSum_insert (V : Finset AKLT.Defs.Plane) (y : AKLT.Defs.Plane) (hy : y ∉ V)
  (s : AKLT.Defs.Plane → AKLT.Defs.Status) (F : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  AKLT.W.REC002.spinSum (insert y V) s F =
    ∑ n,
      (∏ x, AKLT.Defs.spinWeight (s ↑x) (n x)) *
        AKLT.Defs.siteFunctional (s y) fun v => F (Function.update (AKLT.W.REC002.extend V n) y v)
'AKLT.W.REC002.spinSum_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.bondProduct (B : Finset (AKLT.Defs.Plane × AKLT.Defs.Plane)) (n : AKLT.Defs.Plane → AKLT.Defs.Vec3) : ℝ
'AKLT.W.REC002.bondProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.legProduct {G : Finset AKLT.Defs.Plane} (V : Finset AKLT.Defs.Plane) (τ : AKLT.Defs.PinAssignment G)
  (pinned : Bool) (n : AKLT.Defs.Plane → AKLT.Defs.Vec3) : ℝ
'AKLT.W.REC002.legProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.partition_spinSum {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (pinned : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ pinned f =
    AKLT.W.REC002.spinSum D.active D.status fun n =>
      f n * AKLT.W.REC002.bondProduct D.bonds n * AKLT.W.REC002.legProduct D.active τ pinned n
'AKLT.W.REC002.partition_spinSum' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.adjacent_symm (x y : AKLT.Defs.Plane) : AKLT.Defs.Adjacent x y ↔ AKLT.Defs.Adjacent y x
'AKLT.W.REC002.adjacent_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.adjacent_ne {x y : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent x y) : x ≠ y
'AKLT.W.REC002.adjacent_ne' depends on axioms: [propext]
AKLT.W.REC002.adjacent_iff_positive (x y : AKLT.Defs.Plane) :
  AKLT.Defs.Adjacent x y ↔ y ∈ AKLT.Defs.positiveNeighbours x ∨ x ∈ AKLT.Defs.positiveNeighbours y
'AKLT.W.REC002.adjacent_iff_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.neighbour_iff (x y : AKLT.Defs.Plane) : y ∈ AKLT.Defs.neighbours x ↔ AKLT.Defs.Adjacent x y
'AKLT.W.REC002.neighbour_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.present_symm {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (x y : AKLT.Defs.Plane) :
  D.Present x y ↔ D.Present y x
'AKLT.W.REC002.present_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.present_ne {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {x y : AKLT.Defs.Plane}
  (h : D.Present x y) : x ≠ y
'AKLT.W.REC002.present_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.mem_presentNeighbours {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (x y : AKLT.Defs.Plane) :
  y ∈ D.presentNeighbours x ↔ D.Present x y
'AKLT.W.REC002.mem_presentNeighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.mem_internal (G : Finset AKLT.Defs.Plane) (x y : AKLT.Defs.Plane) :
  (x, y) ∈ AKLT.Defs.internalBonds G ↔ x ∈ G ∧ y ∈ G ∧ y ∈ AKLT.Defs.positiveNeighbours x
'AKLT.W.REC002.mem_internal' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.mem_bonds {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (x y : AKLT.Defs.Plane) :
  (x, y) ∈ D.bonds ↔ D.Present x y ∧ y ∈ AKLT.Defs.positiveNeighbours x
'AKLT.W.REC002.mem_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.remove_active {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite D y).active = D.active.erase y
'AKLT.W.REC002.remove_active' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.mem_remove_active {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y x : AKLT.Defs.Plane) :
  x ∈ (AKLT.Defs.removeSite D y).active ↔ x ∈ D.active ∧ x ≠ y
'AKLT.W.REC002.mem_remove_active' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.remove_bonds {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite D y).bonds = {e ∈ D.bonds | e.1 ≠ y ∧ e.2 ≠ y}
'AKLT.W.REC002.remove_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.no_leg {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {y : AKLT.Defs.Plane}
  (hy : D.AdmissibleStart y) (e : ↥(AKLT.Defs.originalLegs G)) : (↑e).1 ≠ y
'AKLT.W.REC002.no_leg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.positive_asymm {x z : AKLT.Defs.Plane} (h : z ∈ AKLT.Defs.positiveNeighbours x) :
  x ∉ AKLT.Defs.positiveNeighbours z
'AKLT.W.REC002.positive_asymm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.otherEnd (y : AKLT.Defs.Plane) (e : AKLT.Defs.Plane × AKLT.Defs.Plane) : AKLT.Defs.Plane
'AKLT.W.REC002.otherEnd' does not depend on any axioms
AKLT.W.REC002.incident_other {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (e : AKLT.Defs.Plane × AKLT.Defs.Plane) (he : e ∈ {e ∈ D.bonds | e.1 = y ∨ e.2 = y}) :
  AKLT.W.REC002.otherEnd y e ∈ D.presentNeighbours y
'AKLT.W.REC002.incident_other' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.incident_injective {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (a b : AKLT.Defs.Plane × AKLT.Defs.Plane) (ha : a ∈ {e ∈ D.bonds | e.1 = y ∨ e.2 = y})
  (hb : b ∈ {e ∈ D.bonds | e.1 = y ∨ e.2 = y}) (hab : AKLT.W.REC002.otherEnd y a = AKLT.W.REC002.otherEnd y b) : a = b
'AKLT.W.REC002.incident_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.incident_surjective {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y z : AKLT.Defs.Plane)
  (hz : z ∈ D.presentNeighbours y) : ∃ e ∈ {e ∈ D.bonds | e.1 = y ∨ e.2 = y}, AKLT.W.REC002.otherEnd y e = z
'AKLT.W.REC002.incident_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.bondProduct_remove {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (n : AKLT.Defs.Plane → AKLT.Defs.Vec3) (v : AKLT.Defs.Vec3) :
  AKLT.W.REC002.bondProduct D.bonds (Function.update n y v) =
    AKLT.W.REC002.bondProduct (AKLT.Defs.removeSite D y).bonds n *
      ∏ z ∈ D.presentNeighbours y, (1 + AKLT.Defs.dot v (n z))
'AKLT.W.REC002.bondProduct_remove' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.legProduct_remove {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (hleg : ∀ (e : ↥(AKLT.Defs.originalLegs G)), (↑e).1 ≠ y)
  (n : AKLT.Defs.Plane → AKLT.Defs.Vec3) (v : AKLT.Defs.Vec3) :
  AKLT.W.REC002.legProduct D.active τ b (Function.update n y v) =
    AKLT.W.REC002.legProduct (AKLT.Defs.removeSite D y).active τ b n
'AKLT.W.REC002.legProduct_remove' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.spinSum_status (V : Finset AKLT.Defs.Plane) (s t : AKLT.Defs.Plane → AKLT.Defs.Status)
  (hst : ∀ x ∈ V, s x = t x) (F : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  AKLT.W.REC002.spinSum V s F = AKLT.W.REC002.spinSum V t F
'AKLT.W.REC002.spinSum_status' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.site_constants (s : AKLT.Defs.Status) (A B : ℝ) (f : AKLT.Defs.Vec3 → ℝ) :
  (AKLT.Defs.siteFunctional s fun v => A * f v * B) = A * AKLT.Defs.siteFunctional s f * B
'AKLT.W.REC002.site_constants' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.partition_integrate {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) (hleg : ∀ (e : ↥(AKLT.Defs.originalLegs G)), (↑e).1 ≠ y) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) :
  (D.partition τ b fun x => 1) =
    (AKLT.Defs.removeSite D y).partition τ b fun n =>
      AKLT.Defs.siteFunctional (D.status y) fun v => ∏ z ∈ D.presentNeighbours y, (1 + AKLT.Defs.dot v (n z))
'AKLT.W.REC002.partition_integrate' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.configWeight {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (n : ↥D.active → AKLT.Defs.SpinLetter) : ℝ
'AKLT.W.REC002.configWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.partition_weight {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ b f = ∑ n, AKLT.W.REC002.configWeight D τ b n * f (D.spins n)
'AKLT.W.REC002.partition_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.spins_ball {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (n : ↥D.active → AKLT.Defs.SpinLetter)
  (x : AKLT.Defs.Plane) : AKLT.Defs.normSq (D.spins n x) ≤ 1
'AKLT.W.REC002.spins_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.configWeight_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (n : ↥D.active → AKLT.Defs.SpinLetter) : 0 ≤ AKLT.W.REC002.configWeight D τ b n
'AKLT.W.REC002.configWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.partition_zero {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (hzero : (D.partition τ b fun x => 1) = 0) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ b f = 0
'AKLT.W.REC002.partition_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.partition_expectation {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (D.partition τ b fun x => 1) * D.expectation τ b f = D.partition τ b f
'AKLT.W.REC002.partition_expectation' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.partition_add {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (f g : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (D.partition τ b fun n => f n + g n) = D.partition τ b f + D.partition τ b g
'AKLT.W.REC002.partition_add' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.partition_smul {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (c : ℝ) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (D.partition τ b fun n => c * f n) = c * D.partition τ b f
'AKLT.W.REC002.partition_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.trace_active {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hU : D.status y = AKLT.Defs.Status.U) : (AKLT.Defs.traceStep D y o).active = D.active
'AKLT.W.REC002.trace_active' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.trace_present_y {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o z : AKLT.Defs.Plane)
  (hU : D.status y = AKLT.Defs.Status.U) (_hyo : y ≠ o) :
  (AKLT.Defs.traceStep D y o).Present y z ↔ D.Present y z ∧ z ≠ o
'AKLT.W.REC002.trace_present_y' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.trace_neighbours {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hU : D.status y = AKLT.Defs.Status.U) (hyo : y ≠ o) :
  (AKLT.Defs.traceStep D y o).presentNeighbours y = (D.presentNeighbours y).erase o
'AKLT.W.REC002.trace_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.trace_kept_away {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o x z : AKLT.Defs.Plane)
  (hx : x ≠ y) (hz : z ≠ y) : z ∈ (AKLT.Defs.traceStep D y o).kept x ↔ z ∈ D.kept x
'AKLT.W.REC002.trace_kept_away' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.trace_present_away {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o x z : AKLT.Defs.Plane)
  (hU : D.status y = AKLT.Defs.Status.U) (hx : x ≠ y) (hz : z ≠ y) :
  (AKLT.Defs.traceStep D y o).Present x z ↔ D.Present x z
'AKLT.W.REC002.trace_present_away' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.remove_trace_status {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite (AKLT.Defs.traceStep D y o) y).status = (AKLT.Defs.removeSite D y).status
'AKLT.W.REC002.remove_trace_status' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.remove_trace_bonds {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hU : D.status y = AKLT.Defs.Status.U) :
  (AKLT.Defs.removeSite (AKLT.Defs.traceStep D y o) y).bonds = (AKLT.Defs.removeSite D y).bonds
'AKLT.W.REC002.remove_trace_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.partition_congr {G : Finset AKLT.Defs.Plane} (D E : AKLT.Defs.Network G) (hstatus : D.status = E.status)
  (hbonds : D.bonds = E.bonds) (τ : AKLT.Defs.PinAssignment G) (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ b f = E.partition τ b f
'AKLT.W.REC002.partition_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.remove_trace_partition {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hU : D.status y = AKLT.Defs.Status.U) (τ : AKLT.Defs.PinAssignment G) (b : Bool)
  (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (AKLT.Defs.removeSite (AKLT.Defs.traceStep D y o) y).partition τ b f = (AKLT.Defs.removeSite D y).partition τ b f
'AKLT.W.REC002.remove_trace_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.integrate_neighbours_three (o f g : AKLT.Defs.Plane) (hof : o ≠ f) (hog : o ≠ g) (hfg : f ≠ g)
  (n : AKLT.Defs.Plane → AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun v => ∏ z ∈ {o, f, g}, (1 + AKLT.Defs.dot v (n z))) =
    1 + (AKLT.Defs.dot (n f) (n g) + AKLT.Defs.dot (n f) (n o) + AKLT.Defs.dot (n g) (n o)) / 3
'AKLT.W.REC002.integrate_neighbours_three' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.integrate_neighbours_two (f g : AKLT.Defs.Plane) (hfg : f ≠ g) (n : AKLT.Defs.Plane → AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.D fun v => ∏ z ∈ {f, g}, (1 + AKLT.Defs.dot v (n z))) =
    1 + AKLT.Defs.dot (n f) (n g) / 5
'AKLT.W.REC002.integrate_neighbours_two' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.partition_div {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (c : ℝ) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (D.partition τ b fun n => f n / c) = D.partition τ b f / c
'AKLT.W.REC002.partition_div' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.partition_three_expectations {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (o f g : AKLT.Defs.Plane) :
  (D.partition τ b fun n =>
      1 + (AKLT.Defs.dot (n f) (n g) + AKLT.Defs.dot (n f) (n o) + AKLT.Defs.dot (n g) (n o)) / 3) =
    (D.partition τ b fun x => 1) *
      (1 +
        (((D.expectation τ b fun n => AKLT.Defs.dot (n f) (n g)) +
              D.expectation τ b fun n => AKLT.Defs.dot (n f) (n o)) +
            D.expectation τ b fun n => AKLT.Defs.dot (n g) (n o)) /
          3)
'AKLT.W.REC002.partition_three_expectations' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.partition_one_expectation {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (f g : AKLT.Defs.Plane) :
  (D.partition τ b fun n => 1 + AKLT.Defs.dot (n f) (n g) / 5) =
    (D.partition τ b fun x => 1) * (1 + (D.expectation τ b fun n => AKLT.Defs.dot (n f) (n g)) / 5)
'AKLT.W.REC002.partition_one_expectation' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC002.main : AKLT.Blueprint.Rec.ThreeFactorizationStatement
'AKLT.W.REC002.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## ORCH-SUMMARY

- Delivered `AKLT/W/REC002/Main.lean` and seven helper/audit modules in the same directory.
- Exact export: `AKLT.W.REC002.main : AKLT.Blueprint.Rec.ThreeFactorizationStatement`.
- Status: PROVED; both pre-step and post-step identities are unconditional under the frozen statement's hypotheses.
- Open declarations: none; no residual obligations remain.
- No unproved blueprint leaves or additional hypotheses were used.
- Reused and extended the earlier coordinate-moment proofs.
- Direct finite active-spin reindexing replaces the suggested common-network bridge.
- Zero deleted mass is handled by nonnegative-summand cancellation; no strict-positivity premise is needed.
- Main build passed; exact-type example and all 80 axiom checks passed.
- Axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
- No frozen statements or files outside the assigned source directory were modified.
- No limitations or orchestrator decisions remain.
