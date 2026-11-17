STATUS: PROVED

## Files

All Lean files are under `/home/ubuntu/aklt/wt/LW_REC022/AKLT/W/REC022/`:

- `Main.lean`: the requested closed theorem.
- `Spin.lean`: unit support, nonnegative factors, exact U/D local sums, and the logarithmic-mean identity.
- `Geometry.lean`: lattice bond orientation, original-leg protection, and removal identities.
- `Sum.lean`: finite weights and the explicit split of a spin assignment into its departure spin and remaining assignment.
- `Integrate.lean`: split the bond product and sum over the departure spin, retaining every original leg.
- `Trace.lean`: traced neighbours and equality of the two departure-deleted partition functionals.
- `Normalize.lean`: finite-sum linearity, the zero-normalizer case, and positivity of I and J.
- `Factorization.lean`: the exact three-neighbour factorization and logarithmic step quotient.
- `Audit.lean`: an importing exact-type check, all exported declaration types, and axiom checks for all 61 exported theorems.

Evidence in this report directory: `build.log`, `audit.log`, `audit.time`, `declarations.txt`, and `axioms.txt`. The earlier report remains in `report.luna.md`.

## Requested export

```lean
theorem AKLT.W.REC022.main :
    AKLT.Blueprint.Rec.ThreeLogIdentityStatement
```

This theorem has no additional hypotheses or residual statements. `Audit.lean` checks it by assignment to the exact frozen type:

```lean
example : AKLT.Blueprint.Rec.ThreeLogIdentityStatement := AKLT.W.REC022.main
```

An additional closed helper is proved:

```lean
theorem AKLT.W.REC022.three_factorization :
    AKLT.Blueprint.Rec.ThreeFactorizationStatement
```

## Proof

The proof computes the cubic U-site and quadratic D-site sums directly from the twelve icosahedral labels and the zero atom. It explicitly reindexes active assignments into the departure spin and the assignment on the departure-deleted network. The incident bond product becomes the product over the present neighbours; original legs remain unchanged because an admissible departure is outside the protected set. The traced network retains exactly f and g at the departure, so the two local sums are precisely the displayed I and J.

All network summands are nonnegative. The pointwise estimates I >= 1/2 and J >= 4/5 give strictly positive normalized response arguments when the remaining normalizer is positive. If that normalizer is zero, every weighted observable sum is zero, the response arguments both equal one, and the original and traced partition sums both vanish. Lean's total real division and `Real.log_zero` handle that branch explicitly. Thus no global strict-positivity theorem is assumed or required.

For positive arguments, the local logarithmic-mean lemma covers both unequal and equal endpoints. Subtracting the two log quotients and collecting the three pair responses gives the exact frozen conclusion.

This uses a direct reindexing of `Network.partition`, rather than the suggested intermediate `FiniteSpinNetwork` model. Conditioning, degree-four mean estimates, and coefficient bounds are unnecessary for this identity. No other blueprint leaf is used as an unproved lemma. No existing file outside REC022 was edited, and no forbidden proof constructs occur in the delivered sources.

## Exported declarations and their statements

The following is the complete `#check` output for the 68 exported definitions and theorems. A separate copy is in `declarations.txt`.

```text
AKLT.W.REC022.golden_sq : AKLT.Defs.goldenRatio ^ 2 = AKLT.Defs.goldenRatio + 1
AKLT.W.REC022.radius_sq : AKLT.Defs.icoRadius ^ 2 = AKLT.Defs.goldenRatio + 2
AKLT.W.REC022.radius_pos : 0 < AKLT.Defs.icoRadius
AKLT.W.REC022.ico_unit (j : AKLT.Defs.IcoLetter) : AKLT.Defs.normSq (AKLT.Defs.icoVector j) = 1
AKLT.W.REC022.dot_comm (a b : AKLT.Defs.Vec3) : AKLT.Defs.dot a b = AKLT.Defs.dot b a
AKLT.W.REC022.normSq_nonneg (a : AKLT.Defs.Vec3) : 0 ≤ AKLT.Defs.normSq a
AKLT.W.REC022.spin_ball (j : AKLT.Defs.SpinLetter) : AKLT.Defs.normSq (AKLT.Defs.spinVector j) ≤ 1
AKLT.W.REC022.ball_factor (a b : AKLT.Defs.Vec3) (ha : AKLT.Defs.normSq a ≤ 1) (hb : AKLT.Defs.normSq b ≤ 1) :
  0 ≤ 1 + AKLT.Defs.dot a b
AKLT.W.REC022.three_scalar_lower (a b c : AKLT.Defs.Vec3) (ha : AKLT.Defs.normSq a ≤ 1) (hb : AKLT.Defs.normSq b ≤ 1)
  (hc : AKLT.Defs.normSq c ≤ 1) : 1 / 2 ≤ 1 + (AKLT.Defs.dot a b + AKLT.Defs.dot a c + AKLT.Defs.dot b c) / 3
AKLT.W.REC022.two_scalar_lower (a b : AKLT.Defs.Vec3) (ha : AKLT.Defs.normSq a ≤ 1) (hb : AKLT.Defs.normSq b ≤ 1) :
  4 / 5 ≤ 1 + AKLT.Defs.dot a b / 5
AKLT.W.REC022.weight_nonneg (s : AKLT.Defs.Status) (j : AKLT.Defs.SpinLetter) : 0 ≤ AKLT.Defs.spinWeight s j
AKLT.W.REC022.site_U_three (a b c : AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun v =>
      (1 + AKLT.Defs.dot v a) * (1 + AKLT.Defs.dot v b) * (1 + AKLT.Defs.dot v c)) =
    1 + (AKLT.Defs.dot a b + AKLT.Defs.dot a c + AKLT.Defs.dot b c) / 3
AKLT.W.REC022.site_D_two (a b : AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.D fun v => (1 + AKLT.Defs.dot v a) * (1 + AKLT.Defs.dot v b)) =
    1 + AKLT.Defs.dot a b / 5
AKLT.W.REC022.logMean_identity (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
  0 < AKLT.Defs.logarithmicMean x y ∧ Real.log x - Real.log y = (x - y) / AKLT.Defs.logarithmicMean x y
AKLT.W.REC022.adjacent_iff (x z : AKLT.Defs.Plane) :
  AKLT.Defs.Adjacent x z ↔ z = (x.1 + 1, x.2) ∨ z = (x.1 - 1, x.2) ∨ z = (x.1, x.2 + 1) ∨ z = (x.1, x.2 - 1)
AKLT.W.REC022.adjacent_symm {x z : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent x z) : AKLT.Defs.Adjacent z x
AKLT.W.REC022.adjacent_ne {x z : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent x z) : x ≠ z
AKLT.W.REC022.mem_neighbours_iff (x z : AKLT.Defs.Plane) : z ∈ AKLT.Defs.neighbours x ↔ AKLT.Defs.Adjacent x z
AKLT.W.REC022.present_symm {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {x z : AKLT.Defs.Plane}
  (h : D.Present x z) : D.Present z x
AKLT.W.REC022.mem_presentNeighbours {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (x z : AKLT.Defs.Plane) :
  z ∈ D.presentNeighbours x ↔ D.Present x z
AKLT.W.REC022.mem_internalBonds {G : Finset AKLT.Defs.Plane} {x z : AKLT.Defs.Plane} :
  (x, z) ∈ AKLT.Defs.internalBonds G ↔ x ∈ G ∧ z ∈ G ∧ z ∈ AKLT.Defs.positiveNeighbours x
AKLT.W.REC022.internal_ne {G : Finset AKLT.Defs.Plane} {e : AKLT.Defs.Plane × AKLT.Defs.Plane}
  (h : e ∈ AKLT.Defs.internalBonds G) : e.1 ≠ e.2
AKLT.W.REC022.internal_not_reverse {G : Finset AKLT.Defs.Plane} {x z : AKLT.Defs.Plane}
  (h : (x, z) ∈ AKLT.Defs.internalBonds G) : (z, x) ∉ AKLT.Defs.internalBonds G
AKLT.W.REC022.internal_or_reverse {G : Finset AKLT.Defs.Plane} {x z : AKLT.Defs.Plane} (hx : x ∈ G) (hz : z ∈ G)
  (h : AKLT.Defs.Adjacent x z) : (x, z) ∈ AKLT.Defs.internalBonds G ∨ (z, x) ∈ AKLT.Defs.internalBonds G
AKLT.W.REC022.leg_protected {G : Finset AKLT.Defs.Plane} {e : AKLT.Defs.Plane × AKLT.Defs.Plane}
  (h : e ∈ AKLT.Defs.originalLegs G) : e.1 ∈ AKLT.Defs.protectedSites G
AKLT.W.REC022.active_remove {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite D y).active = D.active.erase y
AKLT.W.REC022.present_remove {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y x z : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite D y).Present x z ↔ D.Present x z ∧ x ≠ y ∧ z ≠ y
AKLT.W.REC022.mem_active_remove {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y x : AKLT.Defs.Plane) :
  x ∈ (AKLT.Defs.removeSite D y).active ↔ x ≠ y ∧ x ∈ D.active
AKLT.W.REC022.bonds_remove {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite D y).bonds = {e ∈ D.bonds | e.1 ≠ y ∧ e.2 ≠ y}
AKLT.W.REC022.netWeight {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (σ : ↥D.active → AKLT.Defs.SpinLetter) : ℝ
AKLT.W.REC022.partition_sum {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ b f = ∑ σ, AKLT.W.REC022.netWeight D τ b σ * f (D.spins σ)
AKLT.W.REC022.spins_ball {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (σ : ↥D.active → AKLT.Defs.SpinLetter)
  (x : AKLT.Defs.Plane) : AKLT.Defs.normSq (D.spins σ x) ≤ 1
AKLT.W.REC022.netWeight_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (σ : ↥D.active → AKLT.Defs.SpinLetter) : 0 ≤ AKLT.W.REC022.netWeight D τ b σ
AKLT.W.REC022.siteIndexEquiv {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) : ↥D.active ≃ Option ↥(AKLT.Defs.removeSite D y).active
AKLT.W.REC022.joinSpin {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane) (hy : y ∈ D.active)
  (p : AKLT.Defs.SpinLetter × (↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter)) :
  ↥D.active → AKLT.Defs.SpinLetter
AKLT.W.REC022.splitSpin {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) :
  (↥D.active → AKLT.Defs.SpinLetter) ≃
    AKLT.Defs.SpinLetter × (↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter)
AKLT.W.REC022.splitSpin_symm {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) (p : AKLT.Defs.SpinLetter × (↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter)) :
  (AKLT.W.REC022.splitSpin D y hy).symm p = AKLT.W.REC022.joinSpin D y hy p
AKLT.W.REC022.join_spins {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) (p : AKLT.Defs.SpinLetter × (↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter))
  (x : AKLT.Defs.Plane) :
  D.spins (AKLT.W.REC022.joinSpin D y hy p) x =
    if x = y then AKLT.Defs.spinVector p.1 else (AKLT.Defs.removeSite D y).spins p.2 x
AKLT.W.REC022.join_weights {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (hy : y ∈ D.active) (p : AKLT.Defs.SpinLetter × (↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter)) :
  ∏ x, AKLT.Defs.spinWeight (D.status ↑x) (AKLT.W.REC022.joinSpin D y hy p x) =
    AKLT.Defs.spinWeight (D.status y) p.1 * ∏ x, AKLT.Defs.spinWeight ((AKLT.Defs.removeSite D y).status ↑x) (p.2 x)
AKLT.W.REC022.otherEnd (y : AKLT.Defs.Plane) (e : AKLT.Defs.Plane × AKLT.Defs.Plane) : AKLT.Defs.Plane
AKLT.W.REC022.otherEnd_inj {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (e e' : AKLT.Defs.Plane × AKLT.Defs.Plane) (he : e ∈ D.bonds) (he' : e' ∈ D.bonds) (hi : e.1 = y ∨ e.2 = y)
  (hi' : e'.1 = y ∨ e'.2 = y) (hh : AKLT.W.REC022.otherEnd y e = AKLT.W.REC022.otherEnd y e') : e = e'
AKLT.W.REC022.incident_product {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (q n : AKLT.Defs.Plane → AKLT.Defs.Vec3) (hqn : ∀ (x : AKLT.Defs.Plane), x ≠ y → q x = n x) :
  ∏ e ∈ D.bonds with ¬(e.1 ≠ y ∧ e.2 ≠ y), (1 + AKLT.Defs.dot (q e.1) (q e.2)) =
    ∏ z ∈ D.presentNeighbours y, (1 + AKLT.Defs.dot (q y) (n z))
AKLT.W.REC022.bond_product_split {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (q n : AKLT.Defs.Plane → AKLT.Defs.Vec3) (hqn : ∀ (x : AKLT.Defs.Plane), x ≠ y → q x = n x) :
  ∏ e ∈ D.bonds, (1 + AKLT.Defs.dot (q e.1) (q e.2)) =
    (∏ e ∈ (AKLT.Defs.removeSite D y).bonds, (1 + AKLT.Defs.dot (n e.1) (n e.2))) *
      ∏ z ∈ D.presentNeighbours y, (1 + AKLT.Defs.dot (q y) (n z))
AKLT.W.REC022.join_pins {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y : AKLT.Defs.Plane) (hy : y ∈ D.active) (hno : ∀ e ∈ AKLT.Defs.originalLegs G, e.1 ≠ y)
  (p : AKLT.Defs.SpinLetter × (↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter)) :
  (∏ e,
      if b = true ∧ (↑e).1 ∈ D.active then 1 + AKLT.Defs.dot (↑(τ e)) (D.spins (AKLT.W.REC022.joinSpin D y hy p) (↑e).1)
      else 1) =
    ∏ e,
      if b = true ∧ (↑e).1 ∈ (AKLT.Defs.removeSite D y).active then
        1 + AKLT.Defs.dot (↑(τ e)) ((AKLT.Defs.removeSite D y).spins p.2 (↑e).1)
      else 1
AKLT.W.REC022.join_netWeight {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y : AKLT.Defs.Plane) (hy : y ∈ D.active) (hno : ∀ e ∈ AKLT.Defs.originalLegs G, e.1 ≠ y)
  (p : AKLT.Defs.SpinLetter × (↥(AKLT.Defs.removeSite D y).active → AKLT.Defs.SpinLetter)) :
  AKLT.W.REC022.netWeight D τ b (AKLT.W.REC022.joinSpin D y hy p) =
    AKLT.W.REC022.netWeight (AKLT.Defs.removeSite D y) τ b p.2 * AKLT.Defs.spinWeight (D.status y) p.1 *
      ∏ z ∈ D.presentNeighbours y,
        (1 + AKLT.Defs.dot (AKLT.Defs.spinVector p.1) ((AKLT.Defs.removeSite D y).spins p.2 z))
AKLT.W.REC022.integrate_site {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y : AKLT.Defs.Plane) (hy : y ∈ D.active) (hno : ∀ e ∈ AKLT.Defs.originalLegs G, e.1 ≠ y) :
  (D.partition τ b fun x => 1) =
    (AKLT.Defs.removeSite D y).partition τ b fun n =>
      AKLT.Defs.siteFunctional (D.status y) fun v => ∏ z ∈ D.presentNeighbours y, (1 + AKLT.Defs.dot v (n z))
AKLT.W.REC022.active_trace {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hU : D.status y = AKLT.Defs.Status.U) : (AKLT.Defs.traceStep D y o).active = D.active
AKLT.W.REC022.trace_neighbours {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hU : D.status y = AKLT.Defs.Status.U) (hyo : y ≠ o) :
  (AKLT.Defs.traceStep D y o).presentNeighbours y = (D.presentNeighbours y).erase o
AKLT.W.REC022.remove_trace_status {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite (AKLT.Defs.traceStep D y o) y).status = (AKLT.Defs.removeSite D y).status
AKLT.W.REC022.remove_trace_bonds {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite (AKLT.Defs.traceStep D y o) y).bonds = (AKLT.Defs.removeSite D y).bonds
AKLT.W.REC022.partition_congr {G : Finset AKLT.Defs.Plane} (D E : AKLT.Defs.Network G) (hs : D.status = E.status)
  (hb : D.bonds = E.bonds) (τ : AKLT.Defs.PinAssignment G) (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ b f = E.partition τ b f
AKLT.W.REC022.remove_trace_partition {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (AKLT.Defs.removeSite (AKLT.Defs.traceStep D y o) y).partition τ b f = (AKLT.Defs.removeSite D y).partition τ b f
AKLT.W.REC022.scalarI (n : AKLT.Defs.Plane → AKLT.Defs.Vec3) (o f g : AKLT.Defs.Plane) : ℝ
AKLT.W.REC022.scalarJ (n : AKLT.Defs.Plane → AKLT.Defs.Vec3) (f g : AKLT.Defs.Plane) : ℝ
AKLT.W.REC022.partition_add {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (f g : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (D.partition τ b fun n => f n + g n) = D.partition τ b f + D.partition τ b g
AKLT.W.REC022.partition_div {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) (c : ℝ) :
  (D.partition τ b fun n => f n / c) = D.partition τ b f / c
AKLT.W.REC022.partition_const {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (c : ℝ) : (D.partition τ b fun x => c) = (D.partition τ b fun x => 1) * c
AKLT.W.REC022.partition_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) : 0 ≤ D.partition τ b fun x => 1
AKLT.W.REC022.partition_zero {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (hz : (D.partition τ b fun x => 1) = 0) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ b f = 0
AKLT.W.REC022.partition_lower {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) (c : ℝ)
  (h : ∀ (σ : ↥D.active → AKLT.Defs.SpinLetter), c ≤ f (D.spins σ)) :
  (D.partition τ b fun x => 1) * c ≤ D.partition τ b f
AKLT.W.REC022.scalarI_partition {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y o f g : AKLT.Defs.Plane) :
  ((AKLT.Defs.removeSite D y).partition τ b fun n => AKLT.W.REC022.scalarI n o f g) =
    ((AKLT.Defs.removeSite D y).partition τ b fun x => 1) * AKLT.Defs.responseI D τ b y o f g
AKLT.W.REC022.scalarJ_partition {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y f g : AKLT.Defs.Plane) :
  ((AKLT.Defs.removeSite D y).partition τ b fun n => AKLT.W.REC022.scalarJ n f g) =
    ((AKLT.Defs.removeSite D y).partition τ b fun x => 1) * AKLT.Defs.responseJ D τ b y f g
AKLT.W.REC022.responseI_pos {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y o f g : AKLT.Defs.Plane) : 0 < AKLT.Defs.responseI D τ b y o f g
AKLT.W.REC022.responseJ_pos {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y f g : AKLT.Defs.Plane) : 0 < AKLT.Defs.responseJ D τ b y f g
AKLT.W.REC022.three_integrated (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = AKLT.Defs.Status.U)
  (f g : AKLT.Defs.Plane) (hn : a.D.presentNeighbours a.y = {a.o, f, g}) (hof : a.o ≠ f) (hog : a.o ≠ g) (hfg : f ≠ g)
  (b : Bool) :
  ((a.D.partition a.τ b fun x => 1) =
      (AKLT.Defs.removeSite a.D a.y).partition a.τ b fun n => AKLT.W.REC022.scalarI n a.o f g) ∧
    ((AKLT.Defs.traceStep a.D a.y a.o).partition a.τ b fun x => 1) =
      (AKLT.Defs.removeSite a.D a.y).partition a.τ b fun n => AKLT.W.REC022.scalarJ n f g
AKLT.W.REC022.three_factorization : AKLT.Blueprint.Rec.ThreeFactorizationStatement
AKLT.W.REC022.step_log_ratio (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = AKLT.Defs.Status.U)
  (f g : AKLT.Defs.Plane) (hn : a.D.presentNeighbours a.y = {a.o, f, g}) (hof : a.o ≠ f) (hog : a.o ≠ g) (hfg : f ≠ g)
  (b : Bool) :
  Real.log (AKLT.Defs.stepRatio a.D a.τ b a.y a.o) =
    Real.log (AKLT.Defs.responseJ a.D a.τ b a.y f g / AKLT.Defs.responseI a.D a.τ b a.y a.o f g)
AKLT.W.REC022.main : AKLT.Blueprint.Rec.ThreeLogIdentityStatement
```

## Axioms

The following is the complete `#print axioms` output for all 61 exported theorems. Every dependency is among `propext`, `Classical.choice`, and `Quot.sound`. A separate copy is in `axioms.txt`.

```text
'AKLT.W.REC022.golden_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.radius_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.ico_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.dot_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.normSq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.spin_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.ball_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.three_scalar_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.two_scalar_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.weight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.site_U_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.site_D_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.logMean_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.adjacent_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.adjacent_symm' depends on axioms: [propext, Quot.sound]
'AKLT.W.REC022.adjacent_ne' depends on axioms: [propext]
'AKLT.W.REC022.mem_neighbours_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.present_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.mem_presentNeighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.mem_internalBonds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.internal_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.internal_not_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.internal_or_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.leg_protected' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.active_remove' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.present_remove' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.mem_active_remove' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.bonds_remove' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.partition_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.spins_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.netWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.splitSpin_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.join_spins' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.join_weights' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.otherEnd_inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.incident_product' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.bond_product_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.join_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.join_netWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.integrate_site' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.active_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.trace_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.remove_trace_status' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.remove_trace_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.partition_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.remove_trace_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.partition_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.partition_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.partition_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.partition_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.partition_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.partition_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.scalarI_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.scalarJ_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.responseI_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.responseJ_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.three_integrated' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.three_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.step_log_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC022.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Builds and exact-type validation

Run from `/home/ubuntu/aklt/wt/LW_REC022` with `PATH="$HOME/.elan/bin:$PATH"`:

- `lake build AKLT.W.REC022.Main` — PASS, final wall time 56.46 seconds; Main itself compiled in 7.0 seconds. Final build completed without warnings. Existing project dependencies were reused.
- `lake env lean AKLT/W/REC022/Audit.lean` — PASS, wall time 4.61 seconds. This independently imports Main, checks the exact requested type, and audits every new exported theorem.
- Source scan for forbidden proof constructs — PASS.

## Open issues

None. The previous three residuals and conditional `main_of_residuals` have been replaced by local proofs and the requested closed `main` theorem. Global strict positivity and response coefficient estimates are outside the requested leaf and are not prerequisites of this proof.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC022.main : AKLT.Blueprint.Rec.ThreeLogIdentityStatement` in `AKLT/W/REC022/Main.lean`.
- Also proved `AKLT.W.REC022.three_factorization` and the finite-spin, normalization, and logarithmic helpers it uses.
- No residual propositions or unproved dependencies remain.
- Direct finite-assignment reindexing replaces the suggested finite-network-model detour.
- Zero normalizers are handled explicitly; global strict positivity is not needed or asserted.
- Final Main build and importing exact-type/axiom audit pass.
- All 61 exported theorems use only the allowed axioms.
- No frozen statements or files outside the assigned directory were edited.
- Open names: none. Orchestrator may accept REC022 as proved.
