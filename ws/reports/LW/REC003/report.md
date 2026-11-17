STATUS: PROVED

## Files

All Lean source is under `AKLT/W/REC003/`:

- `Main.lean`: the required closed theorem and the two factorization conjuncts.
- `Moments.lean`: direct finite computations of the U second moment, the D first moment, and unit-length spin vectors.
- `Finite.lean`: the explicit spin-assignment equivalence and finite-sum Fubini identity, including an empty complement.
- `Geometry.lean`: incident-bond decomposition, removal identities, and absence of original legs at an unprotected departure.
- `Weights.lean`: nonnegative partition weights, zero-mass handling, and exact normalization identities.
- `Integration.lean`: integration of one active site with all original pins retained.
- `Trace.lean`: the trace removes only the selected bond, and removal of the departure gives the same remaining partition.
- `Audit.lean`: independent import, exact frozen-type check, and statement/axiom checks for every named declaration.

Report artifacts: `report.md`, `audit.txt`, and `audit-time.txt` in `/home/ubuntu/aklt/reports/LW/REC003/`. The previous `report.luna.md` is preserved.

## Exported declarations

```lean
theorem AKLT.W.REC003.main : AKLT.Blueprint.Rec.TwoFactorizationStatement
```

The theorem has exactly the requested name and closed type. It has no residual assumptions.

`pre_factorization` and `post_factorization` prove the two conjuncts under the target's departure, U-status, two-neighbour, distinctness, and pin-choice premises. The complete elaborated statements of all 71 named declarations (63 proved theorems and 8 definitions) appear in the audit appendix below.

## Proof

Split the active spin assignment into the departure label and the assignment on the erased active set. Split the bonds into the remaining bonds and the distinct incident bonds, respecting the original positive orientation. An admissible departure is outside the original protected layer, so no original leg is incident to it. The explicit icosahedron sum gives `siteFunctional U ((1 + dot · a) * (1 + dot · b)) = 1 + dot a b / 3`. After the trace the departure has status D and exactly one remaining neighbour, whose site sum is one. Removing the departure from the traced network preserves the entire remaining partition.

For normalization, nonnegative atom weights imply that a zero total mass makes every inserted partition zero. Thus `Z * expectation f = partition f` holds also when `Z = 0`, and gives the exact normalized I₂ identity without requiring a separate network-positivity leaf. This is a proof-route change from the suggested common FiniteSpinNetwork model, with no change to the statement or its premises. No other blueprint leaf is used as a lemma.

## Axioms

```text
'AKLT.W.REC003.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every new named declaration was checked with `#print axioms`. All 71 results contain only the allowed axioms. There are no unproved residuals or forbidden proof escapes.

## Build and verification

Commands ran from `/home/ubuntu/aklt/wt/LW_REC003` using the existing Lake configuration:

| Command | Result | Wall time |
| --- | --- | --- |
| `lake build AKLT.W.REC003.Main` | Success; Main module compiled in 4.8 seconds, with previously built helpers | 10.98 seconds |
| `lake env lean AKLT/W/REC003/Audit.lean` | Success; exact type checked from an importing module, and all 71 declarations audited | 4.53 seconds |

The audit output is reproduced below and saved verbatim in `audit.txt`. A source scan found no prohibited constructs. No existing source outside `AKLT/W/REC003/` was edited; no package update or Mathlib build was run.

## Open issues

None. The earlier residual-only implementation is replaced by a complete proof. `Residual_PreFactorization`, `Residual_PostFactorization`, and `main_from_residuals` are no longer part of the delivered source.

## Audit appendix: elaborated statements and axiom output

```text
AKLT.W.REC003.phi_sq : AKLT.Defs.goldenRatio ^ 2 = AKLT.Defs.goldenRatio + 1
'AKLT.W.REC003.phi_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.radius_pos : 0 < AKLT.Defs.icoRadius
'AKLT.W.REC003.radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.radius_sq : AKLT.Defs.icoRadius ^ 2 = AKLT.Defs.goldenRatio + 2
'AKLT.W.REC003.radius_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.ico_unit (j : AKLT.Defs.IcoLetter) : AKLT.Defs.normSq (AKLT.Defs.icoVector j) = 1
'AKLT.W.REC003.ico_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.spin_ball (j : AKLT.Defs.SpinLetter) : AKLT.Defs.normSq (AKLT.Defs.spinVector j) ≤ 1
'AKLT.W.REC003.spin_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.factor_nonneg (a b : AKLT.Defs.Vec3) (ha : AKLT.Defs.normSq a ≤ 1) (hb : AKLT.Defs.normSq b ≤ 1) :
  0 ≤ 1 + AKLT.Defs.dot a b
'AKLT.W.REC003.factor_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.dot_comm (a b : AKLT.Defs.Vec3) : AKLT.Defs.dot a b = AKLT.Defs.dot b a
'AKLT.W.REC003.dot_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.site_add (s : AKLT.Defs.Status) (f g : AKLT.Defs.Vec3 → ℝ) :
  (AKLT.Defs.siteFunctional s fun v => f v + g v) = AKLT.Defs.siteFunctional s f + AKLT.Defs.siteFunctional s g
'AKLT.W.REC003.site_add' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.site_mul_const (s : AKLT.Defs.Status) (f : AKLT.Defs.Vec3 → ℝ) (c : ℝ) :
  (AKLT.Defs.siteFunctional s fun v => f v * c) = AKLT.Defs.siteFunctional s f * c
'AKLT.W.REC003.site_mul_const' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.site_sum.{u_1} {ι : Type u_1} [Fintype ι] (s : AKLT.Defs.Status) (f : ι → AKLT.Defs.Vec3 → ℝ) :
  (AKLT.Defs.siteFunctional s fun v => ∑ i, f i v) = ∑ i, AKLT.Defs.siteFunctional s (f i)
'AKLT.W.REC003.site_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.site_const (s : AKLT.Defs.Status) (hs : s = AKLT.Defs.Status.U ∨ s = AKLT.Defs.Status.D) :
  (AKLT.Defs.siteFunctional s fun x => 1) = 1
'AKLT.W.REC003.site_const' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.site_coord (s : AKLT.Defs.Status) (i : Fin 3) : (AKLT.Defs.siteFunctional s fun v => v i) = 0
'AKLT.W.REC003.site_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.site_U_coord_pair (i j : Fin 3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun v => v i * v j) = if i = j then 1 / 3 else 0
'AKLT.W.REC003.site_U_coord_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.site_linear (s : AKLT.Defs.Status) (a : AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional s fun v => AKLT.Defs.dot v a) = 0
'AKLT.W.REC003.site_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.site_U_cross (a b : AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun v => AKLT.Defs.dot v a * AKLT.Defs.dot v b) = AKLT.Defs.dot a b / 3
'AKLT.W.REC003.site_U_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.site_U_two (a b : AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun v => (1 + AKLT.Defs.dot v a) * (1 + AKLT.Defs.dot v b)) =
    1 + AKLT.Defs.dot a b / 3
'AKLT.W.REC003.site_U_two' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.site_D_one (a : AKLT.Defs.Vec3) :
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.D fun v => 1 + AKLT.Defs.dot v a) = 1
'AKLT.W.REC003.site_D_one' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.splitSpins (V : Finset AKLT.Defs.Plane) (y : AKLT.Defs.Plane) (hy : y ∈ V) :
  (↥V → AKLT.Defs.SpinLetter) ≃ AKLT.Defs.SpinLetter × (↥(V.erase y) → AKLT.Defs.SpinLetter)
'AKLT.W.REC003.splitSpins' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.extendSpins (V : Finset AKLT.Defs.Plane) (n : ↥V → AKLT.Defs.SpinLetter) (x : AKLT.Defs.Plane) :
  AKLT.Defs.Vec3
'AKLT.W.REC003.extendSpins' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.extend_split (V : Finset AKLT.Defs.Plane) (y : AKLT.Defs.Plane) (hy : y ∈ V) (j : AKLT.Defs.SpinLetter)
  (n : ↥(V.erase y) → AKLT.Defs.SpinLetter) :
  AKLT.W.REC003.extendSpins V ((AKLT.W.REC003.splitSpins V y hy).symm (j, n)) =
    Function.update (AKLT.W.REC003.extendSpins (V.erase y) n) y (AKLT.Defs.spinVector j)
'AKLT.W.REC003.extend_split' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.prod_split (V : Finset AKLT.Defs.Plane) (y : AKLT.Defs.Plane) (hy : y ∈ V)
  (s : AKLT.Defs.Plane → AKLT.Defs.Status) (j : AKLT.Defs.SpinLetter) (n : ↥(V.erase y) → AKLT.Defs.SpinLetter) :
  ∏ x, AKLT.Defs.spinWeight (s ↑x) ((AKLT.W.REC003.splitSpins V y hy).symm (j, n) x) =
    AKLT.Defs.spinWeight (s y) j * ∏ x, AKLT.Defs.spinWeight (s ↑x) (n x)
'AKLT.W.REC003.prod_split' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.sum_site (V : Finset AKLT.Defs.Plane) (y : AKLT.Defs.Plane) (hy : y ∈ V)
  (s : AKLT.Defs.Plane → AKLT.Defs.Status) (H : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  ∑ n, (∏ x, AKLT.Defs.spinWeight (s ↑x) (n x)) * H (AKLT.W.REC003.extendSpins V n) =
    ∑ n,
      (∏ x, AKLT.Defs.spinWeight (s ↑x) (n x)) *
        AKLT.Defs.siteFunctional (s y) fun v => H (Function.update (AKLT.W.REC003.extendSpins (V.erase y) n) y v)
'AKLT.W.REC003.sum_site' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.spinIntegral (V : Finset AKLT.Defs.Plane) (s : AKLT.Defs.Plane → AKLT.Defs.Status)
  (H : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) : ℝ
'AKLT.W.REC003.spinIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.spinIntegral_status (V : Finset AKLT.Defs.Plane) (s t : AKLT.Defs.Plane → AKLT.Defs.Status)
  (hst : ∀ x ∈ V, s x = t x) (H : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  AKLT.W.REC003.spinIntegral V s H = AKLT.W.REC003.spinIntegral V t H
'AKLT.W.REC003.spinIntegral_status' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.spinIntegral_site (V : Finset AKLT.Defs.Plane) (y : AKLT.Defs.Plane) (hy : y ∈ V)
  (s : AKLT.Defs.Plane → AKLT.Defs.Status) (H : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  AKLT.W.REC003.spinIntegral V s H =
    AKLT.W.REC003.spinIntegral (V.erase y) s fun m => AKLT.Defs.siteFunctional (s y) fun v => H (Function.update m y v)
'AKLT.W.REC003.spinIntegral_site' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.adjacent_symm {x z : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent x z) : AKLT.Defs.Adjacent z x
'AKLT.W.REC003.adjacent_symm' depends on axioms: [propext]
AKLT.W.REC003.adjacent_ne {x z : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent x z) : x ≠ z
'AKLT.W.REC003.adjacent_ne' depends on axioms: [propext]
AKLT.W.REC003.adjacent_positive (x z : AKLT.Defs.Plane) :
  AKLT.Defs.Adjacent x z ↔ z ∈ AKLT.Defs.positiveNeighbours x ∨ x ∈ AKLT.Defs.positiveNeighbours z
'AKLT.W.REC003.adjacent_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.positive_asymm {x z : AKLT.Defs.Plane} (h : z ∈ AKLT.Defs.positiveNeighbours x) :
  x ∉ AKLT.Defs.positiveNeighbours z
'AKLT.W.REC003.positive_asymm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.mem_neighbours (x z : AKLT.Defs.Plane) : z ∈ AKLT.Defs.neighbours x ↔ AKLT.Defs.Adjacent x z
'AKLT.W.REC003.mem_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.mem_internal (G : Finset AKLT.Defs.Plane) (e : AKLT.Defs.Plane × AKLT.Defs.Plane) :
  e ∈ AKLT.Defs.internalBonds G ↔ e.1 ∈ G ∧ e.2 ∈ AKLT.Defs.positiveNeighbours e.1 ∧ e.2 ∈ G
'AKLT.W.REC003.mem_internal' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.present_symm {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {x z : AKLT.Defs.Plane}
  (h : D.Present x z) : D.Present z x
'AKLT.W.REC003.present_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.mem_presentNeighbours {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (x z : AKLT.Defs.Plane) :
  z ∈ D.presentNeighbours x ↔ D.Present x z
'AKLT.W.REC003.mem_presentNeighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.edge (x z : AKLT.Defs.Plane) : AKLT.Defs.Plane × AKLT.Defs.Plane
'AKLT.W.REC003.edge' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.edge_cases (x z : AKLT.Defs.Plane) : AKLT.W.REC003.edge x z = (x, z) ∨ AKLT.W.REC003.edge x z = (z, x)
'AKLT.W.REC003.edge_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.edge_injective (x : AKLT.Defs.Plane) : Function.Injective (AKLT.W.REC003.edge x)
'AKLT.W.REC003.edge_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.edge_mem_bonds {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} {x z : AKLT.Defs.Plane}
  (h : D.Present x z) : AKLT.W.REC003.edge x z ∈ D.bonds
'AKLT.W.REC003.edge_mem_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.remove_active {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane) :
  (AKLT.Defs.removeSite D y).active = D.active.erase y
'AKLT.W.REC003.remove_active' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.mem_remove_bonds {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (e : AKLT.Defs.Plane × AKLT.Defs.Plane) : e ∈ (AKLT.Defs.removeSite D y).bonds ↔ e ∈ D.bonds ∧ e.1 ≠ y ∧ e.2 ≠ y
'AKLT.W.REC003.mem_remove_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.incident_edge {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  {e : AKLT.Defs.Plane × AKLT.Defs.Plane} (he : e ∈ D.bonds) (hi : e.1 = y ∨ e.2 = y) :
  ∃ z ∈ D.presentNeighbours y, e = AKLT.W.REC003.edge y z
'AKLT.W.REC003.incident_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.bonds_split {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane) :
  D.bonds = (AKLT.Defs.removeSite D y).bonds ∪ Finset.image (AKLT.W.REC003.edge y) (D.presentNeighbours y)
'AKLT.W.REC003.bonds_split' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.bonds_split_disjoint {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane) :
  Disjoint (AKLT.Defs.removeSite D y).bonds (Finset.image (AKLT.W.REC003.edge y) (D.presentNeighbours y))
'AKLT.W.REC003.bonds_split_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.no_original_leg {G : Finset AKLT.Defs.Plane} {y : AKLT.Defs.Plane} (hy : y ∉ AKLT.Defs.protectedSites G)
  (e : ↥(AKLT.Defs.originalLegs G)) : (↑e).1 ≠ y
'AKLT.W.REC003.no_original_leg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.spin_weight_nonneg (s : AKLT.Defs.Status) (j : AKLT.Defs.SpinLetter) : 0 ≤ AKLT.Defs.spinWeight s j
'AKLT.W.REC003.spin_weight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.spins_ball {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (n : ↥D.active → AKLT.Defs.SpinLetter)
  (x : AKLT.Defs.Plane) : AKLT.Defs.normSq (D.spins n x) ≤ 1
'AKLT.W.REC003.spins_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.partitionWeight {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (n : ↥D.active → AKLT.Defs.SpinLetter) : ℝ
'AKLT.W.REC003.partitionWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.partition_eq_sum {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ b f = ∑ n, AKLT.W.REC003.partitionWeight D τ b n * f (D.spins n)
'AKLT.W.REC003.partition_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.partitionWeight_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (n : ↥D.active → AKLT.Defs.SpinLetter) :
  0 ≤ AKLT.W.REC003.partitionWeight D τ b n
'AKLT.W.REC003.partitionWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.partition_zero {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (hz : (D.partition τ b fun x => 1) = 0) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ b f = 0
'AKLT.W.REC003.partition_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.partition_mul_expectation {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (D.partition τ b fun x => 1) * D.expectation τ b f = D.partition τ b f
'AKLT.W.REC003.partition_mul_expectation' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.partition_add {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (f g : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (D.partition τ b fun n => f n + g n) = D.partition τ b f + D.partition τ b g
'AKLT.W.REC003.partition_add' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.partition_div {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) (c : ℝ) :
  (D.partition τ b fun n => f n / c) = D.partition τ b f / c
'AKLT.W.REC003.partition_div' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.bondProduct {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (m : AKLT.Defs.Plane → AKLT.Defs.Vec3) : ℝ
'AKLT.W.REC003.bondProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.legProduct {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (m : AKLT.Defs.Plane → AKLT.Defs.Vec3) : ℝ
'AKLT.W.REC003.legProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.interaction {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (m : AKLT.Defs.Plane → AKLT.Defs.Vec3) : ℝ
'AKLT.W.REC003.interaction' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.bondProduct_update {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (m : AKLT.Defs.Plane → AKLT.Defs.Vec3) (v : AKLT.Defs.Vec3) :
  AKLT.W.REC003.bondProduct D (Function.update m y v) =
    AKLT.W.REC003.bondProduct (AKLT.Defs.removeSite D y) m * ∏ z ∈ D.presentNeighbours y, (1 + AKLT.Defs.dot v (m z))
'AKLT.W.REC003.bondProduct_update' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.legProduct_update {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y : AKLT.Defs.Plane) (hy : y ∉ AKLT.Defs.protectedSites G) (m : AKLT.Defs.Plane → AKLT.Defs.Vec3)
  (v : AKLT.Defs.Vec3) :
  AKLT.W.REC003.legProduct D τ b (Function.update m y v) = AKLT.W.REC003.legProduct (AKLT.Defs.removeSite D y) τ b m
'AKLT.W.REC003.legProduct_update' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.interaction_update {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y : AKLT.Defs.Plane) (hy : y ∉ AKLT.Defs.protectedSites G) (m : AKLT.Defs.Plane → AKLT.Defs.Vec3)
  (v : AKLT.Defs.Vec3) :
  AKLT.W.REC003.interaction D τ b (Function.update m y v) =
    AKLT.W.REC003.interaction (AKLT.Defs.removeSite D y) τ b m *
      ∏ z ∈ D.presentNeighbours y, (1 + AKLT.Defs.dot v (m z))
'AKLT.W.REC003.interaction_update' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.partition_repr {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ b f = AKLT.W.REC003.spinIntegral D.active D.status fun m => f m * AKLT.W.REC003.interaction D τ b m
'AKLT.W.REC003.partition_repr' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.removed_integral {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y : AKLT.Defs.Plane)
  (H : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  AKLT.W.REC003.spinIntegral (AKLT.Defs.removeSite D y).active (AKLT.Defs.removeSite D y).status H =
    AKLT.W.REC003.spinIntegral (D.active.erase y) D.status H
'AKLT.W.REC003.removed_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.partition_eliminate {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (b : Bool) (y : AKLT.Defs.Plane) (hy : y ∈ D.active) (hyS : y ∉ AKLT.Defs.protectedSites G) :
  (D.partition τ b fun x => 1) =
    (AKLT.Defs.removeSite D y).partition τ b fun m =>
      AKLT.Defs.siteFunctional (D.status y) fun v => ∏ z ∈ D.presentNeighbours y, (1 + AKLT.Defs.dot v (m z))
'AKLT.W.REC003.partition_eliminate' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.trace_active {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hy : D.status y = AKLT.Defs.Status.U) : (AKLT.Defs.traceStep D y o).active = D.active
'AKLT.W.REC003.trace_active' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.trace_present_at_y {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o z : AKLT.Defs.Plane)
  (hy : D.status y = AKLT.Defs.Status.U) (hyo : y ≠ o) : (AKLT.Defs.traceStep D y o).Present y z ↔ D.Present y z ∧ z ≠ o
'AKLT.W.REC003.trace_present_at_y' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.trace_neighbours {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hy : D.status y = AKLT.Defs.Status.U) (hyo : y ≠ o) :
  (AKLT.Defs.traceStep D y o).presentNeighbours y = (D.presentNeighbours y).erase o
'AKLT.W.REC003.trace_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.trace_present_off {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o x z : AKLT.Defs.Plane)
  (hy : D.status y = AKLT.Defs.Status.U) (hx : x ≠ y) (hz : z ≠ y) :
  (AKLT.Defs.traceStep D y o).Present x z ↔ D.Present x z
'AKLT.W.REC003.trace_present_off' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.remove_trace_bonds {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hy : D.status y = AKLT.Defs.Status.U) :
  (AKLT.Defs.removeSite (AKLT.Defs.traceStep D y o) y).bonds = (AKLT.Defs.removeSite D y).bonds
'AKLT.W.REC003.remove_trace_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.partition_congr {G : Finset AKLT.Defs.Plane} (D E : AKLT.Defs.Network G) (hs : D.status = E.status)
  (hb : D.bonds = E.bonds) (τ : AKLT.Defs.PinAssignment G) (b : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  D.partition τ b f = E.partition τ b f
'AKLT.W.REC003.partition_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.remove_trace_partition {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (y o : AKLT.Defs.Plane)
  (hy : D.status y = AKLT.Defs.Status.U) (τ : AKLT.Defs.PinAssignment G) (b : Bool)
  (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) :
  (AKLT.Defs.removeSite (AKLT.Defs.traceStep D y o) y).partition τ b f = (AKLT.Defs.removeSite D y).partition τ b f
'AKLT.W.REC003.remove_trace_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.pre_factorization (a : AKLT.Blueprint.Rec.Departure) (hy : a.D.status a.y = AKLT.Defs.Status.U)
  (f : AKLT.Defs.Plane) (hneigh : a.D.presentNeighbours a.y = {a.o, f}) (hof : a.o ≠ f) (b : Bool) :
  (a.D.partition a.τ b fun x => 1) =
    ((AKLT.Defs.removeSite a.D a.y).partition a.τ b fun x => 1) * AKLT.Blueprint.Rec.responseI₂ a.D a.τ b a.y a.o f
'AKLT.W.REC003.pre_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.post_factorization (a : AKLT.Blueprint.Rec.Departure) (hy : a.D.status a.y = AKLT.Defs.Status.U)
  (f : AKLT.Defs.Plane) (hneigh : a.D.presentNeighbours a.y = {a.o, f}) (hof : a.o ≠ f) (b : Bool) :
  ((AKLT.Defs.traceStep a.D a.y a.o).partition a.τ b fun x => 1) =
    (AKLT.Defs.removeSite a.D a.y).partition a.τ b fun x => 1
'AKLT.W.REC003.post_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC003.main : AKLT.Blueprint.Rec.TwoFactorizationStatement
'AKLT.W.REC003.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT/W/REC003/Main.lean` and six proof helper modules in the same directory.
- Exact export: `AKLT.W.REC003.main : AKLT.Blueprint.Rec.TwoFactorizationStatement`.
- Independent importing-module exact-type check passes in `AKLT/W/REC003/Audit.lean`.
- `lake build AKLT.W.REC003.Main` succeeds (10.98 seconds wall time).
- Axioms of main: `[propext, Classical.choice, Quot.sound]`.
- All 71 named declarations / 63 theorems have per-declaration axiom checks.
- Open statements: none; no residual hypotheses or external leaf dependencies.
- Route deviation: direct active-spin reindexing and nonnegative zero-mass normalization.
- Limitations affecting the requested theorem: none.
- Existing frozen definitions and other source directories are unchanged.
- Orchestrator can accept the exact theorem; no further decision or premise is needed.
