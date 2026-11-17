STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC010/AKLT/W/REC010/Main.lean): the exact requested closed theorem and the reused, cleaned trace-validity proof.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_REC010/AKLT/W/REC010/Geometry.lean): unit length of the actual icosahedron atoms, interaction-factor bounds, and six distinct pairwise nonantipodal atoms.
- [Positive.lean](/home/ubuntu/aklt/wt/LW_REC010/AKLT/W/REC010/Positive.lean): finite pin avoidance, a positive assignment, and strict partition positivity.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_REC010/AKLT/W/REC010/Audit.lean): exact-type assignment and type/axiom checks for every exported theorem.
- [Build log](/home/ubuntu/aklt/reports/LW/REC010/build-main.log) and [audit log](/home/ubuntu/aklt/reports/LW/REC010/audit.log).

## Result and proof

```lean
theorem AKLT.W.REC010.main : AKLT.Blueprint.Rec.StepRatioPositiveStatement
```

This declaration has no residual hypotheses. The earlier declarations `ResidualOriginalNormalizerPositive` and `ResidualTraceNormalizerPositive` have been removed; both obligations are proved by `partition_pos`.

The proof works directly on the finite type `D.active`. All twelve geometric atoms have squared norm one, and the zero atom lies in the unit ball. Expanding the squared norm of a sum proves that every bond and pin factor is nonnegative. A zero factor between a unit atom and a ball field forces the atom to be the field's antipode.

Use the six atoms with labels `(base, 0, sign)`. They are distinct and pairwise nonantipodal, so every bond factor between them is strictly positive. At each active site, local validity bounds the number of original legs by four. Each arbitrary unit pin can exclude at most one of the six atoms. A finite-cardinality argument therefore supplies a choice avoiding all pins at each site, independently. Its site masses, bond factors, and pin factors are all strictly positive, giving a positive summand in the partition sum. All other summands are nonnegative. This also covers the empty active set.

The trace-validity lemma proves that an admissible one-step trace remains auxiliary. Applying partition positivity to the original and traced networks proves strict positivity of the numerator and denominator of `stepRatio`; `div_pos` finishes.

The suggested reindexing into `FiniteSpinNetwork` is unnecessary for this leaf. No other blueprint leaf is assumed or used as a proved dependency.

## Exported declarations and axiom audit

The additional data definitions, all in namespace `AKLT.W.REC010`, are:

```lean
abbrev HalfLetter := Fin 3 × Fin 2
def halfLetter (j : HalfLetter) : IcoLetter := (j.1, 0, j.2)
def halfVector (j : HalfLetter) : Vec3 := icoVector (halfLetter j)
```

`networkWeight {G} (D : Network G) (τ : PinAssignment G) (b : Bool)
(n : D.active → SpinLetter) : ℝ` is the explicit unnormalized summand of `D.partition τ b (fun _ => 1)`, with the observable-one factor omitted.

The following is the captured output for all 25 exported theorems. Every theorem uses only the three permitted axioms.

```text
AKLT.W.REC010.golden_pos : 0 < AKLT.Defs.goldenRatio
'AKLT.W.REC010.golden_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.golden_sq : AKLT.Defs.goldenRatio ^ 2 = AKLT.Defs.goldenRatio + 1
'AKLT.W.REC010.golden_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.radius_pos : 0 < AKLT.Defs.icoRadius
'AKLT.W.REC010.radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.radius_sq : AKLT.Defs.icoRadius ^ 2 = AKLT.Defs.goldenRatio + 2
'AKLT.W.REC010.radius_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.ico_unit (j : AKLT.Defs.IcoLetter) : AKLT.Defs.normSq (AKLT.Defs.icoVector j) = 1
'AKLT.W.REC010.ico_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.normSq_nonneg (a : AKLT.Defs.Vec3) : 0 ≤ AKLT.Defs.normSq a
'AKLT.W.REC010.normSq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.normSq_add (a b : AKLT.Defs.Vec3) :
  AKLT.Defs.normSq (a + b) = AKLT.Defs.normSq a + AKLT.Defs.normSq b + 2 * AKLT.Defs.dot a b
'AKLT.W.REC010.normSq_add' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.dot_comm (a b : AKLT.Defs.Vec3) : AKLT.Defs.dot a b = AKLT.Defs.dot b a
'AKLT.W.REC010.dot_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.factor_nonneg {a b : AKLT.Defs.Vec3} (ha : AKLT.Defs.normSq a ≤ 1) (hb : AKLT.Defs.normSq b ≤ 1) :
  0 ≤ 1 + AKLT.Defs.dot a b
'AKLT.W.REC010.factor_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.eq_neg_of_factor_zero {a b : AKLT.Defs.Vec3} (ha : AKLT.Defs.normSq a = 1) (hb : AKLT.Defs.normSq b ≤ 1)
  (h : 1 + AKLT.Defs.dot a b = 0) : a = -b
'AKLT.W.REC010.eq_neg_of_factor_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.half_unit (j : AKLT.W.REC010.HalfLetter) : AKLT.Defs.normSq (AKLT.W.REC010.halfVector j) = 1
'AKLT.W.REC010.half_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.half_injective : Function.Injective AKLT.W.REC010.halfVector
'AKLT.W.REC010.half_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.half_ne_neg (a b : AKLT.W.REC010.HalfLetter) : AKLT.W.REC010.halfVector a ≠ -AKLT.W.REC010.halfVector b
'AKLT.W.REC010.half_ne_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.half_pair_pos (a b : AKLT.W.REC010.HalfLetter) :
  0 < 1 + AKLT.Defs.dot (AKLT.W.REC010.halfVector a) (AKLT.W.REC010.halfVector b)
'AKLT.W.REC010.half_pair_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.half_avoid.{u_1} {ι : Type u_1} [Fintype ι] (hi : Fintype.card ι < 6) (b : ι → AKLT.Defs.UnitVector) :
  ∃ j, ∀ (i : ι), 0 < 1 + AKLT.Defs.dot (↑(b i)) (AKLT.W.REC010.halfVector j)
'AKLT.W.REC010.half_avoid' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.spinWeight_nonneg (s : AKLT.Defs.Status) (j : AKLT.Defs.SpinLetter) : 0 ≤ AKLT.Defs.spinWeight s j
'AKLT.W.REC010.spinWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.spinWeight_some_pos (s : AKLT.Defs.Status) (hs : s ≠ AKLT.Defs.Status.X) (j : AKLT.Defs.IcoLetter) :
  0 < AKLT.Defs.spinWeight s (some j)
'AKLT.W.REC010.spinWeight_some_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.spinVector_ball (j : AKLT.Defs.SpinLetter) : AKLT.Defs.normSq (AKLT.Defs.spinVector j) ≤ 1
'AKLT.W.REC010.spinVector_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.spins_ball {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (n : ↥D.active → AKLT.Defs.SpinLetter)
  (x : AKLT.Defs.Plane) : AKLT.Defs.normSq (D.spins n x) ≤ 1
'AKLT.W.REC010.spins_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.networkWeight_nonneg {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (n : ↥D.active → AKLT.Defs.SpinLetter) :
  0 ≤ AKLT.W.REC010.networkWeight D τ b n
'AKLT.W.REC010.networkWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.positive_assignment {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (hlegs : ∀ x ∈ D.active, {e ∈ AKLT.Defs.originalLegs G | e.1 = x}.card ≤ 4) :
  ∃ n,
    ∀ (e : ↥(AKLT.Defs.originalLegs G)) (h : (↑e).1 ∈ D.active),
      0 < 1 + AKLT.Defs.dot (↑(τ e)) (AKLT.W.REC010.halfVector (n ⟨(↑e).1, h⟩))
'AKLT.W.REC010.positive_assignment' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.partition_pos_of_leg_bound {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (hlegs : ∀ x ∈ D.active, {e ∈ AKLT.Defs.originalLegs G | e.1 = x}.card ≤ 4)
  (b : Bool) : 0 < D.partition τ b fun x => 1
'AKLT.W.REC010.partition_pos_of_leg_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.partition_pos {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (hD : D.Auxiliary) (b : Bool) : 0 < D.partition τ b fun x => 1
'AKLT.W.REC010.partition_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.traceStep_auxiliary {G : Finset AKLT.Defs.Plane} {D : AKLT.Defs.Network G} (hD : D.Auxiliary)
  {y o : AKLT.Defs.Plane} (hy : D.AdmissibleStart y) (ho : o ∈ D.presentNeighbours y) :
  (AKLT.Defs.traceStep D y o).Auxiliary
'AKLT.W.REC010.traceStep_auxiliary' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC010.main : AKLT.Blueprint.Rec.StepRatioPositiveStatement
'AKLT.W.REC010.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Validation

Final commands, with `PATH="$HOME/.elan/bin:$PATH"`:

```sh
lake build AKLT.W.REC010.Main
lake env lean AKLT/W/REC010/Audit.lean
```

- Main build: successful, warning-free; ELAPSED 18.18 s wall time, 8.1 seconds for Main compilation. Helper modules had already been built successfully.
- Exact-type and complete axiom audit: successful; ELAPSED 4.52 s wall time.
- Audit contains `example : AKLT.Blueprint.Rec.StepRatioPositiveStatement := AKLT.W.REC010.main`, so a conditional theorem cannot pass this check.
- No prohibited proof escapes or extra assumptions occur in the delivered files.
- Only source files under `AKLT/W/REC010/` and this task's report directory were written. No sub-agents were used.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC010.main : AKLT.Blueprint.Rec.StepRatioPositiveStatement` with no residual assumptions.
- Delivered Geometry, Positive, Main, and Audit modules under `AKLT/W/REC010/`.
- Both earlier normalizer residuals are discharged and removed.
- `partition_pos` proves auxiliary-network positivity for either pin choice.
- `traceStep_auxiliary` preserves validity at every admissible departure.
- Direct finite-active-site proof replaces the suggested `Fin n` reindexing.
- All 25 exported theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- Required Main build and separate exact-type audit pass; final build is warning-free.
- No open obligations, limitations, or external proved-leaf dependencies.
- Ready for the orchestrator's exact-type acceptance check.
