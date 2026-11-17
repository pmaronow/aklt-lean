STATUS: PROVED

## Files

- [AKLT/W/REC070/Main.lean](/home/ubuntu/aklt/wt/LW_REC070/AKLT/W/REC070/Main.lean) — Exact requested theorem.
- [AKLT/W/REC070/Foundations.lean](/home/ubuntu/aklt/wt/LW_REC070/AKLT/W/REC070/Foundations.lean) — Coefficient positivity, first-visit ordering, lattice geometry, and finite shift support.
- [AKLT/W/REC070/TrailBound.lean](/home/ubuntu/aklt/wt/LW_REC070/AKLT/W/REC070/TrailBound.lean) — Nonreversal, the response-coefficient envelope, exposure linearity, and the full first-visit product comparison.
- [AKLT/W/REC070/Mass.lean](/home/ubuntu/aklt/wt/LW_REC070/AKLT/W/REC070/Mass.lean) — The finite length mass bound from H2 and the dyadic witness ratio bound.
- [AKLT/W/REC070/Shift.lean](/home/ubuntu/aklt/wt/LW_REC070/AKLT/W/REC070/Shift.lean) — The shift-power increment estimate, proved using the elementary power inequality.
- [AKLT/W/REC070/Regroup.lean](/home/ubuntu/aklt/wt/LW_REC070/AKLT/W/REC070/Regroup.lean) — Unconditional regrouping of the nonnegative ENNReal row.
- [AKLT/W/REC070/Increment.lean](/home/ubuntu/aklt/wt/LW_REC070/AKLT/W/REC070/Increment.lean) — The finite real row increment estimate and its ENNReal translation.
- [AKLT/W/REC070/Budget.lean](/home/ubuntu/aklt/wt/LW_REC070/AKLT/W/REC070/Budget.lean) — Reused geometric-series calculation and final budget assembly from the earlier attempt.
- [AKLT/W/REC070/Audit.lean](/home/ubuntu/aklt/wt/LW_REC070/AKLT/W/REC070/Audit.lean) — Exact-type check and type/axiom checks for every exported theorem.

The earlier report remains in `report.luna.md`. The complete verification output is in [audit.log](/home/ubuntu/aklt/reports/LW/REC070/audit.log).

## Requested declaration

```lean
theorem AKLT.W.REC070.main : AKLT.Blueprint.Rec.WitnessPerturbationStatement
```

This theorem has no additional hypotheses. Both previously open residuals are now proved: `rowExpansion_proved : Residual_RowExpansion` and `lengthIncrement_proved : Residual_LengthIncrement`. `geometricBudget_proved` discharges the third, already solved bound. The residual definition names are retained only to reuse the earlier proof assembly.

## Proof

1. The fixed cutoff-twelve ordering permutes the first visits, is duplicate-free, and has length at most n. The product of its passage factors, multiplied by the base trail weight, is exactly the H2 trail weight. Passage factors are at least one, so each exposure is bounded by the full product.
2. A true trail cannot immediately reverse. Its outgoing site belongs to the three nonarrival neighbours. Enlarge the live response pairs to all pairs of those three sites; exactly two contain the outgoing site. The frozen rational coefficient tables therefore give total reward at most C = 18094/100000 + 2(36751/100000).
3. Every response site is a neighbour of its departure vertex. Its distance from the start is at most i+1, giving the sufficient support bound s ≤ n+1. Coefficients are nonnegative, and support makes each shift sum finite. All kernel-series regrouping is performed in ENNReal.
4. Sum the exposure bound over closed trails, include them in the open trails of H2, and apply the exact dyadic witness bound h_Y ≤ H h_X. The length-n weighted mass is at most H h_X n C CV q^n.
5. For b=(1+q)/2 < θ ≤ 1, prove 0 ≤ θ^(-s)-1 ≤ (1-θ)(n+1)b^(-n-2). This uses 1-θ^s ≤ s(1-θ), positive powers, and inverse monotonicity; it avoids a differentiation argument.
6. Sum n(n+1)(q/b)^n = 2(q/b)/(1-q/b)^3, yielding the exact `transportB` budget. Add the given numerical unshifted-row inequality and apply the explicit budget premise. The witness and ordering are the original definitions throughout.

No H3 leaf or other blueprint leaf is assumed. The target already supplies the unshifted-row bound numerically, so an independent H3 cutoff-exhaustion proof is unnecessary. The weaker support bound s ≤ n+1 suffices for this statement; the separate n/2+1 geometry leaf is not used.

## Supporting definitions

All declarations below are in namespace `AKLT.W.REC070`. These transparent definitions specify the notation used by the theorem types.

```lean
def RowLength (θ : ℝ) (X : PairType) (n : ℕ) : ℝ≥0∞ :=
  ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2),
    ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
      ENNReal.ofReal (witnessReal Y) * ENNReal.ofReal (θ ^ (-(s : ℤ)))

def RowLengthError (CV q θ : ℝ) (X : PairType) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - θ) * witnessRatio *
    (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) * CV *
    ((1 + q) / 2)^(-2 : ℤ) * (n : ℝ) * (n + 1 : ℝ) *
    (q / ((1 + q) / 2))^n * witnessReal X)

def RowError (CV q θ : ℝ) (X : PairType) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - θ) * transportB CV q * witnessReal X)

def Residual_RowExpansion : Prop :=
  ∀ θ : ℝ, 0 < θ → ∀ X : PairType,
    (∑ Y : PairType, shiftedKernel θ X Y * ENNReal.ofReal (witnessReal Y)) =
      ∑' n : ℕ, RowLength θ X n

def Residual_LengthIncrement : Prop :=
  ∀ CV q : ℝ, OpenTrailBound CV q → ∀ θ : ℝ,
    (1 + q) / 2 < θ → θ ≤ 1 → ∀ X : PairType, ∀ n : ℕ,
      RowLength θ X n ≤ RowLength 1 X n + RowLengthError CV q θ X n

def Residual_GeometricBudget : Prop :=
  ∀ CV q θ : ℝ, 0 ≤ CV → 0 < q → q < 1 → (1 + q) / 2 < θ → θ ≤ 1 →
    ∀ X : PairType,
      (∑' n : ℕ, RowLengthError CV q θ X n) ≤ RowError CV q θ X

def responseCap : ℚ := 18094 / 100000 + 2 * (36751 / 100000)

def rowReal (θ : ℝ) (X : PairType) (n : ℕ) : ℝ :=
  ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2),
    (kernelLengthCoefficient X Y s n : ℝ) * witnessReal Y * θ^(-(s : ℤ))
```

## Exported theorem statements

The following is the successful `#check @...` output for all 42 exported theorems. Names are relative to `AKLT.W.REC070`; the exact type check is also an `example` in `Audit.lean`.

```text
factor_one_le : ∀ (b : Bool), 1 ≤ passageFactor b
@pairCoefficient_nonneg : ∀ {n : ℕ} (w : DirectionWord n) (i : Fin n) (p : Finset Plane), 0 ≤ pairCoefficient w i p
@exposure_nonneg : ∀ {n : ℕ} (w : DirectionWord n) (r : Fin n → ℚ),
  (∀ (i : Fin n), 0 ≤ r i) → ∀ (l : List (Fin n)), 0 ≤ exposureSum w r l
@base_nonneg : ∀ {n : ℕ} (w : DirectionWord n), 0 ≤ trailBaseWeight kernelStart w
@kappa_nonneg : ∀ {n : ℕ} (X Y : PairType) (s : ℕ) (w : DirectionWord n) (i : Fin n), 0 ≤ responseKappa X Y s w i
coefficient_nonneg : ∀ (X Y : PairType) (s n : ℕ), 0 ≤ kernelLengthCoefficient X Y s n
@ordering_perm : ∀ {n : ℕ} (w : DirectionWord n), (kernelOrdering w).Perm (firstVisitList w)
@ordering_nodup : ∀ {n : ℕ} (w : DirectionWord n), (kernelOrdering w).Nodup
@ordering_length : ∀ {n : ℕ} (w : DirectionWord n), (kernelOrdering w).length ≤ n
lattice_triangle : ∀ (x y z : Plane), latticeDist x z ≤ latticeDist x y + latticeDist y z
lattice_symm : ∀ (x y : Plane), latticeDist x y = latticeDist y x
neighbour_dist : ∀ (v z : Plane), z ∈ neighbours v → latticeDist z v = 1
@vertex_dist : ∀ {n : ℕ} (w : DirectionWord n), ∀ j ≤ n, latticeDist (wordVertex kernelStart w j) kernelStart ≤ j
@response_near : ∀ {n : ℕ} (w : DirectionWord n) (i : Fin n),
  ∀ p ∈ responsePairs w i, ∀ {z : Plane}, z ∈ p → z ∈ neighbours (wordVertex kernelStart w ↑i)
@pairShift_le : ∀ {n : ℕ} (X : PairType) (w : DirectionWord n) (i : Fin n),
  ∀ p ∈ responsePairs w i, pairShift X p ≤ n + 1
coefficient_support : ∀ (X Y : PairType) (n s : ℕ), n + 1 < s → kernelLengthCoefficient X Y s n = 0
@coefficient_cap : ∀ {n : ℕ} (w : DirectionWord n) (i : Fin n) (p : Finset Plane),
  pairCoefficient w i p ≤ if wordVertex kernelStart w (↑i + 1) ∈ p then 36751 / 100000 else 18094 / 100000
step_injective : Function.Injective Compass.step
@nonreverse : ∀ {n : ℕ} (w : DirectionWord n),
  IsTrail kernelStart kernelIncoming w → ∀ (i : Fin n), w i ≠ (wordIncoming kernelIncoming w i).reverse
neighbours_card : ∀ (v : Plane), (neighbours v).card = 4
@responseNeighbours_card : ∀ {n : ℕ} (w : DirectionWord n) (i : Fin n), (responseNeighbours w i).card = 3
@outgoing_mem : ∀ {n : ℕ} (w : DirectionWord n),
  IsTrail kernelStart kernelIncoming w → ∀ (i : Fin n), wordVertex kernelStart w (↑i + 1) ∈ responseNeighbours w i
@pair_sum_cap : ∀ {n : ℕ} (w : DirectionWord n),
  IsTrail kernelStart kernelIncoming w → ∀ (i : Fin n), ∑ p ∈ responsePairs w i, pairCoefficient w i p ≤ responseCap
@response_total : ∀ {n : ℕ} (X : PairType) (w : DirectionWord n) (i : Fin n),
  ∑ Y, ∑ s ∈ Finset.range (n + 2), responseKappa X Y s w i = ∑ p ∈ responsePairs w i, pairCoefficient w i p
@exposure_sum : ∀ {n : ℕ} {α : Type u_1} (w : DirectionWord n) (t : Finset α) (r : α → Fin n → ℚ) (l : List (Fin n)),
  exposureSum w (fun i => ∑ a ∈ t, r a i) l = ∑ a ∈ t, exposureSum w (r a) l
@ordering_product : ∀ {n : ℕ} (w : DirectionWord n),
  trailBaseWeight kernelStart w *
      (List.map (fun i => passageFactor (wordStraight kernelIncoming w i)) (kernelOrdering w)).prod =
    trailWeight kernelStart kernelIncoming w
@exposure_cap : ∀ {n : ℕ} (w : DirectionWord n) (r : Fin n → ℚ),
  (∀ (i : Fin n), r i ≤ responseCap) →
    ∀ (l : List (Fin n)),
      exposureSum w r l ≤
        ↑l.length * responseCap * (List.map (fun i => passageFactor (wordStraight kernelIncoming w i)) l).prod
coefficient_total : ∀ (X : PairType) (n : ℕ),
  ∑ Y, ∑ s ∈ Finset.range (n + 2), kernelLengthCoefficient X Y s n =
    ∑ w,
      if ClosedTrail X w then
        trailBaseWeight kernelStart w *
          exposureSum w (fun i => ∑ Y, ∑ s ∈ Finset.range (n + 2), responseKappa X Y s w i) (kernelOrdering w)
      else 0
@closed_exposure_bound : ∀ {n : ℕ} (X : PairType) (w : DirectionWord n),
  ClosedTrail X w →
    trailBaseWeight kernelStart w *
        exposureSum w (fun i => ∑ Y, ∑ s ∈ Finset.range (n + 2), responseKappa X Y s w i) (kernelOrdering w) ≤
      ↑n * responseCap * trailWeight kernelStart kernelIncoming w
coefficient_mass_bound : ∀ (CV q : ℝ),
  OpenTrailBound CV q →
    ∀ (X : PairType) (n : ℕ),
      ∑ Y, ∑ s ∈ Finset.range (n + 2), ↑(kernelLengthCoefficient X Y s n) ≤ ↑n * ↑responseCap * CV * q ^ n
witness_ratio_bound : ∀ (X Y : PairType), witnessReal Y ≤ witnessRatio * witnessReal X
weighted_mass_bound : ∀ (CV q : ℝ),
  OpenTrailBound CV q →
    ∀ (X : PairType) (n : ℕ),
      ∑ Y, ∑ s ∈ Finset.range (n + 2), ↑(kernelLengthCoefficient X Y s n) * witnessReal Y ≤
        witnessRatio * witnessReal X * (↑n * ↑responseCap * CV * q ^ n)
shift_increment : ∀ (b θ : ℝ),
  0 < b →
    b < θ → θ ≤ 1 → ∀ (n s : ℕ), s ≤ n + 1 → 0 ≤ θ ^ (-↑s) - 1 ∧ θ ^ (-↑s) - 1 ≤ (1 - θ) * (↑n + 1) * b ^ (-↑n - 2)
geometricBudget_proved : Residual_GeometricBudget
main_of_residuals : Residual_RowExpansion → Residual_LengthIncrement → WitnessPerturbationStatement
rowExpansion_proved : Residual_RowExpansion
coefficient_real_nonneg : ∀ (X Y : PairType) (s n : ℕ), 0 ≤ ↑(kernelLengthCoefficient X Y s n)
rowReal_nonneg : ∀ (θ : ℝ), 0 < θ → ∀ (X : PairType) (n : ℕ), 0 ≤ rowReal θ X n
rowLength_real : ∀ (θ : ℝ), 0 < θ → ∀ (X : PairType) (n : ℕ), RowLength θ X n = ENNReal.ofReal (rowReal θ X n)
budget_factor : ∀ (b q : ℝ), 0 < b → ∀ (n : ℕ), q ^ n * b ^ (-↑n - 2) = b ^ (-2) * (q / b) ^ n
lengthIncrement_proved : Residual_LengthIncrement
main : WitnessPerturbationStatement
```

## Axioms

The following is the complete `#print axioms` output, checked separately for every exported theorem. All dependencies belong to the permitted set `{propext, Classical.choice, Quot.sound}`.

```text
'AKLT.W.REC070.factor_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.pairCoefficient_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.exposure_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.base_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.kappa_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.coefficient_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.ordering_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.ordering_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.ordering_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.lattice_triangle' depends on axioms: [propext, Quot.sound]
'AKLT.W.REC070.lattice_symm' depends on axioms: [propext, Quot.sound]
'AKLT.W.REC070.neighbour_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.vertex_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.response_near' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.pairShift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.coefficient_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.coefficient_cap' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.step_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.nonreverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.neighbours_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.responseNeighbours_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.outgoing_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.pair_sum_cap' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.response_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.exposure_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.ordering_product' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.exposure_cap' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.coefficient_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.closed_exposure_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.coefficient_mass_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.witness_ratio_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.weighted_mass_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.shift_increment' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.geometricBudget_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.rowExpansion_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.coefficient_real_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.rowReal_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.rowLength_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.budget_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.lengthIncrement_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC070.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build and verification

- `PATH="$HOME/.elan/bin:$PATH" /usr/bin/time -p lake build AKLT.W.REC070.Main` — passed with no warnings; elapsed 20.45 s, user 22.41 s, system 5.78 s. The final module itself took 3.3 s.
- `PATH="$HOME/.elan/bin:$PATH" /usr/bin/time -p lake env lean AKLT/W/REC070/Audit.lean` — passed; elapsed 4.27 s, user 3.11 s, system 3.40 s. This includes the exact expected type and all 42 axiom checks.
- Scanned all delivered Lean files for forbidden constructs: no matches.
- Only files in `AKLT/W/REC070/` and the assigned report directory were written. Frozen statements and existing library files are unchanged.

## Open issues

None. The requested theorem is delivered without unresolved residual assumptions.

## ORCH-SUMMARY

- STATUS: PROVED.
- Exact deliverable: `AKLT/W/REC070/Main.lean`.
- Exact theorem: `AKLT.W.REC070.main : AKLT.Blueprint.Rec.WitnessPerturbationStatement`.
- Added seven proof helper modules and `Audit.lean`, all in the task directory.
- Reused the prior geometric budget and final assembly; proved both prior residuals.
- Every exported theorem was checked with `#print axioms`; only permitted axioms occur.
- `lake build AKLT.W.REC070.Main` passed (20.45 s).
- Exact-type/axiom audit passed (4.27 s).
- The sufficient shift bound is n+1; no need for the separate sharper geometry leaf.
- The numerical unshifted-row premise is used directly; no H3 or other leaf assumption.
- Open declarations: none.
- Limitations/deviations: helper residual names retained; all are discharged.
- Orchestrator action: accept the exact theorem; no dependency proof is outstanding.
