STATUS: PARTIAL

The exact requested closed theorem is not proved. The compiled delivery proves the reduction

```lean
AKLT.W.REC090.coveredRatio_of_localMixture :
  AKLT.Blueprint.Rec.LocalMixtureStatementV2 →
    AKLT.Blueprint.Rec.CoveredRatioStatementV2
```

The sole open blueprint dependency is **`AKLT.Blueprint.Rec.LocalMixtureStatementV2`**, defined in `AKLT/Blueprint/Rec/NodesV2Local.lean:18`. It is absent from `/home/ubuntu/aklt/state/lw/proved-index.tsv`. No unindexed leaf is imported or treated as proved.

The exact type of the delivered `main` is deliberately recorded here:

```lean
def AKLT.W.REC090.Residual_localMixture : Prop :=
  AKLT.Blueprint.Rec.LocalMixtureStatementV2

theorem AKLT.W.REC090.main :
  AKLT.W.REC090.Residual_localMixture →
    AKLT.Blueprint.Rec.CoveredRatioStatementV2
```

Thus this delivery does not pass the requested closed-type check. The residual is transparent, closed, and contains only the common geometric representation; it contains no H1 assumption, numerical inequality, or quotient conclusion.

Files in `AKLT/W/REC090/`:

- `Main.lean` — unconditional current/next normalizer positivity, the H1 averaging and division argument, and the explicit conditional `main` and named-leaf reduction.
- `Mixtures.lean` — new conversion in both directions between the earlier ball-field residual and the exact shared-mixture blueprint leaf. Slot choices are flattened into one finite index, preserving common weights for current and next.
- `Positivity.lean` — retained proof that every network partition normalizer is strictly positive, for either pin choice.
- `Slots.lean` — retained single-slot convexity and finite simultaneous slot expansion.
- `BallPatterns.lean` — retained common current/next unit-field resolution and extension of H1 to ball fields.
- `Audit.lean` — statements and `#print axioms` for all 36 exported theorems, plus a checked exact conditional reduction.

Report artifacts: `build-main.log`, `build-main.time`, `build-audit.log`, `build-audit.time`, `declaration-audit.txt`, `source-audit.txt`, `exact-type-check.log`, and `exact-type-check.time`. The earlier `report.luna.md` is preserved. Only the assigned Lean directory and report directory were edited; the failing diagnostic was written under `/tmp`.

The new equivalence is

```lean
AKLT.W.REC090.sharedBallMixture_iff_localMixture :
  AKLT.W.REC090.Residual_sharedBallMixture ↔
    AKLT.Blueprint.Rec.LocalMixtureStatementV2
```

It proves that leaving the fields in the closed ball does not reduce the remaining geometric obligation: resolving each slot, multiplying its nonnegative coefficient by the outer weight, and reindexing the product into `Fin k` gives precisely the frozen leaf. The reverse implication simply regards unit vectors as ball vectors.

The retained ratio proof applies H1 to each pattern, uses the type equivalence to select the actual straight/turn threshold, multiplies by nonnegative common weights, and sums. It obtains `c * Znext ≤ Zcurrent`. Both normalizers are proved positive with no residual hypothesis before division. Dividing by `Zcurrent` then gives `stepRatio ≤ c⁻¹ = passageFactor`.

What remains: prove `AKLT.Blueprint.Rec.LocalMixtureStatementV2` from its own `Departure` and shared-cover hypotheses. This requires the global finite disintegration over outside spins, the geometric reindexing of internal present bonds, and simultaneous replacement of the four actual tips in the current and next networks. The indexed `TipReplacementStatement` and `BallSlotConvexityStatement` supply local identities, but do not supply this global gluing theorem. No counterexample or missing mathematical premise has been established. This is an incomplete proof, not a claim that the target is false.

For clarity, the one residual unfolds to the following existing closed statement (`open AKLT.Defs`):

```lean
∀ a : AKLT.Blueprint.Rec.Departure, a.D.status a.y = .U →
  ∀ incoming outgoing : Compass,
    a.o = a.y + outgoing.step →
    AKLT.Defs.CoveredDepartureV2 a.D a.y incoming outgoing →
    ∃ k : ℕ, ∃ π : Fin k → PatternData,
      ∃ m : Fin k → (Fin 20 → UnitVector), ∃ weight : Fin k → ℝ,
      (∀ i, 0 ≤ weight i ∧ (π i).Covered ∧
        ((π i).outgoing = .north ↔ outgoing = incoming)) ∧
      a.D.partition a.τ true (fun _ => 1) =
        ∑ i, weight i * patternCurrent (π i) (m i) ∧
      (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) =
        ∑ i, weight i * patternNext (π i) (m i)
```

Validation:

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC090.Main` passed. Fresh Lake module times: `Mixtures` 3.4 s, `Main` 3.5 s. The recorded subsequent cached command took 6.42 s wall time.
- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC090.Audit` passed, 10.54 s wall time (Audit module 3.6 s).
- All 36 exported theorems have actual `#print axioms` output exactly `[propext, Classical.choice, Quot.sound]`, reproduced below.
- A source audit checked that every exported theorem is included in `Audit.lean` and found no forbidden proof constructs.
- `PATH="$HOME/.elan/bin:$PATH" lake env lean /tmp/rec090-exact-type.lean` failed, 3.73 s wall time, because the unconditional type is still unavailable. The diagnostic is:

```text
/tmp/rec090-exact-type.lean:3:56: error: Type mismatch
  AKLT.W.REC090.main
has type
  AKLT.W.REC090.Residual_localMixture → AKLT.Blueprint.Rec.CoveredRatioStatementV2
but is expected to have type
  AKLT.Blueprint.Rec.CoveredRatioStatementV2
```

Exported theorem statements, definition checks, and actual axiom audit output:

```text
AKLT.W.REC090.normSq_nonneg : ∀ (v : AKLT.Defs.Vec3), 0 ≤ AKLT.Defs.normSq v
'AKLT.W.REC090.normSq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.normSq_add : ∀ (a b : AKLT.Defs.Vec3),
  AKLT.Defs.normSq (a + b) = AKLT.Defs.normSq a + AKLT.Defs.normSq b + 2 * AKLT.Defs.dot a b
'AKLT.W.REC090.normSq_add' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC090.normSq_eq_zero : ∀ {v : AKLT.Defs.Vec3}, AKLT.Defs.normSq v = 0 → v = 0
'AKLT.W.REC090.normSq_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC090.ball_factor_nonneg : ∀ {a b : AKLT.Defs.Vec3},
  AKLT.Defs.normSq a ≤ 1 → AKLT.Defs.normSq b ≤ 1 → 0 ≤ 1 + AKLT.Defs.dot a b
'AKLT.W.REC090.ball_factor_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC090.ball_factor_zero : ∀ {a b : AKLT.Defs.Vec3},
  AKLT.Defs.normSq a ≤ 1 → AKLT.Defs.normSq b ≤ 1 → 1 + AKLT.Defs.dot a b = 0 → a = -b
'AKLT.W.REC090.ball_factor_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.goldenRatio_pos : 0 < AKLT.Defs.goldenRatio
'AKLT.W.REC090.goldenRatio_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.goldenRatio_sq : AKLT.Defs.goldenRatio ^ 2 = AKLT.Defs.goldenRatio + 1
'AKLT.W.REC090.goldenRatio_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.icoRadius_pos : 0 < AKLT.Defs.icoRadius
'AKLT.W.REC090.icoRadius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.icoRadius_sq : AKLT.Defs.icoRadius ^ 2 = AKLT.Defs.goldenRatio + 2
'AKLT.W.REC090.icoRadius_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.icoVector_unit : ∀ (j : AKLT.Defs.IcoLetter), AKLT.Defs.normSq (AKLT.Defs.icoVector j) = 1
'AKLT.W.REC090.icoVector_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.spinVector_ball : ∀ (j : AKLT.Defs.SpinLetter), AKLT.Defs.normSq (AKLT.Defs.spinVector j) ≤ 1
'AKLT.W.REC090.spinVector_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.spinWeight_nonneg : ∀ (s : AKLT.Defs.Status) (j : AKLT.Defs.SpinLetter), 0 ≤ AKLT.Defs.spinWeight s j
'AKLT.W.REC090.spinWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC090.spinWeight_some_pos : ∀ {s : AKLT.Defs.Status},
  s ≠ AKLT.Defs.Status.X → ∀ (j : AKLT.Defs.IcoLetter), 0 < AKLT.Defs.spinWeight s (some j)
'AKLT.W.REC090.spinWeight_some_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC090.network_spins_ball : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (n : ↥D.active → AKLT.Defs.SpinLetter) (x : AKLT.Defs.Plane), AKLT.Defs.normSq (D.spins n x) ≤ 1
'AKLT.W.REC090.network_spins_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC090.partition_nonneg : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (pinned : Bool), 0 ≤ D.partition τ pinned fun x => 1
'AKLT.W.REC090.partition_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.goldenRatio_gt_one : 1 < AKLT.Defs.goldenRatio
'AKLT.W.REC090.goldenRatio_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.positiveLetter_sum_pos : ∀ (j : AKLT.W.REC090.PositiveLetter),
  0 < ∑ i, AKLT.Defs.icoVector (AKLT.W.REC090.positiveLetter j) i
'AKLT.W.REC090.positiveLetter_sum_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.positiveLetter_injective : Function.Injective fun j =>
  AKLT.Defs.icoVector (AKLT.W.REC090.positiveLetter j)
'AKLT.W.REC090.positiveLetter_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.positiveLetter_factor_pos : ∀ (a b : AKLT.W.REC090.PositiveLetter),
  0 <
    1 +
      AKLT.Defs.dot (AKLT.Defs.icoVector (AKLT.W.REC090.positiveLetter a))
        (AKLT.Defs.icoVector (AKLT.W.REC090.positiveLetter b))
'AKLT.W.REC090.positiveLetter_factor_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC090.exists_positiveLetter : ∀ {ι : Type u_1} [DecidableEq ι] (s : Finset ι) (p : ι → AKLT.Defs.UnitVector),
  s.card < 6 → ∃ j, ∀ i ∈ s, 0 < 1 + AKLT.Defs.dot (↑(p i)) (AKLT.Defs.icoVector (AKLT.W.REC090.positiveLetter j))
'AKLT.W.REC090.exists_positiveLetter' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC090.originalLegs_neighbour : ∀ {G : Finset AKLT.Defs.Plane} {e : AKLT.Defs.Plane × AKLT.Defs.Plane},
  e ∈ AKLT.Defs.originalLegs G → e.2 ∈ AKLT.Defs.neighbours e.1
'AKLT.W.REC090.originalLegs_neighbour' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.originalLegs_at_card_le_four : ∀ (G : Finset AKLT.Defs.Plane) (x : AKLT.Defs.Plane),
  {e ∈ AKLT.Defs.originalLegs G | e.1 = x}.card ≤ 4
'AKLT.W.REC090.originalLegs_at_card_le_four' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC090.partition_pos : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) (τ : AKLT.Defs.PinAssignment G)
  (pinned : Bool), 0 < D.partition τ pinned fun x => 1
'AKLT.W.REC090.partition_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.ball_slot_convexity : ∀ (b : AKLT.Defs.Vec3),
  AKLT.Defs.normSq b ≤ 1 →
    ∃ e t,
      0 ≤ t ∧
        t ≤ 1 ∧
          ∀ (n : AKLT.Defs.Vec3),
            1 + AKLT.Defs.dot n b = t * (1 + AKLT.Defs.dot n ↑e) + (1 - t) * (1 + AKLT.Defs.dot n (-↑e))
'AKLT.W.REC090.ball_slot_convexity' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC090.ball_slots_mixture : ∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι]
  (b : ι → AKLT.Defs.Vec3),
  (∀ (j : ι), AKLT.Defs.normSq (b j) ≤ 1) →
    ∃ m weight,
      (∀ (σ : ι → Bool), 0 ≤ weight σ) ∧
        ∑ σ, weight σ = 1 ∧
          ∀ (n : ι → AKLT.Defs.Vec3),
            ∏ j, (1 + AKLT.Defs.dot (n j) (b j)) = ∑ σ, weight σ * ∏ j, (1 + AKLT.Defs.dot (n j) ↑(m σ j))
'AKLT.W.REC090.ball_slots_mixture' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.patternBallFunctional_unit : ∀ (π : AKLT.Defs.PatternData) (next : Bool)
  (m : Fin 20 → AKLT.Defs.UnitVector) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ),
  AKLT.W.REC090.patternBallFunctional π next (fun j => ↑(m j)) f = AKLT.Defs.patternFunctional π next m f
'AKLT.W.REC090.patternBallFunctional_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.dot_comm : ∀ (a b : AKLT.Defs.Vec3), AKLT.Defs.dot a b = AKLT.Defs.dot b a
'AKLT.W.REC090.dot_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.patternBallFunctional_mixture : ∀ (π : AKLT.Defs.PatternData) (b : Fin 20 → AKLT.Defs.Vec3),
  (∀ (j : Fin 20), AKLT.Defs.normSq (b j) ≤ 1) →
    ∃ m weight,
      (∀ (σ : Fin 20 → Bool), 0 ≤ weight σ) ∧
        ∑ σ, weight σ = 1 ∧
          ∀ (next : Bool) (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ),
            AKLT.W.REC090.patternBallFunctional π next b f = ∑ σ, weight σ * AKLT.Defs.patternFunctional π next (m σ) f
'AKLT.W.REC090.patternBallFunctional_mixture' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.h1_ball_pattern_bound : AKLT.Blueprint.Top.H1Statement →
  ∀ (π : AKLT.Defs.PatternData),
    π.Covered →
      ∀ (b : Fin 20 → AKLT.Defs.Vec3),
        (∀ (j : Fin 20), AKLT.Defs.normSq (b j) ≤ 1) →
          ((if π.outgoing = AKLT.Defs.Compass.north then 961 / 1000 else 187 / 200) *
              AKLT.W.REC090.patternBallFunctional π true b fun x => 1) ≤
            AKLT.W.REC090.patternBallFunctional π false b fun x => 1
'AKLT.W.REC090.h1_ball_pattern_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.positive_normalizers : ∀ (a : AKLT.Blueprint.Rec.Departure),
  (0 < a.D.partition a.τ true fun x => 1) ∧ 0 < (AKLT.Defs.traceStep a.D a.y a.o).partition a.τ true fun x => 1
'AKLT.W.REC090.positive_normalizers' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.localMixture_of_sharedBallMixture : AKLT.W.REC090.Residual_sharedBallMixture →
  AKLT.Blueprint.Rec.LocalMixtureStatementV2
'AKLT.W.REC090.localMixture_of_sharedBallMixture' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.sharedBallMixture_of_localMixture : AKLT.Blueprint.Rec.LocalMixtureStatementV2 →
  AKLT.W.REC090.Residual_sharedBallMixture
'AKLT.W.REC090.sharedBallMixture_of_localMixture' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.sharedBallMixture_iff_localMixture : AKLT.W.REC090.Residual_sharedBallMixture ↔
  AKLT.Blueprint.Rec.LocalMixtureStatementV2
'AKLT.W.REC090.sharedBallMixture_iff_localMixture' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.coveredRatio_of_sharedBallMixture : AKLT.W.REC090.Residual_sharedBallMixture →
  AKLT.Blueprint.Rec.CoveredRatioStatementV2
'AKLT.W.REC090.coveredRatio_of_sharedBallMixture' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.main : AKLT.W.REC090.Residual_localMixture → AKLT.Blueprint.Rec.CoveredRatioStatementV2
'AKLT.W.REC090.main' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.coveredRatio_of_localMixture : AKLT.Blueprint.Rec.LocalMixtureStatementV2 →
  AKLT.Blueprint.Rec.CoveredRatioStatementV2
'AKLT.W.REC090.coveredRatio_of_localMixture' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.Residual_sharedBallMixture : Prop
def AKLT.W.REC090.Residual_localMixture : Prop :=
AKLT.Blueprint.Rec.LocalMixtureStatementV2
AKLT.W.REC090.patternBallFunctional (π : AKLT.Defs.PatternData) (next : Bool) (b : Fin 20 → AKLT.Defs.Vec3)
  (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) : ℝ
```

## ORCH-SUMMARY

- STATUS: PARTIAL; the requested closed `AKLT.W.REC090.main` is not proved.
- Delivered six compiled Lean files in `AKLT/W/REC090/`.
- `main` explicitly assumes transparent `AKLT.W.REC090.Residual_localMixture`.
- Exact open dependency: `AKLT.Blueprint.Rec.LocalMixtureStatementV2`.
- That dependency is absent from the supplied proved-leaf index.
- Proved `LocalMixtureStatementV2 → CoveredRatioStatementV2`.
- Proved the earlier ball-mixture residual equivalent to `LocalMixtureStatementV2`.
- Normalizer positivity, slot resolution, H1 averaging, and division are proved.
- Remaining work is global disintegration, geometric reindexing, and common tip replacement.
- No other residuals, unproved imported leaves, frozen-source edits, or extra axioms.
- Main and Audit builds pass; all 36 exported theorems use only permitted axioms.
- The exact unconditional type check fails; this is an explicit delivery limitation.
- Orchestrator must prove/supply `LocalMixtureStatementV2`, then discharge `main`'s residual.
