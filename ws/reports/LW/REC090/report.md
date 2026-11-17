STATUS: PROVED FROM DEPS

Delivered the exact closed theorem in `AKLT/W/REC090/Main.lean:86`:

```lean
theorem AKLT.W.REC090.main :
    AKLT.Blueprint.Rec.CoveredRatioStatementV2 :=
  AKLT.W.REC090.coveredRatio_of_localMixture AKLT.W.REC089.main
```

The only direct blueprint dependency is now proved and authorized by the supplied index:

| Statement | Proved theorem | Imported module |
| --- | --- | --- |
| `AKLT.Blueprint.Rec.LocalMixtureStatementV2` | `AKLT.W.REC089.main` | `AKLT.W.REC089.Main` |

This removes the earlier attempt's sole remaining premise. There are no open residual obligations and no additional hypotheses on `main`. The original H1 hypothesis remains inside the frozen target statement.

The retained proof applies H1 to each shared-cover mixture term, selects the threshold from the straight/turn equivalence, multiplies by the common nonnegative weights, and sums to obtain `c * Znext ≤ Zcurrent`. `partition_pos` proves every network normalizer positive, and `positive_normalizers` supplies positivity for both the current and next networks. Division by the positive current normalizer gives `stepRatio ≤ c⁻¹ = passageFactor`. The unit-field mixture from REC089 enters the existing ball-field reduction through `sharedBallMixture_of_localMixture`.

Files under the assigned directory:

- `Main.lean` — positive current/next normalizers, the averaging and division argument, and the exact closed `main`. Now imports the indexed REC089 proof.
- `Mixtures.lean` — conversions between ball-field and unit-field shared mixtures. Historical `Residual_sharedBallMixture` and `Residual_localMixture` definitions are retained as transparent propositions; they impose no unresolved assumption on `main`.
- `Positivity.lean` — retained unconditional positivity and its geometric helpers.
- `Slots.lean` — retained convex resolution of ball-valued fields.
- `BallPatterns.lean` — retained common current/next field resolution and H1 extension.
- `Audit.lean` — statements and `#print axioms` for all 36 exported theorems, plus an exact closed-type example.

The other exported definitions are `PositiveLetter := Fin 3 × Fin 2`, `positiveLetter (j : PositiveLetter) : IcoLetter := (j.1, j.2, 0)`, and `patternBallFunctional (π : PatternData) (next : Bool) (b : Fin 20 → Vec3) (f : (Plane → Vec3) → ℝ) : ℝ`, the frozen pattern functional with ball fields substituted for its unit fields. The two historical proposition definitions and all theorem statements appear in the actual audit output below.

Validation, all successful:

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC090.Main` — 152.41 s wall time. Lake also built missing compiled modules of the newly imported indexed dependency; the REC090 Main module took 11 s. No Mathlib build or package update was run.
- `PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/REC090/Audit.lean` — 9.14 s wall time. All 36 exported theorems have exactly the permitted axioms `[propext, Classical.choice, Quot.sound]`.
- `PATH="$HOME/.elan/bin:$PATH" lake env lean /tmp/rec090-exact-type.lean` — 9.26 s wall time. Its example is exactly `example : AKLT.Blueprint.Rec.CoveredRatioStatementV2 := AKLT.W.REC090.main`.
- Source scan: all exported theorems have axiom audits; no forbidden proof constructs occur in the delivered Lean files. `git status --short` reports only the assigned untracked `AKLT/W/REC090/` directory; no tracked source file was modified.

Current evidence is in `build-main.log`, `build-main.time`, `declaration-audit.txt`, `declaration-audit.time`, `exact-type-check.log`, `exact-type-check.time`, and `source-audit.txt`. Earlier partial reports and their other artifacts remain as historical records; this report supersedes their status.

Exact-type and dependency audit output:

```text
AKLT.W.REC090.main : AKLT.Blueprint.Rec.CoveredRatioStatementV2
'AKLT.W.REC090.main' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC089.main : AKLT.Blueprint.Rec.LocalMixtureStatementV2
'AKLT.W.REC089.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All exported theorem statements and actual axiom output:

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
AKLT.W.REC090.main : AKLT.Blueprint.Rec.CoveredRatioStatementV2
'AKLT.W.REC090.main' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.coveredRatio_of_localMixture : AKLT.Blueprint.Rec.LocalMixtureStatementV2 →
  AKLT.Blueprint.Rec.CoveredRatioStatementV2
'AKLT.W.REC090.coveredRatio_of_localMixture' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.PositiveLetter : Type
AKLT.W.REC090.positiveLetter (j : AKLT.W.REC090.PositiveLetter) : AKLT.Defs.IcoLetter
def AKLT.W.REC090.Residual_sharedBallMixture : Prop :=
∀ (a : AKLT.Blueprint.Rec.Departure),
  a.D.status a.y = AKLT.Defs.Status.U →
    ∀ (incoming outgoing : AKLT.Defs.Compass),
      a.o = a.y + outgoing.step →
        AKLT.Defs.CoveredDepartureV2 a.D a.y incoming outgoing →
          ∃ k π b weight,
            (∀ (i : Fin k),
                0 ≤ weight i ∧
                  (π i).Covered ∧
                    (∀ (j : Fin 20), AKLT.Defs.normSq (b i j) ≤ 1) ∧
                      ((π i).outgoing = AKLT.Defs.Compass.north ↔ outgoing = incoming)) ∧
              ((a.D.partition a.τ true fun x => 1) =
                  ∑ i, weight i * AKLT.W.REC090.patternBallFunctional (π i) false (b i) fun x => 1) ∧
                ((AKLT.Defs.traceStep a.D a.y a.o).partition a.τ true fun x => 1) =
                  ∑ i, weight i * AKLT.W.REC090.patternBallFunctional (π i) true (b i) fun x => 1
def AKLT.W.REC090.Residual_localMixture : Prop :=
AKLT.Blueprint.Rec.LocalMixtureStatementV2
AKLT.W.REC090.patternBallFunctional (π : AKLT.Defs.PatternData) (next : Bool) (b : Fin 20 → AKLT.Defs.Vec3)
  (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) : ℝ
```

## ORCH-SUMMARY

- Delivered `AKLT.W.REC090.main : AKLT.Blueprint.Rec.CoveredRatioStatementV2`.
- STATUS: PROVED FROM DEPS.
- Direct indexed leaf: `AKLT.W.REC089.main : AKLT.Blueprint.Rec.LocalMixtureStatementV2`.
- Main has no residual parameter; no open obligations remain.
- Retained the earlier positivity, field resolution, H1 averaging, and division proofs.
- Historical residual proposition names remain as transparent helper definitions only.
- Main build, complete exported-theorem axiom audit, and exact closed-type check passed.
- Every exported theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
- Changed source only under `AKLT/W/REC090/`; no frozen statement was edited.
- Dependency compiled modules were rebuilt automatically by Lake; no package update or Mathlib build.
- No mathematical limitations or further orchestrator decisions.
