STATUS: PARTIAL

The requested closed theorem is not proved. The delivered `AKLT.W.REC090.main` still has one explicit residual parameter:

```lean
AKLT.W.REC090.main :
  AKLT.W.REC090.Residual_sharedBallMixture →
  AKLT.Blueprint.Rec.CoveredRatioStatementV2
```

The earlier positivity residual is completely discharged. The common ball-slot resolution and extension of H1 are also proved. The remaining work is constructing the shared local representation from the actual covered network.

Files:

- `AKLT/W/REC090/Main.lean` — transparent residual, unconditional normalizer positivity, and conditional ratio proof.
- `AKLT/W/REC090/Positivity.lean` — direct positivity for every `Network`, for both pin choices.
- `AKLT/W/REC090/Slots.lean` — one-slot convexity and simultaneous finite slot expansion.
- `AKLT/W/REC090/BallPatterns.lean` — the pattern functional with ball fields, common current/next unit-field resolution, and H1 on ball fields.
- `AKLT/W/REC090/Audit.lean` — checks the statements and prints axioms for all 32 exported theorems.
- Report artifacts: `build-main.log`, `build-audit.log`, `declaration-audit.txt`, `exact-type-check.log`.
- `report.luna.md` is preserved. No frozen source file was edited.

The unconditional theorem `partition_pos` states

```lean
∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (pinned : Bool),
  0 < D.partition τ pinned (fun _ => 1)
```

It needs no auxiliary or admissibility premise. Six icosahedron vertices have positive coordinate sum and are pairwise non-antipodal. Each unit pin excludes at most one of these vertices, while at most four original legs are incident to a site. Choose a positive-mass spin avoiding those pins at every active site. Every internal factor is then strictly positive. Every other summand is nonnegative, so this one summand proves positivity. Consequently `positive_normalizers` proves both current and next normalizers positive without any residual input.

`ball_slot_convexity` treats zero fields explicitly, and `ball_slots_mixture` expands all slots with nonnegative coefficients summing to one. `patternBallFunctional_mixture` proves that one choice of fields and coefficients works for both values of `next` and every observable. Removed slots are handled by setting their spin argument to zero. Thus `h1_ball_pattern_bound` is proved from the statement's own H1 hypothesis, without assuming any other blueprint leaf.

`main` averages this extended H1 inequality with the residual's common nonnegative weights and divides by the proved positive current normalizer. The additional, explicitly conditional theorem

```lean
AKLT.W.REC090.coveredRatio_of_localMixture :
  AKLT.Blueprint.Rec.LocalMixtureStatementV2 →
  AKLT.Blueprint.Rec.CoveredRatioStatementV2
```

shows that the original shared-mixture leaf alone now suffices; the earlier second residual is gone. This does not assert that the shared-mixture leaf is proved.

The sole residual is the following closed, transparent proposition, written here in the same namespace and with `open AKLT.Defs` as in the source:

```lean
def Residual_sharedBallMixture : Prop :=
  ∀ a : AKLT.Blueprint.Rec.Departure, a.D.status a.y = .U →
    ∀ incoming outgoing : Compass, a.o = a.y + outgoing.step →
      AKLT.Defs.CoveredDepartureV2 a.D a.y incoming outgoing →
      ∃ k : ℕ, ∃ π : Fin k → PatternData, ∃ b : Fin k → (Fin 20 → Vec3),
        ∃ weight : Fin k → ℝ,
        (∀ i, 0 ≤ weight i ∧ (π i).Covered ∧
          (∀ j, normSq (b i j) ≤ 1) ∧
          ((π i).outgoing = .north ↔ outgoing = incoming)) ∧
        a.D.partition a.τ true (fun _ => 1) =
          ∑ i, weight i * patternBallFunctional (π i) false (b i) (fun _ => 1) ∧
        (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) =
          ∑ i, weight i * patternBallFunctional (π i) true (b i) (fun _ => 1)
```

What blocks it: formalize the common finite disintegration over outside spins, use the shared present-bond matcher to identify the non-tip factors, and replace the actual U/D/X tips by covering U tips with the same integrated contribution in both networks. In particular the matcher only matches non-tip statuses and internal bond presence; a direct rewrite of the global partition into the frozen pattern partition does not supply these tip identities. The remaining proposition contains no H1 premise or quotient bound. It only asks for the two common finite-sum identities. No counterexample or missing mathematical premise has been established.

Validation:

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC090.Main` — passed; module 3.8 s, measured wall time 9.03 s.
- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC090.Audit` — passed; measured wall time 9.14 s.
- All 32 exported theorems were checked with `#print axioms`; every output is exactly `[propext, Classical.choice, Quot.sound]`.
- A source scan of the delivered Lean files found no forbidden proof constructs.
- The exact closed-type diagnostic was run with `lake env lean /tmp/rec090_exact_check.lean`, whose only declaration after the import was `example : AKLT.Blueprint.Rec.CoveredRatioStatementV2 := AKLT.W.REC090.main`. It failed, as required by the still-conditional type; wall time 3.84 s. This is a known delivery limitation, not a passed check:

```text
/tmp/rec090_exact_check.lean:2:56: error: Type mismatch
  AKLT.W.REC090.main
has type
  AKLT.W.REC090.Residual_sharedBallMixture → AKLT.Blueprint.Rec.CoveredRatioStatementV2
but is expected to have type
  AKLT.Blueprint.Rec.CoveredRatioStatementV2
real 3.84
user 2.71
sys 1.15
```

All exported theorem statements and the actual `#print axioms` output follow. The additional definitions are `PositiveLetter := Fin 3 × Fin 2`, `positiveLetter (j : PositiveLetter) : IcoLetter := (j.1, j.2, 0)`, `patternBallFunctional` (the frozen finite pattern sum with `Vec3` fields), and the residual reproduced above.

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
AKLT.W.REC090.main : AKLT.W.REC090.Residual_sharedBallMixture → AKLT.Blueprint.Rec.CoveredRatioStatementV2
'AKLT.W.REC090.main' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.coveredRatio_of_localMixture : AKLT.Blueprint.Rec.LocalMixtureStatementV2 →
  AKLT.Blueprint.Rec.CoveredRatioStatementV2
'AKLT.W.REC090.coveredRatio_of_localMixture' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC090.Residual_sharedBallMixture : Prop
AKLT.W.REC090.patternBallFunctional (π : AKLT.Defs.PatternData) (next : Bool) (b : Fin 20 → AKLT.Defs.Vec3)
  (f : (AKLT.Defs.Plane → AKLT.Defs.Vec3) → ℝ) : ℝ
```

## ORCH-SUMMARY

- Delivered five compiled Lean files under `AKLT/W/REC090/`.
- STATUS: PARTIAL; the requested unconditional `AKLT.W.REC090.main` is not delivered.
- `main` has exactly one explicit residual: `AKLT.W.REC090.Residual_sharedBallMixture`.
- Open: prove that residual from `Departure` and `AKLT.Defs.CoveredDepartureV2`.
- It requires common finite disintegration and actual-tip replacement; these remain unproved.
- The earlier `Residual_positiveNormalizers` obligation is fully discharged.
- `partition_pos` proves positivity for every network and either pin choice.
- Ball-slot filling, common unit-field mixtures, H1 extension, averaging, and division are proved.
- Alternatively, `coveredRatio_of_localMixture` gives the target from `LocalMixtureStatementV2` alone.
- No other blueprint leaf is assumed proved and no frozen file is changed.
- Main and Audit builds pass; every exported theorem uses only the three permitted axioms.
- Exact closed-type diagnostic still fails because of the one residual parameter.
- Orchestrator must supply/prove the shared representation and then close the exact `main` type.
