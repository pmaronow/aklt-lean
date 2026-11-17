STATUS: PROVED

Files:

- `AKLT/W/REC029/Main.lean`: the exact target theorem and the reused affine-factor identity.
- `AKLT/W/REC029/Algebra.lean`: explicit finite-sum moment formulas, normalizer positivity, and the unit-triple sum-of-squares bound.
- `AKLT/W/REC029/Ball.lean`: antipodal decomposition, preservation under convex mixtures, missing-slot padding, and both U/D mean bounds.
- `AKLT/W/REC029/Realize.lean`: realization of every mean in the closed radius-3/5 ball by three unit U fields.
- `AKLT/W/REC029/Audit.lean`: exact-type example, public declaration checks, and axiom audits of all 37 exported theorems.
- `report.md`, `build.log`, and `audit.log` in `/home/ubuntu/aklt/reports/LW/REC029/`.

The delivered theorem is unconditional:

```lean
theorem AKLT.W.REC029.main : AKLT.Blueprint.Rec.TipReplacementStatement
```

The frozen statement and all existing files outside the assigned task directory are unchanged. The earlier attempt's conditional proof was replaced by an unconditional proof. No residual propositions or unproved dependencies remain.

Proof details:

1. Evaluate the finite icosahedral functional directly. For three arbitrary fields, the U normalizer is `1 + P/3`, and fifteen times the numerator is `V`.
2. For unit triples, prove the normalizer is at least `1/2` and prove the paper's sum-of-squares identity, yielding the radius-3/5 mean bound.
3. Split each ball field into antipodal unit fields. The homogeneous numerator bound is preserved by convex mixtures. Pad absent slots with zero fields. The D law's zero atom contributes only to the denominator, giving the same bound and strict positivity.
4. Use the symmetric triples `(1,0,0)`, `(x,sqrt(1-x²),0)`, `(x,-sqrt(1-x²),0)` for `-1/2 ≤ x ≤ 1`. Their mean is `(f(x),0,0)`, where `f(x)=(2x+1)(x+2)/(5(x²+x+1))`. The denominator is positive, and the endpoint means are zero and `3/5`. The intermediate value theorem supplies the desired length; a Mathlib orthogonal reflection supplies its direction. Covariance is proved from the explicit moment formulas.
5. Apply the affine-factor identity to the original and replacement tips with their common mean. Choose `scale = A'/A`, prove it positive, and cancel the positive original normalizer.

This uses a real algebraic parameter `x` for the paper's trigonometric path. It requires only the frozen definitions, the proofs in this directory, and Mathlib; no other blueprint leaf is used as an assumed lemma.

Public declarations and their statements (complete `#check` output):

```text
AKLT.W.REC029.E3 : Type
AKLT.W.REC029.asE (v : AKLT.Defs.Vec3) : AKLT.W.REC029.E3
AKLT.W.REC029.asE_apply (v : AKLT.Defs.Vec3) (i : Fin 3) : (AKLT.W.REC029.asE v).ofLp i = v i
AKLT.W.REC029.normSq_eq (v : AKLT.Defs.Vec3) : AKLT.Defs.normSq v = ‖AKLT.W.REC029.asE v‖ ^ 2
AKLT.W.REC029.dot_eq (v w : AKLT.Defs.Vec3) : AKLT.Defs.dot v w = inner ℝ (AKLT.W.REC029.asE v) (AKLT.W.REC029.asE w)
AKLT.W.REC029.normSq_nonneg (v : AKLT.Defs.Vec3) : 0 ≤ AKLT.Defs.normSq v
AKLT.W.REC029.dot_comm (v w : AKLT.Defs.Vec3) : AKLT.Defs.dot v w = AKLT.Defs.dot w v
AKLT.W.REC029.normSq_scale (c : ℝ) (v : AKLT.Defs.Vec3) :
  (AKLT.Defs.normSq fun i => c * v i) = c ^ 2 * AKLT.Defs.normSq v
AKLT.W.REC029.dot_le_one {v w : AKLT.Defs.Vec3} (hv : AKLT.Defs.normSq v = 1) (hw : AKLT.Defs.normSq w = 1) :
  AKLT.Defs.dot v w ≤ 1
AKLT.W.REC029.P (a : Fin 3 → AKLT.Defs.Vec3) : ℝ
AKLT.W.REC029.V (a : Fin 3 → AKLT.Defs.Vec3) : AKLT.Defs.Vec3
AKLT.W.REC029.triple_normalizer (a : Fin 3 → AKLT.Defs.Vec3) :
  AKLT.Defs.siteFunctional AKLT.Defs.Status.U (AKLT.Defs.localProduct a) = 1 + AKLT.W.REC029.P a / 3
AKLT.W.REC029.triple_numerator (a : Fin 3 → AKLT.Defs.Vec3) (i : Fin 3) :
  (15 * AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun n => n i * AKLT.Defs.localProduct a n) = AKLT.W.REC029.V a i
AKLT.W.REC029.normSq_combination (a b c : AKLT.Defs.Vec3) (x y z : ℝ) :
  (AKLT.Defs.normSq fun i => x * a i + y * b i + z * c i) =
    x ^ 2 * AKLT.Defs.normSq a + y ^ 2 * AKLT.Defs.normSq b + z ^ 2 * AKLT.Defs.normSq c +
          2 * x * y * AKLT.Defs.dot a b +
        2 * x * z * AKLT.Defs.dot a c +
      2 * y * z * AKLT.Defs.dot b c
AKLT.W.REC029.unit_normalizer_lower (a : Fin 3 → AKLT.Defs.Vec3) (ha : ∀ (j : Fin 3), AKLT.Defs.normSq (a j) = 1) :
  1 / 2 ≤ AKLT.Defs.siteFunctional AKLT.Defs.Status.U (AKLT.Defs.localProduct a)
AKLT.W.REC029.unit_V_bound (a : Fin 3 → AKLT.Defs.Vec3) (ha : ∀ (j : Fin 3), AKLT.Defs.normSq (a j) = 1) :
  AKLT.Defs.normSq (AKLT.W.REC029.V a) ≤ (9 + 3 * AKLT.W.REC029.P a) ^ 2
AKLT.W.REC029.numerator (s : AKLT.Defs.Status) (W : AKLT.Defs.Vec3 → ℝ) : AKLT.Defs.Vec3
AKLT.W.REC029.Good (W : AKLT.Defs.Vec3 → ℝ) : Prop
AKLT.W.REC029.unit_good (a : Fin 3 → AKLT.Defs.Vec3) (ha : ∀ (j : Fin 3), AKLT.Defs.normSq (a j) = 1) :
  AKLT.W.REC029.Good (AKLT.Defs.localProduct a)
AKLT.W.REC029.site_linear (s : AKLT.Defs.Status) (c d : ℝ) (f g : AKLT.Defs.Vec3 → ℝ) :
  (AKLT.Defs.siteFunctional s fun n => c * f n + d * g n) =
    c * AKLT.Defs.siteFunctional s f + d * AKLT.Defs.siteFunctional s g
AKLT.W.REC029.good_mix {f g : AKLT.Defs.Vec3 → ℝ} {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (hf : AKLT.W.REC029.Good f)
  (hg : AKLT.W.REC029.Good g) : AKLT.W.REC029.Good fun n => t * f n + (1 - t) * g n
AKLT.W.REC029.normSq_div (v : AKLT.Defs.Vec3) (c : ℝ) : (AKLT.Defs.normSq fun i => v i / c) = AKLT.Defs.normSq v / c ^ 2
AKLT.W.REC029.axis : AKLT.Defs.UnitVector
AKLT.W.REC029.negUnit (e : AKLT.Defs.UnitVector) : AKLT.Defs.UnitVector
AKLT.W.REC029.ball_split (b : AKLT.Defs.Vec3) (hb : AKLT.Defs.normSq b ≤ 1) :
  ∃ t e,
    0 ≤ t ∧
      t ≤ 1 ∧
        ∀ (n : AKLT.Defs.Vec3),
          1 + AKLT.Defs.dot n b = t * (1 + AKLT.Defs.dot n ↑e) + (1 - t) * (1 + AKLT.Defs.dot n (-↑e))
AKLT.W.REC029.good_slot (F : AKLT.Defs.Vec3 → ℝ) (b : AKLT.Defs.Vec3) (hb : AKLT.Defs.normSq b ≤ 1)
  (h : ∀ (e : AKLT.Defs.UnitVector), AKLT.W.REC029.Good fun n => (1 + AKLT.Defs.dot n ↑e) * F n) :
  AKLT.W.REC029.Good fun n => (1 + AKLT.Defs.dot n b) * F n
AKLT.W.REC029.ball_triple_good (a : Fin 3 → AKLT.Defs.Vec3) (ha : ∀ (j : Fin 3), AKLT.Defs.normSq (a j) ≤ 1) :
  AKLT.W.REC029.Good (AKLT.Defs.localProduct a)
AKLT.W.REC029.ball_good {k : ℕ} (hk : k ≤ 3) (b : Fin k → AKLT.Defs.Vec3)
  (hb : ∀ (j : Fin k), AKLT.Defs.normSq (b j) ≤ 1) : AKLT.W.REC029.Good (AKLT.Defs.localProduct b)
AKLT.W.REC029.U_ball_bound {k : ℕ} (hk : k ≤ 3) (b : Fin k → AKLT.Defs.Vec3)
  (hb : ∀ (j : Fin k), AKLT.Defs.normSq (b j) ≤ 1) :
  0 < AKLT.Defs.siteFunctional AKLT.Defs.Status.U (AKLT.Defs.localProduct b) ∧
    AKLT.Defs.normSq (AKLT.Defs.localMean AKLT.Defs.Status.U b) ≤ (3 / 5) ^ 2
AKLT.W.REC029.site_D (f : AKLT.Defs.Vec3 → ℝ) :
  AKLT.Defs.siteFunctional AKLT.Defs.Status.D f = 3 / 5 * AKLT.Defs.siteFunctional AKLT.Defs.Status.U f + 2 / 5 * f 0
AKLT.W.REC029.D_ball_bound {k : ℕ} (hk : k ≤ 3) (b : Fin k → AKLT.Defs.Vec3)
  (hb : ∀ (j : Fin k), AKLT.Defs.normSq (b j) ≤ 1) :
  0 < AKLT.Defs.siteFunctional AKLT.Defs.Status.D (AKLT.Defs.localProduct b) ∧
    AKLT.Defs.normSq (AKLT.Defs.localMean AKLT.Defs.Status.D b) ≤ (3 / 5) ^ 2
AKLT.W.REC029.tip_mean_bound {k : ℕ} (hk : k ≤ 3) (b : Fin k → AKLT.Defs.Vec3)
  (hb : ∀ (j : Fin k), AKLT.Defs.normSq (b j) ≤ 1) (s : AKLT.Defs.Status)
  (hs : s = AKLT.Defs.Status.U ∨ s = AKLT.Defs.Status.D) :
  0 < AKLT.Defs.siteFunctional s (AKLT.Defs.localProduct b) ∧ AKLT.Defs.normSq (AKLT.Defs.localMean s b) ≤ (3 / 5) ^ 2
AKLT.W.REC029.rotate (R : AKLT.W.REC029.E3 ≃ₗᵢ[ℝ] AKLT.W.REC029.E3) (v : AKLT.Defs.Vec3) : AKLT.Defs.Vec3
AKLT.W.REC029.asE_rotate (R : AKLT.W.REC029.E3 ≃ₗᵢ[ℝ] AKLT.W.REC029.E3) (v : AKLT.Defs.Vec3) :
  AKLT.W.REC029.asE (AKLT.W.REC029.rotate R v) = R (AKLT.W.REC029.asE v)
AKLT.W.REC029.rotate_normSq (R : AKLT.W.REC029.E3 ≃ₗᵢ[ℝ] AKLT.W.REC029.E3) (v : AKLT.Defs.Vec3) :
  AKLT.Defs.normSq (AKLT.W.REC029.rotate R v) = AKLT.Defs.normSq v
AKLT.W.REC029.rotate_dot (R : AKLT.W.REC029.E3 ≃ₗᵢ[ℝ] AKLT.W.REC029.E3) (v w : AKLT.Defs.Vec3) :
  AKLT.Defs.dot (AKLT.W.REC029.rotate R v) (AKLT.W.REC029.rotate R w) = AKLT.Defs.dot v w
AKLT.W.REC029.V_eq_E (a : Fin 3 → AKLT.Defs.Vec3) :
  AKLT.W.REC029.asE (AKLT.W.REC029.V a) =
    (5 + AKLT.Defs.dot (a 1) (a 2)) • AKLT.W.REC029.asE (a 0) +
        (5 + AKLT.Defs.dot (a 0) (a 2)) • AKLT.W.REC029.asE (a 1) +
      (5 + AKLT.Defs.dot (a 0) (a 1)) • AKLT.W.REC029.asE (a 2)
AKLT.W.REC029.mean_eq_E (a : Fin 3 → AKLT.Defs.Vec3) :
  AKLT.W.REC029.asE (AKLT.Defs.localMean AKLT.Defs.Status.U a) =
    (15 * AKLT.Defs.siteFunctional AKLT.Defs.Status.U (AKLT.Defs.localProduct a))⁻¹ •
      AKLT.W.REC029.asE (AKLT.W.REC029.V a)
AKLT.W.REC029.mean_covariance (R : AKLT.W.REC029.E3 ≃ₗᵢ[ℝ] AKLT.W.REC029.E3) (a : Fin 3 → AKLT.Defs.Vec3) :
  AKLT.W.REC029.asE (AKLT.Defs.localMean AKLT.Defs.Status.U fun j => AKLT.W.REC029.rotate R (a j)) =
    R (AKLT.W.REC029.asE (AKLT.Defs.localMean AKLT.Defs.Status.U a))
AKLT.W.REC029.path (x : ℝ) : Fin 3 → AKLT.Defs.Vec3
AKLT.W.REC029.pathMean (x : ℝ) : ℝ
AKLT.W.REC029.path_den_pos (x : ℝ) : 0 < 5 * (x ^ 2 + x + 1)
AKLT.W.REC029.path_unit (x : ℝ) (hx : x ∈ Set.Icc (-1 / 2) 1) (j : Fin 3) :
  AKLT.Defs.normSq (AKLT.W.REC029.path x j) = 1
AKLT.W.REC029.path_mean (x : ℝ) (hx : x ∈ Set.Icc (-1 / 2) 1) :
  AKLT.Defs.localMean AKLT.Defs.Status.U (AKLT.W.REC029.path x) = ![AKLT.W.REC029.pathMean x, 0, 0]
AKLT.W.REC029.pathMean_continuous : Continuous AKLT.W.REC029.pathMean
AKLT.W.REC029.realize_mean (m : AKLT.Defs.Vec3) (hm : AKLT.Defs.normSq m ≤ (3 / 5) ^ 2) :
  ∃ a,
    0 < AKLT.Defs.siteFunctional AKLT.Defs.Status.U (AKLT.Defs.localProduct fun j => ↑(a j)) ∧
      (AKLT.Defs.localMean AKLT.Defs.Status.U fun j => ↑(a j)) = m
AKLT.W.REC029.affineFactor_identity (s : AKLT.Defs.Status) {k : ℕ} (a : Fin k → AKLT.Defs.Vec3) (v : AKLT.Defs.Vec3)
  (hA : AKLT.Defs.siteFunctional s (AKLT.Defs.localProduct a) ≠ 0) :
  (AKLT.Defs.siteFunctional s fun n => (1 + AKLT.Defs.dot n v) * AKLT.Defs.localProduct a n) =
    AKLT.Defs.siteFunctional s (AKLT.Defs.localProduct a) * (1 + AKLT.Defs.dot (AKLT.Defs.localMean s a) v)
AKLT.W.REC029.main : AKLT.Blueprint.Rec.TipReplacementStatement
```

Axiom audit: every exported theorem is checked in `Audit.lean`. Complete `#print axioms` output:

```text
'AKLT.W.REC029.asE_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.normSq_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.dot_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.normSq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.dot_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.normSq_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.dot_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.triple_normalizer' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.triple_numerator' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.normSq_combination' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.unit_normalizer_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.unit_V_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.unit_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.site_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.good_mix' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.normSq_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.ball_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.good_slot' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.ball_triple_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.ball_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.U_ball_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.site_D' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.D_ball_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.tip_mean_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.asE_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.rotate_normSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.rotate_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.V_eq_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.mean_eq_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.mean_covariance' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.path_den_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.path_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.path_mean' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.pathMean_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.realize_mean' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.affineFactor_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC029.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Build commands and timings, using `PATH="$HOME/.elan/bin:$PATH"`:

```text
lake build AKLT.W.REC029.Algebra
  Success; module time 15 s.
lake build AKLT.W.REC029.Ball
  Success; final module time 5.5 s.
/usr/bin/time -f 'ELAPSED %e s' lake build AKLT.W.REC029.Main
  Success; 13.94 s wall; Realize 5.4 s and Main 3.8 s.
/usr/bin/time -f 'ELAPSED %e s' lake build AKLT.W.REC029.Audit
  Success; 11.43 s wall; Audit 5.1 s.
```

`Audit.lean` also compiles the exact-type check:

```lean
example : AKLT.Blueprint.Rec.TipReplacementStatement := AKLT.W.REC029.main
```

The final Main and Audit builds have no warnings or errors. Source scan found none of the prohibited proof constructs. Full final transcripts are in `build.log` and `audit.log`.

Open issues: none.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC029.main : AKLT.Blueprint.Rec.TipReplacementStatement` in `AKLT/W/REC029/Main.lean`.
- Helper modules: `Algebra`, `Ball`, `Realize`; verification module: `Audit`.
- Both earlier residuals are fully proved through `tip_mean_bound` and `realize_mean`.
- No hypotheses, residual statements, or other blueprint leaves are assumed by `main`.
- All 37 exported theorem audits use exactly `[propext, Classical.choice, Quot.sound]`.
- Main build and independent exact-type example compile successfully.
- Mathematical parameterization deviation: use `x` in `[-1/2,1]` instead of the paper's angle.
- Limitations: none. Open declarations: none.
- Orchestrator action: accept the proved leaf and include all helper modules under `AKLT/W/REC029/`.
