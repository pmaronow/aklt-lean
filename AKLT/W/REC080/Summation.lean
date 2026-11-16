import AKLT.W.REC080.Basic
import AKLT.Cert.H2.Words

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC080

theorem latticeDist_triangle (x y z : Plane) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  have hx := Int.natAbs_add_le (x.1 - y.1) (y.1 - z.1)
  have hy := Int.natAbs_add_le (x.2 - y.2) (y.2 - z.2)
  have hx' : x.1 - y.1 + (y.1 - z.1) = x.1 - z.1 := by ring
  have hy' : x.2 - y.2 + (y.2 - z.2) = x.2 - z.2 := by ring
  rw [hx'] at hx
  rw [hy'] at hy
  unfold latticeDist
  omega

theorem compass_distance (x : Plane) (d : Compass) : latticeDist x (x + d.step) = 1 := by
  cases d <;> simp [latticeDist, Compass.step]

theorem word_distance_le {n : ℕ} (u : Plane) (w : DirectionWord n)
    (j : ℕ) (hj : j ≤ n) : latticeDist u (wordVertex u w j) ≤ j := by
  induction j with
  | zero => simp [AKLT.Cert.H2.vertex_zero, latticeDist]
  | succ j ih =>
    calc
      latticeDist u (wordVertex u w (j + 1)) ≤
          latticeDist u (wordVertex u w j) +
            latticeDist (wordVertex u w j) (wordVertex u w (j + 1)) :=
        latticeDist_triangle _ _ _
      _ ≤ j + 1 := by
        rw [AKLT.Cert.H2.vertex_succ u w j (by omega), compass_distance]
        exact Nat.add_le_add_right (ih (by omega)) 1

theorem stopped_distance_le {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (w : DirectionWord n) (hw : StoppedNetworkTrail D u (protectedSites G) w) :
    protectedDistance G u ≤ n := by
  have hd : setDistance latticeDist u (↑(protectedSites G) : Set Plane) ≤
      (latticeDist u (wordVertex u w n) : ℕ∞) :=
    iInf_le (fun y : (↑(protectedSites G) : Set Plane) =>
      (latticeDist u y.val : ℕ∞)) ⟨wordVertex u w n, hw.2.2.2⟩
  exact ENat.toNat_le_of_le_natCast
    (hd.trans (by exact_mod_cast word_distance_le u w n le_rfl))

theorem reverse_step (d : Compass) : d.reverse.step = -d.step := by
  cases d <;> rfl

/-- The absent incoming edge forbids the first reversal in the H2 class. -/
theorem stopped_isTrail {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (incoming : Compass) (habs : ¬ D.Present (u - incoming.step) u)
    (w : DirectionWord n) (hw : StoppedNetworkTrail D u (protectedSites G) w) :
    IsTrail u incoming w := by
  refine ⟨hw.1, ?_⟩
  intro i hi he
  have hp := hw.2.1 i
  have h0 : wordVertex u w i.val = u := by rw [hi, AKLT.Cert.H2.vertex_zero]
  have h1 : wordVertex u w (i.val + 1) = u - incoming.step := by
    rw [AKLT.Cert.H2.vertex_succ u w i.val i.isLt, h0]
    have hie : (⟨i.val, i.isLt⟩ : Fin n) = i := rfl
    rw [hie, he, reverse_step, sub_eq_add_neg]
  rw [h0, h1] at hp
  exact habs (present_symm D hp)

theorem trailWeight_nonneg {n : ℕ} (u : Plane) (incoming : Compass) (w : DirectionWord n) :
    0 ≤ (trailWeight u incoming w : ℝ) := by
  exact_mod_cast AKLT.Cert.H2.weight_nonneg u incoming w

theorem exceptionFactor_nonneg : 0 ≤ exceptionFactor := by
  unfold exceptionFactor
  positivity

/-- Sum a common trace majorant by length. This uses only H2 and the
original stopping set, so no geometry of extra removed sites enters the tail. -/
theorem onePointSum_le_of_pointwise
    {CV q : ℝ} (hOpen : OpenTrailBound CV q)
    {G : Finset Plane} (D : Network G) (τ : PinAssignment G) (u : Plane)
    (incoming : Compass) (habs : ¬ D.Present (u - incoming.step) u)
    (hpoint : ∀ n : ℕ, ∀ w : DirectionWord n,
      StoppedNetworkTrail D u (protectedSites G) w →
      (traceCoefficient D (wordVertices u w) : ℝ) *
        max (traceRatio D τ true (wordVertices u w)) (traceRatio D τ false (wordVertices u w)) ≤
          exceptionFactor * (trailWeight u incoming w : ℝ)) :
    onePointSum D τ u ≤ onePointConstant CV q * q^(protectedDistance G u) := by
  classical
  let d := protectedDistance G u
  let L := D.bonds.card + 1
  let F : ℕ → ℝ := fun n =>
    ∑ w ∈ stoppedNetworkTrails D u (protectedSites G) n,
      (traceCoefficient D (wordVertices u w) : ℝ) *
        max (traceRatio D τ true (wordVertices u w)) (traceRatio D τ false (wordVertices u w))
  have hzero (n : ℕ) (hn : n < d) : F n = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    have hstop : StoppedNetworkTrail D u (protectedSites G) w :=
      (Finset.mem_filter.mp hw).2
    have := stopped_distance_le D u w hstop
    exact False.elim (Nat.not_le_of_gt hn this)
  have hlen (n : ℕ) : F n ≤ exceptionFactor * CV * q^n := by
    calc
      F n ≤ ∑ w ∈ stoppedNetworkTrails D u (protectedSites G) n,
          exceptionFactor * (trailWeight u incoming w : ℝ) := by
        apply Finset.sum_le_sum
        intro w hw
        exact hpoint n w (Finset.mem_filter.mp hw).2
      _ = exceptionFactor * ∑ w ∈ stoppedNetworkTrails D u (protectedSites G) n,
          (trailWeight u incoming w : ℝ) := by rw [Finset.mul_sum]
      _ ≤ exceptionFactor *
          ∑ w : DirectionWord n, if IsTrail u incoming w then (trailWeight u incoming w : ℝ) else 0 := by
        apply mul_le_mul_of_nonneg_left _ exceptionFactor_nonneg
        calc
          _ = ∑ w ∈ stoppedNetworkTrails D u (protectedSites G) n,
              if IsTrail u incoming w then (trailWeight u incoming w : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [ite_eq_left (stopped_isTrail D u incoming habs w (Finset.mem_filter.mp hw).2)]
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun w _ _ => by
              split_ifs
              · exact trailWeight_nonneg u incoming w
              · exact le_rfl)
      _ ≤ exceptionFactor * (CV * q^n) :=
        mul_le_mul_of_nonneg_left (hOpen.2.2.2 n u incoming) exceptionFactor_nonneg
      _ = _ := by ring
  have hcut : (∑ n ∈ Finset.range L, F n) = ∑ n ∈ Finset.Ico d L, F n := by
    symm
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
    · intro n hn hn'
      apply hzero
      have hlt := Finset.mem_range.mp hn
      simpa only [Finset.mem_Ico, hlt, and_true, not_le] using hn'
  change (∑ n ∈ Finset.range L, F n) ≤ _
  rw [hcut]
  calc
    (∑ n ∈ Finset.Ico d L, F n) ≤ ∑ n ∈ Finset.Ico d L, exceptionFactor * CV * q^n :=
      Finset.sum_le_sum fun n _ => hlen n
    _ = (exceptionFactor * CV) * ∑ n ∈ Finset.Ico d L, q^n := by rw [Finset.mul_sum]
    _ ≤ (exceptionFactor * CV) * (q^d / (1 - q)) := by
      exact mul_le_mul_of_nonneg_left
        (geom_sum_Ico_le_of_lt_one (le_of_lt hOpen.2.1) hOpen.2.2.1)
        (mul_nonneg exceptionFactor_nonneg (le_trans (by norm_num) hOpen.1))
    _ = onePointConstant CV q * q^(protectedDistance G u) := by
      dsimp [onePointConstant, d]
      ring

end AKLT.W.REC080
