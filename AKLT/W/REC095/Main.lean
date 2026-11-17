module
public import AKLT.Blueprint.Rec.NodesV2Walk
public import AKLT.W.REC095.Local
public import AKLT.W.REC094.Main
public import AKLT.Cert.H2.Main
public import Mathlib.Algebra.Field.GeomSum

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC095

/-! Finite grouping and the geometric tail for the one-point estimate.
The proved pointwise leaf REC094 supplies the shared-cover comparison. -/

/-- The pointwise comparison needed before summing a stopped trail. -/
def Residual_OnePointPointwise : Prop :=
  AKLT.Blueprint.Rec.OnePointPointwiseStatementV2

/-- A stopped network trail is an open lattice trail and its length reaches
the protected distance.  The initial reversal clause uses the absent incoming
bond from the one-point statement. -/
def Residual_StoppedTrailGeometry : Prop :=
  ∀ G : Finset Plane, ∀ D : Network G, ∀ u : Plane, ∀ incoming : Compass,
    ¬ D.Present (u - incoming.step) u →
    ∀ n : ℕ, ∀ w : DirectionWord n,
      StoppedNetworkTrail D u (protectedSites G) w →
        IsTrail u incoming w ∧ AKLT.Blueprint.Rec.protectedDistance G u ≤ n

private theorem trailWeight_nonneg {n : ℕ} (u : Plane) (incoming : Compass)
    (w : DirectionWord n) : 0 ≤ (trailWeight u incoming w : ℝ) := by
  have hq : 0 ≤ trailWeight u incoming w := by
    unfold trailWeight
    apply Finset.prod_nonneg
    intro i hi
    by_cases hr : wordRevisit u w i = true
    · simp [hr]
    · have hrf : wordRevisit u w i = false := Bool.eq_false_of_not_eq_true hr
      rw [hrf]
      cases hs : wordStraight incoming w i <;>
        norm_num [passageFactor, localThreshold, hs]
  exact_mod_cast hq

private theorem protectedLength_bound {n : ℕ} {G : Finset Plane} {D : Network G}
    {u : Plane} {incoming : Compass} {w : DirectionWord n}
    (hgeo : Residual_StoppedTrailGeometry)
    (hmiss : ¬ D.Present (u - incoming.step) u)
    (hstop : StoppedNetworkTrail D u (protectedSites G) w) :
    AKLT.Blueprint.Rec.protectedDistance G u ≤ n :=
  (hgeo G D u incoming hmiss n w hstop).2

private theorem openTrail_bound {G : Finset Plane} {D : Network G} {u : Plane}
    {incoming : Compass} {n : ℕ} {w : DirectionWord n}
    (hgeo : Residual_StoppedTrailGeometry)
    (hmiss : ¬ D.Present (u - incoming.step) u)
    (hstop : StoppedNetworkTrail D u (protectedSites G) w) :
    IsTrail u incoming w :=
  (hgeo G D u incoming hmiss n w hstop).1

private theorem adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  have h₁ : y.1 - x.1 = -(x.1 - y.1) := by omega
  have h₂ : y.2 - x.2 = -(x.2 - y.2) := by omega
  unfold Adjacent at *
  change (y.1 - x.1).natAbs + (y.2 - x.2).natAbs = 1
  rw [h₁, h₂, Int.natAbs_neg, Int.natAbs_neg]
  exact h

private theorem present_symm {G : Finset Plane} (D : Network G) {x y : Plane}
    (h : D.Present x y) : D.Present y x := by
  rcases h with ⟨hx, hy, hadj, hxy, hyx⟩
  exact ⟨hy, hx, adjacent_symm hadj, hyx, hxy⟩

private theorem latticeDist_vertex_le {n : ℕ} (u : Plane) (w : DirectionWord n) :
    latticeDist u (wordVertex u w n) ≤ n := by
  have hv : wordVertex u w n = u + ∑ i : Fin n, (w i).step := by
    simp only [wordVertex]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp [i.isLt]
  have hfst : (∑ i : Fin n, (w i).step).1 = ∑ i : Fin n, (w i).step.1 := by
    simpa using (Prod.fst_sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => (w i).step))
  have hsnd : (∑ i : Fin n, (w i).step).2 = ∑ i : Fin n, (w i).step.2 := by
    simpa using (Prod.snd_sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => (w i).step))
  have hx :
      (u.1 - (wordVertex u w n).1) = -(∑ i : Fin n, (w i).step.1) := by
    rw [hv]
    rw [Prod.fst_add, hfst]
    ring
  have hy :
      (u.2 - (wordVertex u w n).2) = -(∑ i : Fin n, (w i).step.2) := by
    rw [hv]
    rw [Prod.snd_add, hsnd]
    ring
  have hsteps :
      (∑ i : Fin n, Int.natAbs (w i).step.1) +
        ∑ i : Fin n, Int.natAbs (w i).step.2 = n := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ i : Fin n, (Int.natAbs (w i).step.1 + Int.natAbs (w i).step.2)) =
          ∑ _i : Fin n, 1 := by
        apply Finset.sum_congr rfl
        intro i hi
        cases w i <;> norm_num [Compass.step]
      _ = n := by simp
  calc
    latticeDist u (wordVertex u w n) =
        Int.natAbs (∑ i : Fin n, (w i).step.1) +
          Int.natAbs (∑ i : Fin n, (w i).step.2) := by
      simp [latticeDist, hx, hy, Int.natAbs_neg]
    _ ≤ (∑ i : Fin n, Int.natAbs (w i).step.1) +
        ∑ i : Fin n, Int.natAbs (w i).step.2 := by
      have h₁ := Int.natAbs_sum_le (Finset.univ : Finset (Fin n))
        (fun i => (w i).step.1)
      have h₂ := Int.natAbs_sum_le (Finset.univ : Finset (Fin n))
        (fun i => (w i).step.2)
      exact Nat.add_le_add h₁ h₂
    _ = n := hsteps

theorem stoppedTrailGeometry : Residual_StoppedTrailGeometry := by
  intro G D u incoming hmiss n w hstop
  refine ⟨?_, ?_⟩
  · refine ⟨hstop.1, ?_⟩
    intro i hi heq
    have hi0 : i = ⟨0, by omega⟩ := Fin.ext hi
    rw [hi0] at heq
    have hzero : wordVertex u w 0 = u := AKLT.Cert.H2.vertex_zero u w
    have hone : wordVertex u w 1 = u + (w ⟨0, by omega⟩).step := by
      simpa [AKLT.Cert.H2.vertex_zero] using
        AKLT.Cert.H2.vertex_succ u w 0 (by omega)
    have hstep : (w ⟨0, by omega⟩).step = -incoming.step := by
      rw [heq]
      cases incoming <;> rfl
    have hp : D.Present u (u - incoming.step) := by
      simpa [hzero, hone, hstep, sub_eq_add_neg] using
        hstop.2.1 ⟨0, by omega⟩
    exact hmiss (present_symm D hp)
  · have hterminal := hstop.2.2.2
    have hdist :
        setDistance latticeDist u (↑(protectedSites G) : Set Plane) ≤
          (latticeDist u (wordVertex u w n) : ℕ∞) := by
      rw [setDistance]
      exact iInf_le (fun z : ↑(protectedSites G) =>
        (latticeDist u z.val : ℕ∞)) ⟨wordVertex u w n, hterminal⟩
    have hpath := latticeDist_vertex_le u w
    have hnat :
        setDistance latticeDist u (↑(protectedSites G) : Set Plane) ≤ n :=
      hdist.trans (Nat.cast_le.mpr hpath)
    simpa [AKLT.Blueprint.Rec.protectedDistance] using
      ENat.toNat_le_of_le_natCast hnat

private theorem finite_geometric_tail {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (d N : ℕ) :
    (∑ n ∈ Finset.Ico d N, q ^ n) ≤ q ^ d / (1 - q) := by
  by_cases hdN : d ≤ N
  · rw [Finset.sum_Ico_eq_sum_range]
    have hgeom := geom_sum_eq (x := q) (by linarith) (N - d)
    simp_rw [pow_add]
    rw [← Finset.mul_sum]
    rw [hgeom]
    have hpow : 0 ≤ q ^ (N - d) := pow_nonneg hq0.le _
    have hden : 0 < 1 - q := sub_pos.mpr hq1
    have hqd : 0 ≤ q ^ d := pow_nonneg hq0.le _
    have hfrac : (q ^ (N - d) - 1) / (q - 1) =
        (1 - q ^ (N - d)) / (1 - q) := by
      rw [div_eq_div_iff (sub_ne_zero.mpr (ne_of_lt hq1)) hden.ne']
      ring
    rw [hfrac]
    apply mul_le_mul_of_nonneg_left _ hqd
    have hnum : 1 - q ^ (N - d) ≤ 1 := by linarith [hpow]
    calc
      (1 - q ^ (N - d)) / (1 - q) ≤ 1 / (1 - q) :=
        div_le_div_of_nonneg_right hnum hden.le
      _ = (1 - q)⁻¹ := by rw [one_div]
  · have hEq : Finset.Ico d N = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    simp [hEq, div_nonneg (pow_nonneg hq0.le _) (sub_nonneg.mpr hq1.le)]

/-- The finite grouping and geometric tail argument, conditional on the two
explicit residual facts. -/
theorem main_of_residuals (hpoint : Residual_OnePointPointwise)
    (hgeo : Residual_StoppedTrailGeometry) :
    AKLT.Blueprint.Rec.OnePointSumStatementV2 := by
  intro hH1 CV q hOpen G τ D hD u hu incoming hmiss hex
  rcases hOpen with ⟨hCV, hq0, hq1, hlength⟩
  have hfactor : 0 ≤ AKLT.Blueprint.Rec.exceptionFactor := by
    unfold AKLT.Blueprint.Rec.exceptionFactor
    positivity
  have hCV0 : 0 ≤ CV := le_trans (by norm_num) hCV
  let d := AKLT.Blueprint.Rec.protectedDistance G u
  let N := D.bonds.card + 1
  have hinner : ∀ n : ℕ,
      (∑ w ∈ AKLT.Defs.stoppedNetworkTrails D u (protectedSites G) n,
        (AKLT.Defs.traceCoefficient D (AKLT.Defs.wordVertices u w) : ℝ) *
          max (AKLT.Defs.traceRatio D τ true (AKLT.Defs.wordVertices u w))
            (AKLT.Defs.traceRatio D τ false (AKLT.Defs.wordVertices u w))) ≤
        AKLT.Blueprint.Rec.exceptionFactor * CV * q ^ n := by
    intro n
    classical
    rw [AKLT.Defs.stoppedNetworkTrails, Finset.sum_filter]
    calc
      (∑ w : DirectionWord n,
          if StoppedNetworkTrail D u (protectedSites G) w then
            (AKLT.Defs.traceCoefficient D (AKLT.Defs.wordVertices u w) : ℝ) *
              max (AKLT.Defs.traceRatio D τ true (AKLT.Defs.wordVertices u w))
                (AKLT.Defs.traceRatio D τ false (AKLT.Defs.wordVertices u w))
          else 0) ≤
        ∑ w : DirectionWord n,
          AKLT.Blueprint.Rec.exceptionFactor *
            (if IsTrail u incoming w then (trailWeight u incoming w : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro w hw
        by_cases hs : StoppedNetworkTrail D u (protectedSites G) w
        · have hc := hpoint hH1 G τ D hD u hu incoming hmiss n w hs (hex n w hs)
          have ht := openTrail_bound hgeo hmiss hs
          simp only [hs, ht, ite_true]
          exact hc
        · have ht : 0 ≤ AKLT.Blueprint.Rec.exceptionFactor *
              (if IsTrail u incoming w then (trailWeight u incoming w : ℝ) else 0) := by
            split_ifs
            · exact mul_nonneg hfactor (trailWeight_nonneg u incoming w)
            · exact mul_nonneg hfactor (by norm_num)
          simpa [hs] using ht
      _ = AKLT.Blueprint.Rec.exceptionFactor *
          ∑ w : DirectionWord n,
            if IsTrail u incoming w then (trailWeight u incoming w : ℝ) else 0 := by
        rw [Finset.mul_sum]
      _ ≤ AKLT.Blueprint.Rec.exceptionFactor * (CV * q ^ n) := by
        apply mul_le_mul_of_nonneg_left (hlength n u incoming) hfactor
      _ = _ := by ring
  have hsum :
      AKLT.Blueprint.Rec.onePointSum D τ u ≤
        AKLT.Blueprint.Rec.exceptionFactor * CV *
          ∑ n ∈ Finset.Ico d N, q ^ n := by
    classical
    unfold AKLT.Blueprint.Rec.onePointSum AKLT.Blueprint.Rec.stoppedSum
    dsimp [N, d]
    calc
      (∑ n ∈ Finset.range (D.bonds.card + 1),
          ∑ w ∈ AKLT.Defs.stoppedNetworkTrails D u (protectedSites G) n,
            (AKLT.Defs.traceCoefficient D (AKLT.Defs.wordVertices u w) : ℝ) *
              max (AKLT.Defs.traceRatio D τ true (AKLT.Defs.wordVertices u w))
                (AKLT.Defs.traceRatio D τ false (AKLT.Defs.wordVertices u w))) ≤
        ∑ n ∈ Finset.range (D.bonds.card + 1),
          if d ≤ n then AKLT.Blueprint.Rec.exceptionFactor * CV * q ^ n else 0 :=
        Finset.sum_le_sum fun n hn => by
          by_cases hd : d ≤ n
          · simp [hd, hinner n]
          · have hempty :
                AKLT.Defs.stoppedNetworkTrails D u (protectedSites G) n = ∅ := by
              apply Finset.not_nonempty_iff_eq_empty.mp
              intro hne
              obtain ⟨w, hw⟩ := hne
              have hs : StoppedNetworkTrail D u (protectedSites G) w :=
                (Finset.mem_filter.mp hw).2
              have hdn := protectedLength_bound hgeo hmiss hs
              omega
            simp [hd, hempty]
      _ = ∑ n ∈ Finset.Ico d (D.bonds.card + 1),
          AKLT.Blueprint.Rec.exceptionFactor * CV * q ^ n := by
        rw [← Finset.sum_filter]
        congr 1
        ext n
        simp [Finset.mem_Ico, Finset.mem_range, and_comm]
      _ = AKLT.Blueprint.Rec.exceptionFactor * CV *
          ∑ n ∈ Finset.Ico d (D.bonds.card + 1), q ^ n := by
        rw [Finset.mul_sum]
  have htail := finite_geometric_tail hq0 hq1 d N
  have hscale : 0 ≤ AKLT.Blueprint.Rec.exceptionFactor * CV :=
    mul_nonneg hfactor hCV0
  calc
    AKLT.Blueprint.Rec.onePointSum D τ u ≤
        AKLT.Blueprint.Rec.exceptionFactor * CV *
          ∑ n ∈ Finset.Ico d N, q ^ n := hsum
    _ ≤ AKLT.Blueprint.Rec.exceptionFactor * CV * (q ^ d / (1 - q)) :=
      mul_le_mul_of_nonneg_left htail hscale
    _ = AKLT.Blueprint.Rec.onePointConstant CV q * q ^ d := by
      unfold AKLT.Blueprint.Rec.onePointConstant AKLT.Blueprint.Rec.exceptionFactor
      ring

/-- Sum any shared-cover pointwise estimate using the proved trail geometry. -/
theorem main_of_pointwise (hpoint : Residual_OnePointPointwise) :
    AKLT.Blueprint.Rec.OnePointSumStatementV2 :=
  main_of_residuals hpoint stoppedTrailGeometry

/-- The local shared-cover ratio comparison also suffices. -/
theorem main_of_coveredRatio (hcovered : Residual_CoveredRatio) :
    AKLT.Blueprint.Rec.OnePointSumStatementV2 :=
  main_of_pointwise (pointwise_of_coveredRatio hcovered)

/-- The stronger local mixture leaf (REC089) is also sufficient. -/
theorem main_of_localMixture (hmixture : AKLT.Blueprint.Rec.LocalMixtureStatementV2) :
    AKLT.Blueprint.Rec.OnePointSumStatementV2 :=
  main_of_coveredRatio (coveredRatio_of_localMixture hmixture)

/-- `l:onepoint`: apply the proved pointwise comparison with the identical
incoming direction, then group by length and bound the geometric tail. -/
theorem main : AKLT.Blueprint.Rec.OnePointSumStatementV2 :=
  main_of_pointwise AKLT.W.REC094.main

end AKLT.W.REC095

end
