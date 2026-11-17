module
public import AKLT.W.REC082.PE.Enumeration
public import AKLT.W.REC082.PE.Normalization
public import AKLT.W.REC082.PE.LocalStep

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC082.PE

private theorem partition_fin_sum {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) {ι : Type*} [Fintype ι]
    (f : ι → (Plane → Vec3) → ℝ) :
    D.partition τ b (fun a => ∑ i, f i a) = ∑ i, D.partition τ b (f i) := by
  classical
  simp only [partition_eq_weighted_sum, Finset.mul_sum]
  exact Finset.sum_comm

private theorem stoppedSum_fin_sum {G : Finset Plane} (D : Network G) (u : Plane)
    (T : Finset Plane) {ι : Type*} [Fintype ι]
    (f : (i : ι) → (n : ℕ) → DirectionWord n → ℝ) :
    stoppedSum D u T (fun n w => ∑ i, f i n w) =
      ∑ i, stoppedSum D u T (fun n w => f i n w) := by
  classical
  unfold stoppedSum
  simp_rw [Finset.sum_comm (s := stoppedNetworkTrails D u T _)]
  exact Finset.sum_comm

private theorem stoppedSum_congr {G : Finset Plane} (D : Network G) (u : Plane)
    (T : Finset Plane) (f g : (n : ℕ) → DirectionWord n → ℝ)
    (h : ∀ n w, f n w = g n w) : stoppedSum D u T f = stoppedSum D u T g := by
  classical
  unfold stoppedSum
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro w hw
  exact h n w

/-- The complete finite unused-bond iteration and trail enumeration for one
unnormalized coordinate numerator, conditional only on the local contraction. -/
theorem coordinate_unnormalized (hStep : LocalPartitionResidual)
    {G : Finset Plane} (τ : PinAssignment G) (D : Network G) (hD : D.Auxiliary)
    (u v : Plane) (hu : D.AdmissibleStart u) (hv : AdmissibleTarget D v)
    (b : Bool) (k : Fin 3) :
    D.partition τ b (fun a => a u k * a v k) =
      stoppedSum D u (insert v (protectedSites G)) fun n w =>
        (traceCoefficient D (wordVertices u w) : ℝ) *
          (traceNetwork D (wordVertices u w)).partition τ b
            (fun a => a (wordVertex u w n) k * a v k) := by
  calc
    _ = branchSum D (insert v (protectedSites G))
        (fun E e => E.partition τ b (fun a => a e k * a v k)) D.bonds.card u :=
      coordinate_eq_branchSum hStep τ b v k D.bonds.card D hD u (Or.inr hu) hv le_rfl
    _ = boundedTrailSum D (insert v (protectedSites G))
        (fun E e => E.partition τ b (fun a => a e k * a v k)) D.bonds.card u :=
      branchSum_eq_boundedTrailSum D hD _ (Finset.subset_insert _ _) _ _ u (Or.inr hu)
    _ = _ := by
      simp only [boundedTrailSum, lengthTerm, stoppedSum, stoppedNetworkTrails,
        Finset.sum_filter]

/-- Scalar products are obtained by summing the three coordinate numerators. -/
theorem pair_unnormalized (hStep : LocalPartitionResidual)
    {G : Finset Plane} (τ : PinAssignment G) (D : Network G) (hD : D.Auxiliary)
    (u v : Plane) (hu : D.AdmissibleStart u) (hv : AdmissibleTarget D v) (b : Bool) :
    D.partition τ b (fun a => dot (a u) (a v)) =
      stoppedSum D u (insert v (protectedSites G)) fun n w =>
        (traceCoefficient D (wordVertices u w) : ℝ) *
          (traceNetwork D (wordVertices u w)).partition τ b
            (fun a => dot (a (wordVertex u w n)) (a v)) := by
  calc
    _ = ∑ k : Fin 3, D.partition τ b (fun a => a u k * a v k) :=
      partition_fin_sum D τ b _
    _ = ∑ k : Fin 3, stoppedSum D u (insert v (protectedSites G)) (fun n w =>
        (traceCoefficient D (wordVertices u w) : ℝ) *
          (traceNetwork D (wordVertices u w)).partition τ b
            (fun a => a (wordVertex u w n) k * a v k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact coordinate_unnormalized hStep τ D hD u v hu hv b k
    _ = stoppedSum D u (insert v (protectedSites G)) (fun n w => ∑ k : Fin 3,
        (traceCoefficient D (wordVertices u w) : ℝ) *
          (traceNetwork D (wordVertices u w)).partition τ b
            (fun a => a (wordVertex u w n) k * a v k)) :=
      (stoppedSum_fin_sum D u _ _).symm
    _ = _ := stoppedSum_congr D u _ _ _ (by
      intro n w
      rw [← Finset.mul_sum, ← partition_fin_sum]
      rfl)

/-- The requested expansion follows from the explicit local, one-step
residual. The global iteration, trail enumeration, and final normalization
are all proved here. No other blueprint leaf is imported as a hypothesis. -/
theorem main_of_localPartitionResidual (hStep : LocalPartitionResidual) :
    AKLT.Blueprint.Rec.PairExpansionStatement := by
  intro G τ D hD u v hu hv huv b
  change D.partition τ b (fun a => dot (a u) (a v)) /
    D.partition τ b (fun _ => 1) = _
  rw [pair_unnormalized hStep τ D hD u v hu hv b]
  classical
  unfold stoppedSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro w hw
  dsimp only
  unfold traceRatio
  rw [mul_assoc, div_mul_eq_mul_div, normalizer_mul_expectation]
  ring

/-- The finite stopped pair-walk expansion. -/
theorem main : AKLT.Blueprint.Rec.PairExpansionStatement :=
  main_of_localPartitionResidual coordinateStep

end AKLT.W.REC082.PE
