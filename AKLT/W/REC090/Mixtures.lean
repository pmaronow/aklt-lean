import AKLT.W.REC090.BallPatterns

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC090

private theorem sum_product_fin {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ → ℝ) :
    (∑ i, ∑ j, f i j) =
      ∑ p : Fin (Fintype.card (ι × κ)),
        f ((Fintype.equivFin (ι × κ)).symm p).1
          ((Fintype.equivFin (ι × κ)).symm p).2 := by
  rw [← Fintype.sum_prod_type']
  exact (Equiv.sum_comp (Fintype.equivFin (ι × κ)).symm
    (fun p : ι × κ => f p.1 p.2)).symm

/-- The geometric representation before resolving the ball-valued slots. -/
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

/-- Resolve and flatten all slot choices. The two finite sums use the same
new index, patterns, unit fields, and nonnegative weights. -/
theorem localMixture_of_sharedBallMixture (hMix : Residual_sharedBallMixture) :
    AKLT.Blueprint.Rec.LocalMixtureStatementV2 := by
  classical
  intro a hU incoming outgoing hyo hcov
  obtain ⟨k, π, b, w, hw, hcurrent, hnext⟩ :=
    hMix a hU incoming outgoing hyo hcov
  choose m v hv hvs hrep using
    fun i => patternBallFunctional_mixture (π i) (b i) (hw i).2.2.1
  let I := Fin k × (Fin 20 → Bool)
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hflat (next : Bool) :
      (∑ i : Fin k, w i * patternBallFunctional (π i) next (b i) (fun _ => 1)) =
        ∑ j : Fin (Fintype.card I),
          (w (e j).1 * v (e j).1 (e j).2) *
            patternFunctional (π (e j).1) next (m (e j).1 (e j).2) (fun _ => 1) := by
    calc
      _ = ∑ i : Fin k, ∑ σ : Fin 20 → Bool,
          (w i * v i σ) * patternFunctional (π i) next (m i σ) (fun _ => 1) := by
            simp_rw [hrep, Finset.mul_sum, mul_assoc]
      _ = _ := sum_product_fin (fun i σ =>
        (w i * v i σ) * patternFunctional (π i) next (m i σ) (fun _ => 1))
  refine ⟨Fintype.card I, (fun j => π (e j).1),
    (fun j => m (e j).1 (e j).2), (fun j => w (e j).1 * v (e j).1 (e j).2),
    ?_, hcurrent.trans (hflat false), hnext.trans (hflat true)⟩
  intro j
  exact ⟨mul_nonneg (hw (e j).1).1 (hv (e j).1 (e j).2),
    (hw (e j).1).2.1, (hw (e j).1).2.2.2⟩

/-- Unit fields are already in the closed ball. -/
theorem sharedBallMixture_of_localMixture
    (hMix : AKLT.Blueprint.Rec.LocalMixtureStatementV2) :
    Residual_sharedBallMixture := by
  intro a hU incoming outgoing hyo hcov
  obtain ⟨k, π, m, w, hw, hcurrent, hnext⟩ := hMix a hU incoming outgoing hyo hcov
  refine ⟨k, π, (fun i j => (m i j).val), w, ?_, hcurrent, hnext⟩
  intro i
  exact ⟨(hw i).1, (hw i).2.1, (fun j => (m i j).property.le), (hw i).2.2⟩

/-- The earlier residual is exactly the shared-mixture blueprint leaf. -/
theorem sharedBallMixture_iff_localMixture :
    Residual_sharedBallMixture ↔ AKLT.Blueprint.Rec.LocalMixtureStatementV2 :=
  ⟨localMixture_of_sharedBallMixture, sharedBallMixture_of_localMixture⟩

/-- Transparent alias retained for compatibility with the earlier reduction.
The proposition is now proved by `AKLT.W.REC089.main`. -/
def Residual_localMixture : Prop := AKLT.Blueprint.Rec.LocalMixtureStatementV2

end AKLT.W.REC090
