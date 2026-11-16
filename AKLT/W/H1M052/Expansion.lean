import AKLT.W.H1M052.Realization

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M052

theorem blochMatrix_smul (a : ℝ) (n : Vec3) :
    blochMatrix (a • n) = (a : ℂ) • blochMatrix n := by
  simp only [blochMatrix, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    Finset.smul_sum, smul_smul]

def summandMatrices (π : PatternData) (r : Representation) (I : Finset (Fin 20))
    (n : Plane → Vec3) : reductionVectors π r → SmallMatrix :=
  fun j => 1 + blochMatrix (inversionSign I j.val • tokenVector π r n j.val)

theorem summand_factor_pair (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (hI : GroupInversion π r I)
    (x : reductionGroups π) (h : groupIsPair π r x.val = true) (n : Plane → Vec3) :
    toEnd (tensorMatrix (reductionVectors π r) (summandMatrices π r I n)) =
      pairTerm (reductionVectors π r) (leaderToken π r x) (secondToken π r x h)
        (inversionSign I (groupLeader x.val)) (n x.val) *
      toEnd (remainingTensor (leaderToken π r x) (secondToken π r x h)
        (summandMatrices π r I n)) := by
  have hs : inversionSign I (groupSecond x.val) = inversionSign I (groupLeader x.val) := by
    simp only [inversionSign, hI.2 x.val x.property h]
  have hj : summandMatrices π r I n (leaderToken π r x) =
      1 + (inversionSign I (groupLeader x.val) : ℂ) • blochMatrix (n x.val) := by
    change 1 + blochMatrix (inversionSign I (groupLeader x.val) •
      tokenVector π r n (groupLeader x.val)) = _
    rw [tokenVector_leader π r n x h, blochMatrix_smul]
  have hk : summandMatrices π r I n (secondToken π r x h) =
      1 + (inversionSign I (groupLeader x.val) : ℂ) • blochMatrix (n x.val) := by
    change 1 + blochMatrix (inversionSign I (groupSecond x.val) •
      tokenVector π r n (groupSecond x.val)) = _
    rw [tokenVector_second π r n x h, hs, blochMatrix_smul]
  have hjk : leaderToken π r x ≠ secondToken π r x h := by
    intro he
    exact group_pair_distinct x.val (congrArg Subtype.val he)
  rw [tensorMatrix_factor_pair _ _ hjk _ _ hj hk, toEnd_mul]
  rfl

/-- Zero coefficients may be padded with a unit spin, then every finite index
type may be enumerated by `Fin`. -/
theorem pairExpansion_of_sum {J : Finset (Fin 20)} (j k : J) (unitOnly : Prop)
    {α : Type*} [Fintype α] (η : ℝ) (hη : η ^ 2 = 1)
    (w : α → ℂ) (n : α → Vec3) (H : α → Module.End ℂ (TensorSpace J))
    (hn : ∀ a, normSq (n a) ≤ 1 ∧ (unitOnly → w a ≠ 0 → normSq (n a) = 1))
    (hH : ∀ a, Commute (H a) (exchangeOperator J j k) ∧
      Commute (H a) (symmetricPairProjection J j k)) :
    PairExpansion J j k (∑ a, w a • (pairTerm J j k η (n a) * H a)) unitOnly := by
  classical
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  let n' : α → Vec3 := fun a => if w a = 0 then ![1, 0, 0] else n a
  have hu : normSq (![1, 0, 0] : Vec3) = 1 := by
    norm_num [normSq, dot, Fin.sum_univ_succ]
  refine ⟨Fintype.card α, η, hη, w ∘ e, n' ∘ e, H ∘ e, ?_, ?_, ?_⟩
  · intro a
    dsimp only [Function.comp_apply]
    dsimp only [n']
    split_ifs with hw
    · exact ⟨hu.le, fun _ => hu⟩
    · exact ⟨(hn (e a)).1, fun h => (hn (e a)).2 h hw⟩
  · intro a
    exact hH (e a)
  · change _ = ∑ a : Fin (Fintype.card α),
      w (e a) • (pairTerm J j k η (n' (e a)) * H (e a))
    rw [e.sum_comp (fun a => w a • (pairTerm J j k η (n' a) * H a))]
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [n']
    by_cases hw : w a = 0
    · simp [hw]
    · simp [hw]

theorem spinVector_norm (hNorm : ∀ j : IcoLetter, normSq (icoVector j) = 1)
    (a : SpinLetter) : normSq (spinVector a) ≤ 1 := by
  cases a with
  | none => norm_num [spinVector, normSq, dot]
  | some a => exact (hNorm a).le

theorem spinVector_unit_of_weight (hNorm : ∀ j : IcoLetter, normSq (icoVector j) = 1)
    (a : SpinLetter) (h : spinWeight .U a ≠ 0) : normSq (spinVector a) = 1 := by
  cases a with
  | none => exact False.elim (h (by simp [spinWeight]))
  | some a => exact hNorm a

end AKLT.W.H1M052
