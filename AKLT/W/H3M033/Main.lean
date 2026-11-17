module
public import AKLT.Blueprint.H3.NodesV2Stationary

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H3M033

lemma stationaryReward_center_zero (X : PairType) (φ : Phase) (a : Fin 3741) :
    stationaryReward X φ a kernelCenter = 0 := by
  cases X <;> simp [stationaryReward, kernelCenter, kernelTarget]

lemma stationaryApplyV2_center_zero
    (Q : MemoryQuotient 10 3741) (X : PairType) (d₀ : Compass)
    (F : Phase → Fin 3741 → Plane → ℚ) (φ : Phase) (a : Fin 3741) :
    stationaryApplyV2 Q X d₀ F φ a kernelCenter = 0 := by
  simp [stationaryApplyV2, stationaryCoefficientV2, kernelCenter]

lemma stationaryApply_center_zero
    (Q : MemoryQuotient 10 3741) (X : PairType) (d₀ : Compass)
    (F : Phase → Fin 3741 → Plane → ℚ) (φ : Phase) (a : Fin 3741) :
    stationaryApply Q X d₀ F φ a kernelCenter = 0 := by
  simp [stationaryApply, stationaryCoefficient, kernelCenter]

lemma stationaryCoefficient_eq_of_destination_ne_center
    (Q : MemoryQuotient 10 3741) (X : PairType) (d₀ : Compass)
    (φ : Phase) (a : Fin 3741) (x : Plane) (d : Compass) (ψ : Phase)
    (h : x + d.step ≠ kernelCenter) :
    stationaryCoefficientV2 Q X d₀ φ a x d ψ =
      stationaryCoefficient Q X d₀ φ a x d ψ := by
  simp [stationaryCoefficientV2, stationaryCoefficient, h]

lemma stationaryApplyV2_eq_of_center_zero
    (Q : MemoryQuotient 10 3741) (X : PairType) (d₀ : Compass)
    (F : Phase → Fin 3741 → Plane → ℚ)
    (hF : ∀ φ a, F φ a kernelCenter = 0)
    (φ : Phase) (a : Fin 3741) (x : Plane) :
    stationaryApplyV2 Q X d₀ F φ a x = stationaryApply Q X d₀ F φ a x := by
  unfold stationaryApplyV2 stationaryApply
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro ψ hψ
  by_cases hdest : x + d.step = kernelCenter
  · simp [hdest, hF]
  · rw [stationaryCoefficient_eq_of_destination_ne_center Q X d₀ φ a x d ψ hdest]

lemma stationaryContinuation_iterates_joint
    (Q : MemoryQuotient 10 3741) (X : PairType) (d₀ : Compass) :
    ∀ j : ℕ,
      (∀ φ a, ((stationaryApplyV2 Q X d₀)^[j]) (stationaryReward X) φ a kernelCenter = 0) ∧
      (∀ φ a, ((stationaryApply Q X d₀)^[j]) (stationaryReward X) φ a kernelCenter = 0) ∧
      (∀ φ a x, ((stationaryApplyV2 Q X d₀)^[j]) (stationaryReward X) φ a x =
        ((stationaryApply Q X d₀)^[j]) (stationaryReward X) φ a x) := by
  intro j
  induction j with
  | zero =>
      constructor
      · intro φ a
        exact stationaryReward_center_zero X φ a
      constructor
      · intro φ a
        exact stationaryReward_center_zero X φ a
      · intro φ a x
        rfl
  | succ j ih =>
      rcases ih with ⟨hV2center, hLegacycenter, hEq⟩
      constructor
      · intro φ a
        simpa only [Function.iterate_succ_apply'] using
          (stationaryApplyV2_center_zero Q X d₀
            (((stationaryApplyV2 Q X d₀)^[j]) (stationaryReward X)) φ a)
      constructor
      · intro φ a
        simpa only [Function.iterate_succ_apply'] using
          (stationaryApply_center_zero Q X d₀
            (((stationaryApply Q X d₀)^[j]) (stationaryReward X)) φ a)
      · intro φ a x
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        have hfun : ((stationaryApplyV2 Q X d₀)^[j]) (stationaryReward X) =
            ((stationaryApply Q X d₀)^[j]) (stationaryReward X) := by
          funext ψ b y
          exact hEq ψ b y
        rw [hfun]
        exact stationaryApplyV2_eq_of_center_zero Q X d₀
          (((stationaryApply Q X d₀)^[j]) (stationaryReward X)) hLegacycenter φ a x

end AKLT.W.H3M033

namespace AKLT.W.H3M033

theorem main : AKLT.Blueprint.H3.StationaryContinuationBridgeStatementV2 := by
  intro Q X d₀ φ a x R
  unfold stationaryContinuationSumV2 stationaryContinuationSum
  apply Finset.sum_congr rfl
  intro j hj
  exact (stationaryContinuation_iterates_joint Q X d₀ j).2.2 φ a x

end AKLT.W.H3M033
