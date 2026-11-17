module
public import AKLT.Blueprint.Rec.NodesKernel

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC061

private theorem passageFactor_pos_local (b : Bool) : 0 < passageFactor b := by
  cases b <;> norm_num [passageFactor, localThreshold]

private theorem pairCoefficient_nonneg_local {n : ℕ} (w : DirectionWord n)
    (i : Fin n) (p : Finset Plane) : 0 ≤ pairCoefficient w i p := by
  unfold pairCoefficient
  split_ifs <;> cases wordStraight kernelIncoming w i <;>
    norm_num [alphaBound, betaBound, betaPrimeBound]

private theorem pairCoefficient_pos_local {n : ℕ} (w : DirectionWord n)
    (i : Fin n) (p : Finset Plane) : 0 < pairCoefficient w i p := by
  unfold pairCoefficient
  split_ifs <;> cases wordStraight kernelIncoming w i <;>
    norm_num [alphaBound, betaBound, betaPrimeBound]

private theorem responseKappa_nonneg_local {n : ℕ} (X Y : PairType) (s : ℕ)
    (w : DirectionWord n) (i : Fin n) : 0 ≤ responseKappa X Y s w i := by
  unfold responseKappa
  apply Finset.sum_nonneg
  intro p hp
  split_ifs
  · exact pairCoefficient_nonneg_local w i p
  · exact le_rfl

private theorem exposureSum_nonneg_local {n : ℕ} (w : DirectionWord n)
    (r : Fin n → ℚ) (hr : ∀ i, 0 ≤ r i) (l : List (Fin n)) :
    0 ≤ exposureSum w r l := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih =>
      exact mul_nonneg (passageFactor_pos_local _).le (add_nonneg (hr i) ih)

private theorem kernelLengthCoefficient_nonneg_local (X Y : PairType) (s n : ℕ) :
    0 ≤ kernelLengthCoefficient X Y s n := by
  classical
  unfold kernelLengthCoefficient
  apply Finset.sum_nonneg
  intro w hw
  split_ifs
  · apply mul_nonneg
    · apply Finset.prod_nonneg
      intro i hi
      split_ifs <;> norm_num
    · exact exposureSum_nonneg_local w _ (responseKappa_nonneg_local X Y s w) _
  · exact le_rfl

private theorem responsePairs_card_two_local {n : ℕ} (w : DirectionWord n)
    (i : Fin n) (p : Finset Plane) (hp : p ∈ responsePairs w i) : p.card = 2 := by
  simpa [responsePairs] using (Finset.mem_powersetCard.mp hp).2

private theorem pairCoefficient_pos_of_response_local {n : ℕ} (w : DirectionWord n)
    (i : Fin n) (p : Finset Plane) (_hp : p ∈ responsePairs w i) :
    0 < pairCoefficient w i p := pairCoefficient_pos_local w i p

end AKLT.W.REC061

namespace AKLT.W.REC061

theorem main : AKLT.Blueprint.Rec.KernelPositivityStatement := by
  constructor
  · intro n X Y s
    exact kernelLengthCoefficient_nonneg_local X Y s n
  · intro n w i p hp
    exact ⟨responsePairs_card_two_local w i p hp,
      pairCoefficient_pos_of_response_local w i p hp⟩

end AKLT.W.REC061

#print axioms AKLT.W.REC061.main
