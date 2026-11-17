module
public import AKLT.Blueprint.H3.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.H3

theorem passageFactor_pos (b : Bool) : 0 < passageFactor b := by
  cases b <;> norm_num [passageFactor, localThreshold]

theorem kernelRho_pos_lt_one : 0 < kernelRho ∧ kernelRho < 1 := by
  norm_num [kernelRho]

theorem kernelWitness_pos (X : PairType) : 0 < kernelWitness X := by
  cases X <;> norm_num [kernelWitness]

theorem pairCoefficient_nonneg {n : ℕ} (w : DirectionWord n) (i : Fin n) (p : Finset Plane) :
    0 ≤ pairCoefficient w i p := by
  unfold pairCoefficient
  split_ifs <;> cases wordStraight kernelIncoming w i <;>
    norm_num [alphaBound, betaBound, betaPrimeBound]

theorem witnessKappa_nonneg {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    0 ≤ witnessKappa w i := by
  unfold witnessKappa
  exact Finset.sum_nonneg fun p _ => mul_nonneg (pairCoefficient_nonneg w i p)
    (kernelWitness_pos _).le

theorem relaxedReward_nonneg (x : Plane) (incoming outgoing : Compass) (dead : Finset Plane) :
    0 ≤ relaxedReward x incoming outgoing dead := by
  unfold relaxedReward
  apply Finset.sum_nonneg
  intro p _
  apply mul_nonneg _ (kernelWitness_pos _).le
  split_ifs <;> cases decide (outgoing = incoming) <;>
    norm_num [alphaBound, betaBound, betaPrimeBound]

theorem phaseTransition_nonneg (k : StepKind) (r : ℚ) (hr : 0 ≤ r) (φ ψ : Phase) :
    0 ≤ phaseTransition k r φ ψ := by
  cases k <;> cases φ <;> cases ψ <;>
    simp [phaseTransition, phaseDiagonal, passageFactor, localThreshold] <;> positivity

theorem truePhaseCoefficient_nonneg {n : ℕ} (w : DirectionWord n) (i : Fin n) (φ ψ : Phase) :
    0 ≤ truePhaseCoefficient w i φ ψ :=
  phaseTransition_nonneg _ _ (witnessKappa_nonneg w i) φ ψ

theorem stationaryCoefficient_nonneg {m q : ℕ} (Q : MemoryQuotient m q)
    (X : PairType) (d₀ : Compass) (φ : Phase) (a : Fin q) (x : Plane) (d : Compass) (ψ : Phase) :
    0 ≤ stationaryCoefficient Q X d₀ φ a x d ψ := by
  unfold stationaryCoefficient
  split_ifs <;> try norm_num
  exact phaseTransition_nonneg _ _ (relaxedReward_nonneg _ _ _ _) _ _

theorem freeCoefficient_nonneg {m q : ℕ} (Q : MemoryQuotient m q)
    (φ : Phase) (a : Fin q) (d : Compass) (ψ : Phase) : 0 ≤ freeCoefficient Q φ a d ψ := by
  unfold freeCoefficient
  split_ifs
  · exact phaseTransition_nonneg _ _ (relaxedReward_nonneg _ _ _ _) _ _
  · exact le_rfl

theorem prefixPhases_nonneg {n : ℕ} (w : DirectionWord n) (φ : Phase) : 0 ≤ prefixPhases w φ := by
  have hp : ∀ (l : List (Fin n)) (p : Phase → ℚ), (∀ ψ, 0 ≤ p ψ) →
      ∀ ψ, 0 ≤ phaseRun (fun i => truePhaseCoefficient w i) l p ψ := by
    intro l
    induction l with
    | nil => intro p hp ψ; exact hp ψ
    | cons i l ih =>
      intro p hp ψ
      apply ih _ _ ψ
      intro χ
      exact Finset.sum_nonneg fun η _ =>
        mul_nonneg (hp η) (truePhaseCoefficient_nonneg w i η χ)
  apply hp (List.finRange n) phaseInitial _ φ
  intro ψ
  cases ψ <;> norm_num [phaseInitial]

theorem exposureSum_nonneg {n : ℕ} (w : DirectionWord n) (r : Fin n → ℚ)
    (hr : ∀ i, 0 ≤ r i) (l : List (Fin n)) : 0 ≤ exposureSum w r l := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih =>
    exact mul_nonneg (passageFactor_pos _).le (add_nonneg (hr i) ih)

theorem closedContribution_nonneg {n : ℕ} (w : DirectionWord n) : 0 ≤ closedContribution w := by
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro i _
    split_ifs <;> norm_num
  · exact exposureSum_nonneg w _ (witnessKappa_nonneg w) _

theorem responseKappa_nonneg {n : ℕ} (X Y : PairType) (s : ℕ) (w : DirectionWord n) (i : Fin n) :
    0 ≤ responseKappa X Y s w i := by
  unfold responseKappa
  apply Finset.sum_nonneg
  intro p _
  split_ifs
  · exact pairCoefficient_nonneg _ _ _
  · exact le_rfl

theorem kernelLengthCoefficient_nonneg (X Y : PairType) (s n : ℕ) :
    0 ≤ kernelLengthCoefficient X Y s n := by
  classical
  unfold kernelLengthCoefficient
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · apply mul_nonneg
    · apply Finset.prod_nonneg
      intro i _
      split_ifs <;> norm_num
    · exact exposureSum_nonneg w _ (responseKappa_nonneg X Y s w) _
  · exact le_rfl

theorem kernelLengthRow_nonneg (X : PairType) (n : ℕ) : 0 ≤ kernelLengthRow X n := by
  classical
  unfold kernelLengthRow
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · exact closedContribution_nonneg w
  · exact le_rfl

theorem stationaryWordValue_nonneg (Q : MemoryQuotient 10 3741) (X : PairType) (d₀ : Compass)
    (l : List Compass) (φ : Phase) (a : Fin 3741) (x : Plane) :
    0 ≤ stationaryWordValue Q X d₀ l φ a x := by
  induction l generalizing φ a x with
  | nil => unfold stationaryWordValue stationaryReward; split_ifs <;> cases φ <;> norm_num [phaseTerminal]
  | cons d l ih =>
    exact Finset.sum_nonneg fun ψ _ =>
      mul_nonneg (stationaryCoefficient_nonneg _ _ _ _ _ _ _ _) (ih _ _ _)

end AKLT.Blueprint.H3
