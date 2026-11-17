module
public import AKLT.Blueprint.H3.NodesPhase

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H3M003

private theorem phase_univ : (Finset.univ : Finset Phase) =
    {Phase.A, Phase.B, Phase.C, Phase.D} := by decide

private theorem phase_sum (f : Phase → ℚ) :
    (∑ φ : Phase, f φ) = f .A + f .B + f .C + f .D := by
  rw [phase_univ]
  simp
  ring

private theorem finRange_castSucc_append (n : ℕ) :
    List.finRange (n + 1) = (List.finRange n).map Fin.castSucc ++ [Fin.last n] := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    apply Fin.ext
    by_cases h : i < n
    · simp [h, List.getElem_append_left, List.getElem_map, List.getElem_finRange]
    · have hi : i = n := by simp at hi₁; omega
      subst i
      simp [List.getElem_append_right]

private theorem update_A (k : StepKind) (r : ℚ) (p : Phase → ℚ) :
    AKLT.Blueprint.H3.phaseUpdate (phaseTransition k r) p .A =
      p .A * phaseDiagonal .A k := by
  unfold AKLT.Blueprint.H3.phaseUpdate
  rw [phase_sum]
  simp [phaseTransition, phaseDiagonal]

private theorem update_B (k : StepKind) (r : ℚ) (p : Phase → ℚ) :
    AKLT.Blueprint.H3.phaseUpdate (phaseTransition k r) p .B =
      p .B * phaseDiagonal .B k := by
  unfold AKLT.Blueprint.H3.phaseUpdate
  rw [phase_sum]
  simp [phaseTransition, phaseDiagonal]

private theorem update_C (k : StepKind) (r : ℚ) (p : Phase → ℚ) :
    AKLT.Blueprint.H3.phaseUpdate (phaseTransition k r) p .C =
      p .A * phaseTransition k r .A .C + p .C * phaseDiagonal .C k := by
  unfold AKLT.Blueprint.H3.phaseUpdate
  rw [phase_sum]
  simp [phaseTransition, phaseDiagonal]

private theorem update_D (k : StepKind) (r : ℚ) (p : Phase → ℚ) :
    AKLT.Blueprint.H3.phaseUpdate (phaseTransition k r) p .D =
      p .B * phaseTransition k r .B .D + p .D * phaseDiagonal .D k := by
  unfold AKLT.Blueprint.H3.phaseUpdate
  rw [phase_sum]
  simp [phaseTransition, phaseDiagonal]

private theorem singleChange_castSucc {n : ℕ} (k : Fin (n + 1) → StepKind)
    (r : Fin (n + 1) → ℚ) (j : Fin n) (φ ψ : Phase) :
    AKLT.Blueprint.H3.singleChange k r j.castSucc φ ψ =
      AKLT.Blueprint.H3.singleChange (fun i : Fin n => k i.castSucc)
        (fun i => r i.castSucc) j φ ψ * phaseDiagonal ψ (k (Fin.last n)) := by
  unfold AKLT.Blueprint.H3.singleChange
  rw [Fin.prod_univ_castSucc]
  have hlt : ¬ n < (j : Fin n).val := by have := j.isLt; omega
  have hne : (Fin.last n : Fin (n + 1)) ≠ j.castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  simp [Fin.val_castSucc, Fin.val_last, hlt, hne, Fin.castSucc_inj]

private theorem singleChange_last {n : ℕ} (k : Fin (n + 1) → StepKind)
    (r : Fin (n + 1) → ℚ) (φ ψ : Phase) :
    AKLT.Blueprint.H3.singleChange k r (Fin.last n) φ ψ =
      (∏ i : Fin n, phaseDiagonal φ (k i.castSucc)) *
        phaseTransition (k (Fin.last n)) (r (Fin.last n)) φ ψ := by
  unfold AKLT.Blueprint.H3.singleChange
  rw [Fin.prod_univ_castSucc]
  simp [Fin.val_castSucc, Fin.val_last]

private theorem phaseRun_coordinates : ∀ n : ℕ, ∀ k : Fin n → StepKind,
    ∀ r : Fin n → ℚ,
    let p := AKLT.Blueprint.H3.phaseRun
      (fun i => phaseTransition (k i) (r i)) (List.finRange n) phaseInitial
    p .A = (∏ i : Fin n, phaseDiagonal .A (k i)) ∧
    p .B = (∏ i : Fin n, phaseDiagonal .B (k i)) ∧
    p .C = (∑ j : Fin n, AKLT.Blueprint.H3.singleChange k r j .A .C) ∧
    p .D = (∑ j : Fin n, AKLT.Blueprint.H3.singleChange k r j .B .D) := by
  intro n
  induction n with
  | zero =>
      intro k r
      simp [AKLT.Blueprint.H3.phaseRun, AKLT.Blueprint.H3.singleChange,
        phaseInitial, phaseDiagonal]
  | succ n ih =>
      intro k r
      let k₀ : Fin n → StepKind := fun i => k i.castSucc
      let r₀ : Fin n → ℚ := fun i => r i.castSucc
      have hcoords := ih k₀ r₀
      rcases hcoords with ⟨hA, hB, hC, hD⟩
      have hrun :
          AKLT.Blueprint.H3.phaseRun
            (fun i : Fin (n + 1) => phaseTransition (k i) (r i))
            (List.finRange (n + 1)) phaseInitial =
          AKLT.Blueprint.H3.phaseUpdate
            (phaseTransition (k (Fin.last n)) (r (Fin.last n)))
            (AKLT.Blueprint.H3.phaseRun
              (fun i : Fin n => phaseTransition (k i.castSucc) (r i.castSucc))
              (List.finRange n) phaseInitial) := by
        rw [finRange_castSucc_append]
        simp only [AKLT.Blueprint.H3.phaseRun, List.foldl_append,
          List.foldl_cons, List.foldl_nil]
        rw [List.foldl_map]
      have hsumAC :
          (∑ j : Fin (n + 1), AKLT.Blueprint.H3.singleChange k r j .A .C) =
            (∑ j : Fin n, AKLT.Blueprint.H3.singleChange k₀ r₀ j .A .C) *
              phaseDiagonal .C (k (Fin.last n)) +
            (∏ i : Fin n, phaseDiagonal .A (k i.castSucc)) *
              phaseTransition (k (Fin.last n)) (r (Fin.last n)) .A .C := by
        rw [Fin.sum_univ_castSucc]
        simp_rw [singleChange_castSucc]
        rw [Finset.sum_mul, singleChange_last]
      have hsumBD :
          (∑ j : Fin (n + 1), AKLT.Blueprint.H3.singleChange k r j .B .D) =
            (∑ j : Fin n, AKLT.Blueprint.H3.singleChange k₀ r₀ j .B .D) *
              phaseDiagonal .D (k (Fin.last n)) +
            (∏ i : Fin n, phaseDiagonal .B (k i.castSucc)) *
              phaseTransition (k (Fin.last n)) (r (Fin.last n)) .B .D := by
        rw [Fin.sum_univ_castSucc]
        simp_rw [singleChange_castSucc]
        rw [Finset.sum_mul, singleChange_last]
      constructor
      · rw [hrun, update_A, hA, Fin.prod_univ_castSucc]
      constructor
      · rw [hrun, update_B, hB, Fin.prod_univ_castSucc]
      constructor
      · rw [hrun, update_C, hC, hA, hsumAC]
        ring
      · rw [hrun, update_D, hD, hB, hsumBD]
        ring

theorem main : AKLT.Blueprint.H3.PhaseFoldExpansionStatement := by
  intro n k r
  have hcoords := phaseRun_coordinates n k r
  rcases hcoords with ⟨_, _, hC, hD⟩
  rw [phase_sum]
  simp [phaseTerminal]
  rw [hC, hD, ← Finset.sum_add_distrib]

end AKLT.W.H3M003

#print axioms AKLT.W.H3M003.main
