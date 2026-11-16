import AKLT.Blueprint.H3.NodesPhase

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.H3

namespace AKLT.W.H3M008

private def phaseDelta (φ : Phase) : Phase → ℚ := fun ψ => if ψ = φ then 1 else 0

private def rowUpdate {α : Type} (M : α → Phase → Phase → ℚ) (i : α)
    (p : Phase → ℚ) : Phase → ℚ := fun ψ => ∑ φ, p φ * M i φ ψ

private def trueRowUpdate {n : ℕ} (w : DirectionWord n) (p : Phase → ℚ)
    (i : Fin n) : Phase → ℚ := rowUpdate (truePhaseCoefficient w) i p

private theorem take_finRange_cast {n L : ℕ} (h : L ≤ n) :
    (List.finRange n).take L = (List.finRange L).map (Fin.castLE h) := by
  induction L generalizing n with
  | zero => simp
  | succ L ih =>
      cases n with
      | zero => omega
      | succ n =>
          have h' : L ≤ n := by omega
          simp only [List.finRange_succ, List.take_succ_cons, List.map_cons]
          rw [← List.map_take, ih h']
          simp only [List.map_map, Function.comp_def]
          apply congrArg (fun xs : List (Fin (n + 1)) => 0 :: xs)
          apply List.map_congr_left
          intro i _
          symm
          exact Fin.castLE_succ h i

private theorem foldl_congr {α β : Type} (l : List α) (f g : β → α → β)
    (b : β) (h : ∀ b a, f b a = g b a) :
    List.foldl f b l = List.foldl g b l := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
      simp only [List.foldl_cons]
      rw [h b a]
      exact ih (g b a)

private theorem rowUpdate_linear {α : Type} (M : α → Phase → Phase → ℚ) (i : α)
    (c : Phase → ℚ) (V : Phase → Phase → ℚ) :
    rowUpdate M i (fun ψ => ∑ φ, c φ * V φ ψ) =
      fun ψ => ∑ φ, c φ * rowUpdate M i (V φ) ψ := by
  funext ψ
  simp only [rowUpdate]
  calc
    (∑ η, (∑ φ, c φ * V φ η) * M i η ψ) =
        ∑ η, ∑ φ, (c φ * V φ η) * M i η ψ := by
          apply Finset.sum_congr rfl
          intro η _
          rw [Finset.sum_mul]
    _ = ∑ φ, ∑ η, (c φ * V φ η) * M i η ψ := by
          rw [Finset.sum_comm]
    _ = ∑ φ, c φ * ∑ η, V φ η * M i η ψ := by
          apply Finset.sum_congr rfl
          intro φ _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro η _
          ring

private theorem foldl_linear {α : Type} (M : α → Phase → Phase → ℚ)
    (l : List α) (c : Phase → ℚ) (V : Phase → Phase → ℚ) :
    List.foldl (fun p i => rowUpdate M i p)
      (fun ψ => ∑ φ, c φ * V φ ψ) l =
    fun ψ => ∑ φ, c φ * List.foldl (fun p i => rowUpdate M i p) (V φ) l ψ := by
  induction l generalizing V with
  | nil =>
      funext ψ
      simp
  | cons i l ih =>
      simp only [List.foldl_cons]
      rw [rowUpdate_linear]
      exact ih (fun φ => rowUpdate M i (V φ))

private theorem row_as_delta (p : Phase → ℚ) :
    p = fun ψ => ∑ φ, p φ * phaseDelta φ ψ := by
  funext ψ
  simp [phaseDelta]

private theorem prefix_fold_eq {n : ℕ} (w : DirectionWord n) (L : ℕ)
    (hL : L ≤ n)
    (hcoef : ∀ i : Fin L, ∀ φ ψ : Phase,
      truePhaseCoefficient (takeWord w L) i φ ψ =
        truePhaseCoefficient w (Fin.castLE hL i) φ ψ) :
    prefixPhases (takeWord w L) =
      List.foldl (trueRowUpdate w) phaseInitial (List.take L (List.finRange n)) := by
  change List.foldl (trueRowUpdate (takeWord w L)) phaseInitial (List.finRange L) = _
  rw [take_finRange_cast hL, List.foldl_map]
  apply foldl_congr
  intro p i
  funext ψ
  unfold trueRowUpdate rowUpdate
  apply Finset.sum_congr rfl
  intro φ _
  rw [hcoef i φ ψ]

private theorem suffix_terminal_linear {n : ℕ} (w : DirectionWord n) (L : ℕ)
    (p : Phase → ℚ) :
    (∑ ψ : Phase,
      List.foldl (trueRowUpdate w) p (List.drop L (List.finRange n)) ψ * phaseTerminal ψ) =
    ∑ φ : Phase, p φ *
      (∑ ψ : Phase,
        List.foldl (trueRowUpdate w) (phaseDelta φ) (List.drop L (List.finRange n)) ψ *
          phaseTerminal ψ) := by
  have hfold : List.foldl (trueRowUpdate w) p (List.drop L (List.finRange n)) =
      fun ψ => ∑ φ, p φ *
        List.foldl (trueRowUpdate w) (phaseDelta φ) (List.drop L (List.finRange n)) ψ := by
    conv_lhs => rw [row_as_delta p]
    exact foldl_linear (truePhaseCoefficient w) (List.drop L (List.finRange n)) p phaseDelta
  rw [hfold]
  calc
    (∑ ψ : Phase,
        (∑ φ : Phase, p φ *
          List.foldl (trueRowUpdate w) (phaseDelta φ) (List.drop L (List.finRange n)) ψ) *
          phaseTerminal ψ) =
      ∑ ψ : Phase, ∑ φ : Phase,
        (p φ * List.foldl (trueRowUpdate w) (phaseDelta φ)
          (List.drop L (List.finRange n)) ψ) * phaseTerminal ψ := by
            apply Finset.sum_congr rfl
            intro ψ _
            rw [Finset.sum_mul]
    _ = ∑ φ : Phase, ∑ ψ : Phase,
        (p φ * List.foldl (trueRowUpdate w) (phaseDelta φ)
          (List.drop L (List.finRange n)) ψ) * phaseTerminal ψ := by
            rw [Finset.sum_comm]
    _ = ∑ φ : Phase, p φ *
        (∑ ψ : Phase,
          List.foldl (trueRowUpdate w) (phaseDelta φ) (List.drop L (List.finRange n)) ψ *
            phaseTerminal ψ) := by
          apply Finset.sum_congr rfl
          intro φ _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ψ _
          ring

/-- Split the finite phase fold at a prefix whose transition coefficients agree. -/
theorem main : AKLT.Blueprint.H3.PhaseSplitAlgebraStatement := by
  intro n w L hL hcoef
  have hcoef' : ∀ i : Fin L, ∀ φ ψ : Phase,
      truePhaseCoefficient (takeWord w L) i φ ψ =
        truePhaseCoefficient w (Fin.castLE hL i) φ ψ := by
    intro i φ ψ
    have hi : (Fin.castLE hL i : Fin n) = ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩ := by
      apply Fin.ext
      rfl
    rw [hi]
    exact hcoef i φ ψ
  have hpref := prefix_fold_eq w L hL hcoef'
  have hfull : prefixPhases w =
      List.foldl (trueRowUpdate w) phaseInitial
        (List.take L (List.finRange n) ++ List.drop L (List.finRange n)) := by
    change List.foldl (trueRowUpdate w) phaseInitial (List.finRange n) = _
    conv_lhs => rw [← List.take_append_drop L (List.finRange n)]
  rw [hfull, List.foldl_append, ← hpref]
  change (∑ φ : Phase,
      List.foldl (trueRowUpdate w) (prefixPhases (takeWord w L))
        (List.drop L (List.finRange n)) φ * phaseTerminal φ) = _
  have hsuffix (φ : Phase) : truePhaseSuffix w L φ =
      ∑ ψ : Phase, List.foldl (trueRowUpdate w) (phaseDelta φ)
        (List.drop L (List.finRange n)) ψ * phaseTerminal ψ := rfl
  simp_rw [hsuffix]
  exact suffix_terminal_linear w L (prefixPhases (takeWord w L))

  
end AKLT.W.H3M008

#print axioms AKLT.W.H3M008.main
