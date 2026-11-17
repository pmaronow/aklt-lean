module
public import AKLT.Blueprint.H1.NodesPassage

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M011

private theorem supportSpins_eq_patternSpins (π : PatternData)
    (n : (x : π.active) → SpinLetter) :
    supportSpins π.active n = π.spins n := by
  funext x
  simp [supportSpins, PatternData.spins]

private theorem originalIntegrand_eval (π : PatternData) (next : Bool)
    (n : (x : π.active) → SpinLetter) (m : Fin 20 → UnitVector) :
    AKLT.Blueprint.H1.localEvaluation (AKLT.Blueprint.H1.originalIntegrand π next)
        (π.spins n) (fun j => (m j).val) =
      (∏ e ∈ π.bonds,
        if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1
        else 1 + dot (π.spins n e.1) (π.spins n e.2)) *
      ∏ j : Fin 20,
        if π.statusAt (externalSlot j).1 = .X then 1
        else 1 + dot (m j).val (π.spins n (externalSlot j).1) := by
  unfold AKLT.Blueprint.H1.localEvaluation AKLT.Blueprint.H1.originalIntegrand
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_prod]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro e he
    by_cases h : next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step}
    · simp [h]
    · simp [h, formalDot, dot]
  · apply Finset.prod_congr rfl
    intro j hj
    by_cases h : π.statusAt (externalSlot j).1 = .X
    · simp [h]
    · simp [h, formalDot, dot]
      apply Finset.sum_congr rfl
      intro i hi
      ring

private theorem rawFunctional_eq_patternFunctional (π : PatternData) (next : Bool)
    (m : Fin 20 → UnitVector) :
    AKLT.Blueprint.H1.rawFunctional π.active (AKLT.Blueprint.H1.nextStatus π next)
        (AKLT.Blueprint.H1.originalIntegrand π next) (fun j => (m j).val) =
      patternFunctional π next m (fun _ => 1) := by
  classical
  unfold AKLT.Blueprint.H1.rawFunctional patternFunctional AKLT.Blueprint.H1.nextStatus
  simp only [supportSpins_eq_patternSpins]
  apply Finset.sum_congr rfl
  intro n hn
  rw [originalIntegrand_eval]
  ring_nf

theorem main : AKLT.Blueprint.H1.OriginalRawEvaluationStatement := by
  classical
  intro π next m
  rw [rawFunctional_eq_patternFunctional]
  cases next <;> simp [patternNext, patternCurrent]

end AKLT.W.H1M011
