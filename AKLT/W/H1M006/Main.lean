module
public import AKLT.W.H1M006.Local

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M006

/-- Summing the passage coordinate first gives the current and next passage factors. -/
theorem main : AKLT.Blueprint.H1.PassageFubiniStatement := by
  intro hSite π hCovered m f g hNeighbours
  have h0active : (0, 0) ∈ π.active := origin_active π hCovered
  let e := splitAssignments π h0active
  have hCurrentSum : patternCurrent π m =
      ∑ n : (x : π.active) → SpinLetter, originalSummand π false m n := by
    simp [patternCurrent, patternFunctional, originalSummand]
  have hNextSum : patternNext π m =
      ∑ n : (x : π.active) → SpinLetter, originalSummand π true m n := by
    simp [patternNext, patternFunctional, originalSummand]
  constructor
  · rw [hCurrentSum]
    calc
      _ = ∑ q : (passageComplement π → SpinLetter) × SpinLetter,
            originalSummand π false m (e q) :=
          Fintype.sum_equiv e.symm _ _ (by intro n; simp)
      _ = ∑ n : passageComplement π → SpinLetter,
            ∑ p : SpinLetter, originalSummand π false m (e (n, p)) :=
          Fintype.sum_prod_type _
      _ = ∑ n : passageComplement π → SpinLetter,
            erasedSummand π m (passageI π.outgoing.step f g)
              n := by
          apply Finset.sum_congr rfl
          intro n hn
          exact (local_fubini hSite π hCovered m f g hNeighbours n).1
      _ = withoutPassageFunctional π m (passageI π.outgoing.step f g) := rfl
  · rw [hNextSum]
    calc
      _ = ∑ q : (passageComplement π → SpinLetter) × SpinLetter,
            originalSummand π true m (e q) :=
          Fintype.sum_equiv e.symm _ _ (by intro n; simp)
      _ = ∑ n : passageComplement π → SpinLetter,
            ∑ p : SpinLetter, originalSummand π true m (e (n, p)) :=
          Fintype.sum_prod_type _
      _ = ∑ n : passageComplement π → SpinLetter,
            erasedSummand π m (passageJ f g)
              n := by
          apply Finset.sum_congr rfl
          intro n hn
          exact (local_fubini hSite π hCovered m f g hNeighbours n).2
      _ = withoutPassageFunctional π m (passageJ f g) := rfl

end AKLT.W.H1M006
