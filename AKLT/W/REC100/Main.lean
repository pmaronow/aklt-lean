import AKLT.Blueprint.Rec.NodesV2Ordering
import Mathlib.Data.Prod.Lex

noncomputable section

namespace AKLT.W.REC100

open AKLT.Defs
open AKLT.Blueprint.Rec

def shortScore {n : ℕ} (w : DirectionWord n) (i : Fin n) : WithTop ℚ :=
  if witnessKappa w i = 0 then ⊤ else
    ↑((passageFactor (wordStraight kernelIncoming w i) - 1) /
      (passageFactor (wordStraight kernelIncoming w i) * witnessKappa w i))

def shortKey {n : ℕ} (w : DirectionWord n) (i : Fin n) : WithTop ℚ × ℕ :=
  (shortScore w i, i.val)

def shortKeyLE {n : ℕ} (w : DirectionWord n) (i j : Fin n) : Prop :=
  Prod.Lex (· < ·) (· ≤ ·) (shortKey w i) (shortKey w j)

noncomputable def shortKeyLEBool {n : ℕ} (w : DirectionWord n) (i j : Fin n) : Bool := by
  classical
  exact decide (shortKeyLE w i j)

theorem shortOrderLE_eq_decide_shortKeyLE {n : ℕ} (w : DirectionWord n) (i j : Fin n) :
    shortOrderLE w i j = shortKeyLEBool w i j := by
  classical
  unfold shortOrderLE shortKeyLEBool shortKeyLE shortKey shortScore
  dsimp only
  by_cases hi : witnessKappa w i = 0
  · by_cases hj : witnessKappa w j = 0
    · simp [hi, hj, Prod.lex_def]
    · simp [hi, hj, Prod.lex_def]
  · by_cases hj : witnessKappa w j = 0
    · simp [hi, hj, Prod.lex_def]
    · simp [hi, hj, Prod.lex_def]

theorem shortKeyLE_trans {n : ℕ} (w : DirectionWord n) {i j k : Fin n} :
    shortKeyLE w i j → shortKeyLE w j k → shortKeyLE w i k := by
  exact Prod.Lex.trans

theorem shortKeyLE_total {n : ℕ} (w : DirectionWord n) (i j : Fin n) :
    shortKeyLE w i j ∨ shortKeyLE w j i := by
  have htotal : Std.Total (Prod.Lex (· < ·) (· ≤ ·) :
      (WithTop ℚ × ℕ) → (WithTop ℚ × ℕ) → Prop) := inferInstance
  exact htotal.total (shortKey w i) (shortKey w j)

theorem shortOrderLE_trans {n : ℕ} (w : DirectionWord n) {i j k : Fin n} :
    shortOrderLE w i j = true → shortOrderLE w j k = true → shortOrderLE w i k = true := by
  classical
  intro hij hjk
  rw [shortOrderLE_eq_decide_shortKeyLE] at hij hjk ⊢
  have hij' : shortKeyLE w i j := of_decide_eq_true (by simpa [shortKeyLEBool] using hij)
  have hjk' : shortKeyLE w j k := of_decide_eq_true (by simpa [shortKeyLEBool] using hjk)
  simpa [shortKeyLEBool] using
    (Eq.mpr decide_eq_true_eq (shortKeyLE_trans w hij' hjk'))

theorem shortOrderLE_total {n : ℕ} (w : DirectionWord n) (i j : Fin n) :
    shortOrderLE w i j = true ∨ shortOrderLE w j i = true := by
  classical
  rw [shortOrderLE_eq_decide_shortKeyLE, shortOrderLE_eq_decide_shortKeyLE]
  rcases shortKeyLE_total w i j with h | h
  · left
    simpa [shortKeyLEBool] using (Eq.mpr decide_eq_true_eq h)
  · right
    simpa [shortKeyLEBool] using (Eq.mpr decide_eq_true_eq h)

theorem main : AKLT.Blueprint.Rec.ShortKernelOrderingStatementV2 := by
  intro n X w hw hn
  have hord : kernelOrdering w = (firstVisitList w).mergeSort (shortOrderLE w) := by
    simp only [kernelOrdering, ite_eq_left hn]
  constructor
  · exact hord
  · rw [hord]
    exact (List.pairwise_mergeSort (le := shortOrderLE w)
      (fun i j k hij hjk => shortOrderLE_trans w hij hjk)
      (fun i j => by
        rcases shortOrderLE_total w i j with h | h <;> simp [h])
      (firstVisitList w) :
      List.Pairwise (fun i j => shortOrderLE w i j = true)
        ((firstVisitList w).mergeSort (shortOrderLE w)))

end AKLT.W.REC100

end

#print axioms AKLT.W.REC100.main
