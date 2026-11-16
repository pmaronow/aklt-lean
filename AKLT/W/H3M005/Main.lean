import AKLT.Blueprint.H3.NodesPhase

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H3M005

private def listExposure {α : Type} (x r : α → ℚ) : List α → ℚ
  | [] => 0
  | a :: as => x a * (r a + listExposure x r as)

private def listMultiplier {α : Type} [BEq α] (x : α → ℚ) (l : List α) (a : α) : ℚ :=
  ((l.take (l.idxOf a + 1)).map x).prod

private theorem listExposure_expansion {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
    (x r : α → ℚ) (l : List α) (hn : l.Nodup) :
    listExposure x r l = ∑ a ∈ l.toFinset, r a * listMultiplier x l a := by
  induction l with
  | nil => simp [listExposure]
  | cons a as ih =>
      have has : as.Nodup := List.nodup_cons.mp hn |>.2
      have hnot : a ∉ as := List.nodup_cons.mp hn |>.1
      have hnotFinset : a ∉ as.toFinset := by simpa using hnot
      have hmult : ∀ b ∈ as.toFinset, listMultiplier x (a :: as) b = x a * listMultiplier x as b := by
        intro b hb
        have hba : b ≠ a := by
          intro hEq
          apply hnot
          exact List.mem_toFinset.mp (hEq ▸ hb)
        simp [listMultiplier, Ne.symm hba]
      calc
        listExposure x r (a :: as) =
            x a * (r a + ∑ b ∈ as.toFinset, r b * listMultiplier x as b) := by
          rw [listExposure, ih has]
        _ = ∑ b ∈ (a :: as).toFinset, r b * listMultiplier x (a :: as) b := by
          rw [List.toFinset_cons, Finset.sum_insert hnotFinset]
          have hhead : listMultiplier x (a :: as) a = x a := by
            simp [listMultiplier, List.idxOf_cons_self]
          rw [hhead]
          calc
            x a * (r a + ∑ b ∈ as.toFinset, r b * listMultiplier x as b) =
                r a * x a + x a * (∑ b ∈ as.toFinset, r b * listMultiplier x as b) := by ring
            _ = r a * x a + ∑ b ∈ as.toFinset, r b * listMultiplier x (a :: as) b := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro b hb
              rw [hmult b hb]
              ring

theorem main : AKLT.Blueprint.H3.ExposureListExpansionStatement := by
  intro n w reward l hn
  let x : Fin n → ℚ := fun i => passageFactor (wordStraight kernelIncoming w i)
  have hfold : ∀ t, listExposure x reward t = AKLT.Defs.exposureSum w reward t := by
    intro t
    induction t with
    | nil => rfl
    | cons a as ih => simp [listExposure, AKLT.Defs.exposureSum, x, ih]
  calc
    AKLT.Defs.exposureSum w reward l = listExposure x reward l := (hfold l).symm
    _ = ∑ j ∈ l.toFinset, reward j * listMultiplier x l j := listExposure_expansion x reward l hn
    _ = ∑ j ∈ l.toFinset, reward j * AKLT.Blueprint.H3.orderedMultiplier w l j := by
      simp [listMultiplier, AKLT.Blueprint.H3.orderedMultiplier, x]

end AKLT.W.H3M005
