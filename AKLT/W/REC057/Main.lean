module
public import AKLT.Blueprint.Rec.NodesClosure

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

open AKLT.Defs
open AKLT.Blueprint.Rec

namespace AKLT.W.REC057

private theorem traceNetwork_append_pair {G : Finset Plane} (D : Network G)
    (xs : List Plane) (a z : Plane) :
    traceNetwork D (xs ++ [a, z]) =
      traceStep (traceNetwork D (xs ++ [a])) a z := by
  induction xs generalizing D with
  | nil => simp [traceNetwork]
  | cons b xs ih =>
    cases xs with
    | nil => simp [traceNetwork]
    | cons c rest =>
      simp only [List.cons_append, traceNetwork]
      exact ih (D := traceStep D b c)

private theorem prefix_succ {G : Finset Plane} {n : ℕ} (D : Network G)
    (u : Plane) (w : DirectionWord n) (j : ℕ) (hj : j < n) :
    prefixNetwork D u w (j + 1) =
      traceStep (prefixNetwork D u w j) (wordVertex u w j) (wordVertex u w (j + 1)) := by
  have hsmall : j + 1 ≤ n + 1 := by omega
  have hlarge : j + 2 ≤ n + 1 := by omega
  have hbase :
      (List.map (wordVertex u w) (List.range (j + 1))) =
        List.map (wordVertex u w) (List.range j) ++ [wordVertex u w j] := by
    simp [List.range_succ, List.map_append]
  have hlong :
      (List.map (wordVertex u w) (List.range (j + 2))) =
        List.map (wordVertex u w) (List.range j) ++
          [wordVertex u w j, wordVertex u w (j + 1)] := by
    simp [List.range_succ, List.map_append, List.append_assoc]
  have htake_small :
      (wordVertices u w).take (j + 1) =
        List.map (wordVertex u w) (List.range (j + 1)) := by
    simp only [wordVertices, ← List.map_take, List.take_range]
    rw [Nat.min_eq_left hsmall]
  have htake_large :
      (wordVertices u w).take (j + 2) =
        List.map (wordVertex u w) (List.range (j + 2)) := by
    simp only [wordVertices, ← List.map_take, List.take_range]
    rw [Nat.min_eq_left hlarge]
  rw [prefixNetwork, prefixNetwork, htake_large, htake_small, hlong, hbase]
  exact traceNetwork_append_pair D (List.map (wordVertex u w) (List.range j))
    (wordVertex u w j) (wordVertex u w (j + 1))

private theorem traceStep_status_ne_U {G : Finset Plane} (D : Network G)
    (x y o : Plane) (h : D.status x ≠ .U) :
    (traceStep D y o).status x ≠ .U := by
  by_cases hxy : x = y
  · subst y
    simp [traceStep, h]
  · simp [traceStep, hxy, h]

private theorem traceStep_departure_ne_U {G : Finset Plane} (D : Network G)
    (y o : Plane) (h : D.status y = .U) :
    (traceStep D y o).status y ≠ .U := by
  simp [traceStep, h]

private theorem prefix_status_ne_U_of {G : Finset Plane} {n : ℕ}
    (D : Network G) (u : Plane) (w : DirectionWord n)
    (x : Plane) : ∀ i j : ℕ, i ≤ j → j ≤ n →
      (prefixNetwork D u w i).status x ≠ .U →
      (prefixNetwork D u w j).status x ≠ .U := by
  intro i j
  induction j generalizing i with
  | zero =>
      intro hij hj hstart
      have hi : i = 0 := by omega
      subst i
      exact hstart
  | succ j ih =>
      intro hij hj hstart
      by_cases heq : i = j + 1
      · subst i
        exact hstart
      · have hij' : i ≤ j := by omega
        have hj' : j ≤ n := by omega
        have hprev := ih i hij' hj' hstart
        rw [prefix_succ D u w j (by omega)]
        exact traceStep_status_ne_U _ x _ _ hprev

private theorem later_status_ne_U {G : Finset Plane} {n : ℕ}
    (D : Network G) (u : Plane) (w : DirectionWord n)
    (i j : ℕ) (hij : i < j) (hj : j ≤ n) :
    (prefixNetwork D u w i).status (wordVertex u w i) = .U →
    (prefixNetwork D u w j).status (wordVertex u w i) ≠ .U := by
  intro hU
  have hnext := traceStep_departure_ne_U
    (D := prefixNetwork D u w i) (wordVertex u w i) (wordVertex u w (i + 1)) hU
  have hrec := prefix_succ D u w i (by omega)
  rw [← hrec] at hnext
  exact prefix_status_ne_U_of D u w (wordVertex u w i) (i + 1) j (by omega)
    hj hnext

theorem main : AKLT.Blueprint.Rec.UDepartureInjectiveStatement := by
  intro G D hAux u hStart T n w hTrail i j hUi hUj hVertex
  have hval : i.val = j.val := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hij | hji
    · have hLater := later_status_ne_U D u w i.val j.val hij (Nat.le_of_lt j.isLt) hUi
      rw [hVertex] at hLater
      exact hLater hUj
    · have hLater := later_status_ne_U D u w j.val i.val hji (Nat.le_of_lt i.isLt) hUj
      rw [← hVertex] at hLater
      exact hLater hUi
  exact Fin.ext hval

end AKLT.W.REC057

end
