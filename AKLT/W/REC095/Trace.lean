module
public import AKLT.Blueprint.Rec.NodesV2Walk
public import AKLT.W.REC039.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC095

/-- The mass-free factor at an evolving departure. -/
def departureCoefficient (s : Status) : ℚ :=
  if s = .U then 1 / 3 else if s = .D then 1 / 5 else 0

theorem departureCoefficient_nonneg (s : Status) : 0 ≤ departureCoefficient s := by
  cases s <;> norm_num [departureCoefficient]

private theorem traceNetwork_append_pair {G : Finset Plane} (D : Network G)
    (xs : List Plane) (y o : Plane) :
    traceNetwork D (xs ++ [y, o]) = traceStep (traceNetwork D (xs ++ [y])) y o := by
  induction xs generalizing D with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons z zs => exact ih (traceStep D x z)

private theorem prefix_list {n : ℕ} (u : Plane) (w : DirectionWord n) (j : ℕ) (hj : j ≤ n) :
    (wordVertices u w).take (j + 1) = (List.range (j + 1)).map (wordVertex u w) := by
  simp [wordVertices, ← List.map_take, List.take_range, Nat.min_eq_left (by omega : j + 1 ≤ n + 1)]

private theorem prefix_succ {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (w : DirectionWord n) (j : ℕ) (hj : j < n) :
    prefixNetwork D u w (j + 1) =
      traceStep (prefixNetwork D u w j) (wordVertex u w j) (wordVertex u w (j + 1)) := by
  unfold prefixNetwork
  rw [prefix_list u w (j + 1) (by omega), prefix_list u w j (by omega)]
  simp only [List.range_succ, List.map_append, List.map_singleton]
  simpa only [List.append_assoc, List.singleton_append] using
    traceNetwork_append_pair D ((List.range j).map (wordVertex u w))
      (wordVertex u w j) (wordVertex u w (j + 1))

theorem present_neighbour {G : Finset Plane} {D : Network G} {x y : Plane}
    (hD : D.LocalRules) (h : D.Present x y) : y ∈ D.presentNeighbours x := by
  exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp (hD.2.1 x h.2.2.2.1)).1, h⟩

private theorem traceStep_status_ne_U {G : Finset Plane} (D : Network G) (y o : Plane) :
    (traceStep D y o).status y ≠ .U := by
  simp only [traceStep, Function.update_self]
  split_ifs <;> simp

private theorem traceStep_status_ne_U_of {G : Finset Plane} {D : Network G} {x y o : Plane}
    (hx : D.status x ≠ .U) : (traceStep D y o).status x ≠ .U := by
  by_cases hxy : x = y
  · subst x; exact traceStep_status_ne_U D y o
  · simpa [traceStep, Function.update_of_ne hxy] using hx

private theorem prefix_status_ne_U_of {G : Finset Plane} {n : ℕ} (D : Network G)
    (u : Plane) (w : DirectionWord n) {j k : ℕ} (hjk : j ≤ k) (hkn : k ≤ n)
    {x : Plane} (hx : (prefixNetwork D u w j).status x ≠ .U) :
    (prefixNetwork D u w k).status x ≠ .U := by
  induction k, hjk using Nat.le_induction with
  | base => exact hx
  | succ k hjk ih =>
    rw [prefix_succ D u w k (by omega)]
    exact traceStep_status_ne_U_of (ih (by omega))

theorem revisit_status_ne_U {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (w : DirectionWord n) (i : Fin n) (hi : wordRevisit u w i = true) :
    (prefixNetwork D u w i.val).status (wordVertex u w i.val) ≠ .U := by
  have hc : 0 < departureCount u w i.val (wordVertex u w i.val) := by
    simpa [wordRevisit] using hi
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hc
  obtain ⟨hjrange, hv⟩ := Finset.mem_filter.mp hj
  have hji : j < i.val := lt_of_lt_of_le (Finset.mem_range.mp hjrange) (min_le_left _ _)
  have hx : (prefixNetwork D u w (j + 1)).status (wordVertex u w j) ≠ .U := by
    rw [prefix_succ D u w j (by omega)]
    exact traceStep_status_ne_U _ _ _
  rw [← hv]
  exact prefix_status_ne_U_of D u w (by omega) (by omega) hx

/-- Prefix validity and admissibility, using the proved trace-dynamics leaf. -/
theorem traceDynamics : TraceDynamicsStatement := AKLT.W.REC039.main

end AKLT.W.REC095
