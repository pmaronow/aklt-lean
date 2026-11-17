module
public import AKLT.Blueprint.Rec.NodesV2Walk
public import AKLT.W.REC094.Positivity

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC094

def departureCoefficient {G : Finset Plane} (D : Network G) (y : Plane) : ℚ :=
  if D.status y = .U then 1 / 3 else if D.status y = .D then 1 / 5 else 0

theorem traceNetwork_append {G : Finset Plane} (D : Network G)
    (l : List Plane) (y : Plane) (r : List Plane) :
    traceNetwork D (l ++ y :: r) =
      traceNetwork (traceNetwork D (l ++ [y])) (y :: r) := by
  induction l generalizing D with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l => exact ih (traceStep D a b)

theorem traceCoefficient_append {G : Finset Plane} (D : Network G)
    (l : List Plane) (y : Plane) (r : List Plane) :
    traceCoefficient D (l ++ y :: r) =
      traceCoefficient D (l ++ [y]) *
        traceCoefficient (traceNetwork D (l ++ [y])) (y :: r) := by
  induction l generalizing D with
  | nil => simp [traceCoefficient, traceNetwork]
  | cons a l ih =>
    cases l with
    | nil => simp [traceCoefficient, traceNetwork]
    | cons b l =>
      simp only [List.cons_append, traceCoefficient, traceNetwork]
      simp only [List.cons_append] at ih
      rw [ih (traceStep D a b), mul_assoc]

def vertexList (v : ℕ → Plane) (n : ℕ) : List Plane :=
  (List.range (n + 1)).map v

theorem vertexList_succ (v : ℕ → Plane) (n : ℕ) :
    vertexList v (n + 1) = ((List.range n).map v) ++ [v n, v (n + 1)] := by
  simp [vertexList, List.range_succ, List.map_append, List.append_assoc]

theorem traceNetwork_vertexList_succ {G : Finset Plane} (D : Network G)
    (v : ℕ → Plane) (n : ℕ) :
    traceNetwork D (vertexList v (n + 1)) =
      traceStep (traceNetwork D (vertexList v n)) (v n) (v (n + 1)) := by
  rw [vertexList_succ, traceNetwork_append]
  simp only [vertexList, List.range_succ, List.map_append, List.map_singleton, traceNetwork]

theorem traceCoefficient_vertexList_succ {G : Finset Plane} (D : Network G)
    (v : ℕ → Plane) (n : ℕ) :
    traceCoefficient D (vertexList v (n + 1)) =
      traceCoefficient D (vertexList v n) *
        departureCoefficient (traceNetwork D (vertexList v n)) (v n) := by
  rw [vertexList_succ, traceCoefficient_append]
  simp only [traceCoefficient, mul_one]
  simp only [vertexList, List.range_succ, List.map_append, List.map_singleton,
    departureCoefficient]

theorem traceCoefficient_vertexList {G : Finset Plane} (D : Network G)
    (v : ℕ → Plane) (n : ℕ) :
    traceCoefficient D (vertexList v n) =
      ∏ i ∈ Finset.range n, departureCoefficient (traceNetwork D (vertexList v i)) (v i) := by
  induction n with
  | zero => simp [vertexList, traceCoefficient]
  | succ n ih => rw [traceCoefficient_vertexList_succ, ih, Finset.prod_range_succ]

theorem traceRatio_vertexList {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (v : ℕ → Plane) (n : ℕ) :
    traceRatio D τ b (vertexList v n) =
      ∏ i ∈ Finset.range n, stepRatio (traceNetwork D (vertexList v i)) τ b
        (v i) (v (i + 1)) := by
  induction n with
  | zero =>
    simp [vertexList, traceRatio, traceNetwork, ne_of_gt (partition_pos D τ b)]
  | succ n ih =>
    rw [Finset.prod_range_succ, ← ih]
    unfold stepRatio traceRatio
    simp only [traceNetwork]
    rw [traceNetwork_vertexList_succ]
    have hp := ne_of_gt (partition_pos (traceNetwork D (vertexList v n)) τ b)
    field_simp

theorem prefixNetwork_eq_vertexList {G : Finset Plane} {n : ℕ} (D : Network G)
    (u : Plane) (w : DirectionWord n) (j : ℕ) (hj : j ≤ n) :
    AKLT.Blueprint.Rec.prefixNetwork D u w j =
      traceNetwork D (vertexList (wordVertex u w) j) := by
  unfold AKLT.Blueprint.Rec.prefixNetwork wordVertices vertexList
  rw [← List.map_take, List.take_range, Nat.min_eq_left (by omega)]

theorem traceCoefficient_product {G : Finset Plane} {n : ℕ} (D : Network G)
    (u : Plane) (w : DirectionWord n) :
    traceCoefficient D (wordVertices u w) = ∏ i : Fin n,
      departureCoefficient (AKLT.Blueprint.Rec.prefixNetwork D u w i.val)
        (wordVertex u w i.val) := by
  change traceCoefficient D (vertexList (wordVertex u w) n) = _
  rw [traceCoefficient_vertexList, ← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _
  rw [prefixNetwork_eq_vertexList D u w i.val (Nat.le_of_lt i.isLt)]

theorem traceRatio_product {G : Finset Plane} {n : ℕ} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (u : Plane) (w : DirectionWord n) :
    traceRatio D τ b (wordVertices u w) = ∏ i : Fin n,
      stepRatio (AKLT.Blueprint.Rec.prefixNetwork D u w i.val) τ b
        (wordVertex u w i.val) (wordVertex u w (i.val + 1)) := by
  change traceRatio D τ b (vertexList (wordVertex u w) n) = _
  rw [traceRatio_vertexList, ← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _
  rw [prefixNetwork_eq_vertexList D u w i.val (Nat.le_of_lt i.isLt)]

theorem traceStep_status_U_iff {G : Finset Plane} (D : Network G)
    (y o x : Plane) :
    (traceStep D y o).status x = .U ↔ D.status x = .U ∧ x ≠ y := by
  by_cases hx : x = y
  · subst x
    by_cases hu : D.status y = .U <;> simp [traceStep, hu]
  · simp [traceStep, hx]

theorem traceNetwork_vertexList_status_U_iff {G : Finset Plane} (D : Network G)
    (v : ℕ → Plane) (n : ℕ) (x : Plane) :
    (traceNetwork D (vertexList v n)).status x = .U ↔
      D.status x = .U ∧ ∀ j < n, v j ≠ x := by
  induction n with
  | zero => simp [vertexList, traceNetwork]
  | succ n ih =>
    rw [traceNetwork_vertexList_succ, traceStep_status_U_iff, ih]
    constructor
    · rintro ⟨⟨hu, hj⟩, hn⟩
      refine ⟨hu, ?_⟩
      intro j hjn
      by_cases he : j = n
      · subst j; exact Ne.symm hn
      · exact hj j (by omega)
    · rintro ⟨hu, hj⟩
      exact ⟨⟨hu, fun j hjn => hj j (by omega)⟩, Ne.symm (hj n (by omega))⟩

/-- A U departure cannot be a lattice revisit, without any network assumptions. -/
theorem U_departure_first {G : Finset Plane} {n : ℕ} (D : Network G)
    (u : Plane) (w : DirectionWord n) (i : Fin n)
    (hU : (AKLT.Blueprint.Rec.prefixNetwork D u w i.val).status
      (wordVertex u w i.val) = .U) : wordRevisit u w i = false := by
  rw [prefixNetwork_eq_vertexList D u w i.val (Nat.le_of_lt i.isLt),
    traceNetwork_vertexList_status_U_iff] at hU
  cases hr : wordRevisit u w i with
  | false => rfl
  | true =>
    have hp : 0 < departureCount u w i.val (wordVertex u w i.val) := by
      simpa only [wordRevisit, decide_eq_true_eq] using hr
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hp
    rcases Finset.mem_filter.mp hj with ⟨hj, he⟩
    have hjn : j < i.val := lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.min_le_left _ _)
    exact False.elim (hU.2 j hjn he)

theorem wordVertex_succ {n : ℕ} (u : Plane) (w : DirectionWord n) (i : Fin n) :
    wordVertex u w (i.val + 1) = wordVertex u w i.val + (w i).step := by
  have hs (j : Fin n) :
      (if j.val < i.val + 1 then (w j).step else 0) =
        (if j.val < i.val then (w j).step else 0) +
          if j = i then (w i).step else 0 := by
    by_cases he : j = i
    · subst j; simp
    · have hv : j.val ≠ i.val := fun h => he (Fin.ext h)
      by_cases hj : j.val < i.val <;>
        simp [he, hj, show (j.val < i.val + 1) ↔ j.val < i.val by omega]
  unfold wordVertex
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  simp [add_assoc]

#print axioms traceCoefficient_product
#print axioms traceRatio_product
#print axioms U_departure_first

end AKLT.W.REC094
