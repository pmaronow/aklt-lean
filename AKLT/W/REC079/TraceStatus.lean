import AKLT.W.REC079.TraceGeometry
import AKLT.W.REC079.KernelSupport

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec AKLT.Cert.H2

namespace AKLT.W.REC079

/-- The actual law transition at a departure, including an already removed site. -/
def advanceStatus : Status → Status
  | .U => .D
  | .D | .X => .X

@[simp] theorem advanceStatus_ne_U (s : Status) : advanceStatus s ≠ .U := by
  cases s <;> decide

@[simp] theorem advanceStatus_twice (s : Status) : advanceStatus (advanceStatus s) = .X := by
  cases s <;> rfl

@[simp] theorem iterate_advance_X (k : ℕ) : advanceStatus^[k] .X = .X := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem iterate_advance_ne_U (s : Status) {k : ℕ} (hk : 0 < k) :
    advanceStatus^[k] s ≠ .U := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [Function.iterate_succ_apply']
  exact advanceStatus_ne_U _

theorem iterate_advance_removed (s : Status) {k : ℕ} (hk : 2 ≤ k) :
    advanceStatus^[k] s = .X := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm 2 j, Function.iterate_add_apply]
  simp [Function.iterate_succ_apply]

/-- Status depends exactly on the number of previous departures, never on
arrivals alone. The live final vertex is excluded by dropLast. -/
theorem traceNetwork_status {G : Finset Plane} (D : Network G) (l : List Plane) (x : Plane) :
    (traceNetwork D l).status x = advanceStatus^[(l.dropLast.count x)] (D.status x) := by
  induction l generalizing D with
  | nil => simp [traceNetwork]
  | cons y l ih =>
    cases l with
    | nil => simp [traceNetwork]
    | cons o rest =>
      simp only [traceNetwork, ih, List.dropLast_cons_cons, List.count_cons]
      by_cases hy : y = x
      · subst y
        cases h : D.status x <;> simp [traceStep, h, advanceStatus, Function.iterate_succ_apply]
      · simp [hy, Ne.symm hy, traceStep]

private theorem count_map_range (f : ℕ → Plane) (x : Plane) (j : ℕ) :
    ((List.range j).map f).count x = ((Finset.range j).filter fun i => f i = x).card := by
  induction j with
  | zero => simp
  | succ j ih =>
    by_cases h : f j = x <;>
      simp [List.range_succ, Finset.range_add_one, Finset.filter_insert, h, ih]

/-- The finite-list and finite-word departure conventions agree exactly. -/
theorem wordVertices_departures {n : ℕ} (u : Plane) (w : DirectionWord n) (x : Plane) :
    ((wordVertices u w).dropLast).count x = departureCount u w n x := by
  rw [wordVertices, List.range_succ, List.map_append, List.map_singleton,
    List.dropLast_append_cons]
  simp only [List.dropLast_singleton, List.append_nil]
  simpa only [departureCount, min_self] using count_map_range (wordVertex u w) x n

/-- At every genuine prefix, status is determined by previous departures. -/
theorem prefixNetwork_status {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (w : DirectionWord n) (j : ℕ) (hj : j ≤ n) (x : Plane) :
    (prefixNetwork D u w j).status x = advanceStatus^[departureCount u w j x] (D.status x) := by
  unfold prefixNetwork
  rw [traceNetwork_status]
  congr 1
  simp only [wordVertices, ← List.map_take, List.take_range]
  rw [min_eq_left (by omega : j + 1 ≤ n + 1), List.range_succ, List.map_append,
    List.map_singleton, List.dropLast_append_cons]
  simp only [List.dropLast_singleton, List.append_nil]
  simpa only [departureCount, min_eq_left hj] using count_map_range (wordVertex u w) x j

/-- An actual U departure must be a lattice first visit, even for an arbitrary
initial network. Extra initial D sites need not be lattice revisits. -/
theorem U_departure_first_visit {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (w : DirectionWord n) (i : Fin n)
    (hU : (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .U) :
    wordRevisit u w i = false := by
  rw [prefixNetwork_status D u w i.val (by omega)] at hU
  have hzero : departureCount u w i.val (wordVertex u w i.val) = 0 := by
    by_contra h
    exact iterate_advance_ne_U _ (Nat.pos_of_ne_zero h) hU
  simp [wordRevisit, hzero]

/-- Two previous departures have actually removed the site. -/
theorem twice_departed_removed {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (w : DirectionWord n) (j : ℕ) (hj : j ≤ n) (x : Plane)
    (hx : 2 ≤ departureCount u w j x) : (prefixNetwork D u w j).status x = .X := by
  rw [prefixNetwork_status D u w j hj x]
  exact iterate_advance_removed _ hx

/-- The target has not changed its law before its first hit. -/
theorem target_status_unchanged {G : Finset Plane} {n : ℕ} (D : Network G) (u v : Plane)
    (w : DirectionWord n) (hfirst : ∀ j < n, wordVertex u w j ≠ v) :
    (traceNetwork D (wordVertices u w)).status v = D.status v := by
  rw [traceNetwork_status, wordVertices_departures]
  have hc : departureCount u w n v = 0 := by
    simp only [departureCount, min_self, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_range]
    exact hfirst
  simp [hc]

/-- Actual departure counts commute with the same fixed lattice chart. -/
theorem canonicalWord_departureCount (p : PairData) {n : ℕ} (w : DirectionWord n)
    (j : ℕ) (hj : j ≤ n) (x : Plane) :
    departureCount kernelStart (canonicalWord p w) j ((canonicalChart p).point x) =
      departureCount p.u w j x := by
  unfold departureCount
  congr 1
  apply Finset.filter_congr
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [canonicalWord_vertex p w k (by omega)]
  exact (canonicalChart p).point.injective.eq_iff

/-- A true U departure occurs in the canonical first-visit ordering. -/
theorem U_departure_canonical_first_visit (p : PairData) {n : ℕ} (w : DirectionWord n)
    (i : Fin n)
    (hU : (prefixNetwork p.normalized p.u w i.val).status (wordVertex p.u w i.val) = .U) :
    wordRevisit kernelStart (canonicalWord p w) i = false := by
  rw [← canonicalChart_start p]
  change wordRevisit ((canonicalChart p).point p.u) ((canonicalChart p).word w) i = false
  rw [frame_revisit]
  exact U_departure_first_visit _ _ _ _ hU

/-- Kernel-dead sites are actually removed in the trace. Initial removals may
make additional kernel-live sites removed; that direction is deliberately not
asserted. -/
theorem kernel_dead_removed (p : PairData) {n : ℕ} (w : DirectionWord n) (i : Fin n)
    (z : Plane) (hz : deadAt (canonicalWord p w) i z) :
    (prefixNetwork p.normalized p.u w i.val).status ((canonicalChart p).point.symm z) = .X := by
  rcases hz with rfl | hz
  · have hc : (canonicalChart p).point.symm kernelCentre = p.c := by
      apply (canonicalChart p).point.injective
      simp
    rw [hc, prefixNetwork_status _ _ _ i.val (by omega)]
    have hX : p.normalized.status p.c = .X := p.pair.2.2.2.2.1
    rw [hX, iterate_advance_X]
  · apply twice_departed_removed _ _ _ _ (by omega)
    have he := canonicalWord_departureCount p w i.val (by omega)
      ((canonicalChart p).point.symm z)
    rw [Equiv.apply_symm_apply] at he
    omega

/-- Concatenating vertex lists at their shared endpoint multiplies the
mass-free trace coefficients in the actual evolving network. -/
theorem traceCoefficient_concat {G : Finset Plane} (D : Network G)
    (l : List Plane) (x : Plane) (r : List Plane) :
    traceCoefficient D (l ++ x :: r) = traceCoefficient D (l ++ [x]) *
      traceCoefficient (traceNetwork D (l ++ [x])) (x :: r) := by
  induction l generalizing D with
  | nil => simp [traceCoefficient, traceNetwork]
  | cons y l ih =>
    cases l with
    | nil => simp [traceCoefficient, traceNetwork]
    | cons z rest =>
      simpa only [List.cons_append, traceCoefficient, traceNetwork, mul_assoc] using
        congrArg (fun a : ℚ => (if D.status y = .U then 1 / 3 else
          if D.status y = .D then 1 / 5 else 0) * a) (ih (traceStep D y z))

theorem traceCoefficient_nonneg {G : Finset Plane} (D : Network G) (l : List Plane) :
    0 ≤ traceCoefficient D l := by
  induction l generalizing D with
  | nil => norm_num [traceCoefficient]
  | cons y l ih =>
    cases l with
    | nil => norm_num [traceCoefficient]
    | cons z rest =>
      apply mul_nonneg _ (ih (traceStep D y z))
      split_ifs <;> norm_num

private theorem wordVertices_snoc {n : ℕ} (u : Plane) (w : DirectionWord n) (a : Compass) :
    wordVertices u (snoc w a) = wordVertices u w ++ [wordVertex u (snoc w a) (n + 1)] := by
  unfold wordVertices
  rw [List.range_succ, List.map_append, List.map_singleton]
  congr 1
  apply List.map_congr_left
  intro j hj
  exact snoc_vertex u w a j (by have := List.mem_range.mp hj; omega)

private theorem wordVertices_split_last {n : ℕ} (u : Plane) (w : DirectionWord n) :
    wordVertices u w = (List.range n).map (wordVertex u w) ++ [wordVertex u w n] := by
  simp only [wordVertices, List.range_succ, List.map_append, List.map_singleton]

theorem traceCoefficient_snoc {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (w : DirectionWord n) (a : Compass) :
    traceCoefficient D (wordVertices u (snoc w a)) = traceCoefficient D (wordVertices u w) *
      (if (traceNetwork D (wordVertices u w)).status (wordVertex u w n) = .U then 1 / 3
        else if (traceNetwork D (wordVertices u w)).status (wordVertex u w n) = .D
          then 1 / 5 else 0) := by
  rw [wordVertices_snoc, wordVertices_split_last u w, List.append_assoc]
  simpa only [List.singleton_append, traceCoefficient, mul_one, ← wordVertices_split_last] using
    traceCoefficient_concat D ((List.range n).map (wordVertex u w)) (wordVertex u w n)
      [wordVertex u (snoc w a) (n + 1)]

theorem trailBaseWeight_snoc {n : ℕ} (u : Plane) (w : DirectionWord n) (a : Compass) :
    trailBaseWeight u (snoc w a) = trailBaseWeight u w *
      (if 0 < departureCount u w n (wordVertex u w n) then 1 / 5 else 1 / 3) := by
  unfold trailBaseWeight
  rw [Fin.prod_univ_castSucc]
  simp only [snoc_old_revisit]
  congr 1
  simp only [wordRevisit, Fin.val_last, snoc_vertex u w a n le_rfl,
    snoc_departure u w a n le_rfl, decide_eq_true_eq]

/-- Extra initial D sites only lower the base weight. This holds for every
network and word, with no positivity or validity hypothesis on the network. -/
theorem traceCoefficient_le_baseWeight {G : Finset Plane} {n : ℕ} (D : Network G)
    (u : Plane) (w : DirectionWord n) :
    traceCoefficient D (wordVertices u w) ≤ trailBaseWeight u w := by
  induction n with
  | zero => simp [wordVertices, traceCoefficient, trailBaseWeight]
  | succ n ih =>
    rw [← snoc_initWord w, traceCoefficient_snoc, trailBaseWeight_snoc]
    apply mul_le_mul (ih (initWord w)) _ _ (trailBaseWeight_nonneg _ _)
    · by_cases hr : 0 < departureCount u (initWord w) n (wordVertex u (initWord w) n)
      · have hU : (traceNetwork D (wordVertices u (initWord w))).status
            (wordVertex u (initWord w) n) ≠ .U := by
          rw [traceNetwork_status, wordVertices_departures]
          exact iterate_advance_ne_U _ hr
        simp only [hr, ite_true, hU, ite_false]
        split_ifs <;> norm_num
      · simp only [hr, ite_false]
        split_ifs <;> norm_num
    · split_ifs <;> norm_num

end AKLT.W.REC079
