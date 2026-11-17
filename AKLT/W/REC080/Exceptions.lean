module
public import AKLT.W.REC080.TerminalGeometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC080

/-- A U site survives as U precisely when it has never been departed. -/
theorem trace_status_U_iff {G : Finset Plane} (D : Network G) (xs : List Plane) (x : Plane) :
    (traceNetwork D xs).status x = .U ↔ D.status x = .U ∧ x ∉ xs.dropLast := by
  induction xs generalizing D with
  | nil => simp [traceNetwork]
  | cons y ys ih =>
    cases ys with
    | nil => simp [traceNetwork]
    | cons o ys =>
      change (traceNetwork (traceStep D y o) (o :: ys)).status x = .U ↔ _
      rw [ih]
      by_cases hxy : x = y
      · subst x
        cases h : D.status y <;> simp [traceStep, h]
      · simp [traceStep, hxy]

theorem prefix_departures {n : ℕ} (u : Plane) (w : DirectionWord n) (j : ℕ) (hj : j ≤ n) :
    ((wordVertices u w).take (j + 1)).dropLast = (List.range j).map (wordVertex u w) := by
  rw [List.dropLast_take_eq_take_dropLast, Nat.add_sub_cancel,
    wordVertices_dropLast, ← List.map_take, List.take_range, Nat.min_eq_left hj]

/-- No trail, degree or auxiliary premise is required for uniqueness of
U departures: it follows solely from the U-to-D-to-X update. -/
theorem u_departure_injective {G : Finset Plane} (D : Network G) (u : Plane)
    {n : ℕ} (w : DirectionWord n) (i j : Fin n)
    (hi : (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .U)
    (hj : (prefixNetwork D u w j.val).status (wordVertex u w j.val) = .U)
    (heq : wordVertex u w i.val = wordVertex u w j.val) : i = j := by
  have hnot (k : Fin n)
      (hk : (prefixNetwork D u w k.val).status (wordVertex u w k.val) = .U) :
      wordVertex u w k.val ∉ (List.range k.val).map (wordVertex u w) := by
    have h := (trace_status_U_iff D ((wordVertices u w).take (k.val + 1))
      (wordVertex u w k.val)).mp hk
    rw [prefix_departures u w k.val (Nat.le_of_lt k.isLt)] at h
    exact h.2
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with hlt | he | hgt
  · exact False.elim (hnot j hj (List.mem_map.mpr
      ⟨i.val, List.mem_range.mpr hlt, heq⟩))
  · exact he
  · exact False.elim (hnot i hi (List.mem_map.mpr
      ⟨j.val, List.mem_range.mpr hgt, heq.symm⟩))

theorem diamond_twelve (e : Plane) :
    ((square e 2).filter fun z => 0 < latticeDist z e ∧ latticeDist z e ≤ 2).card = 12 := by
  classical
  have hsq (z : Plane) : z ∈ square e 2 ↔ z - e ∈ square (0, 0) 2 := by
    simp [square, Prod.fst_sub, Prod.snd_sub]
    omega
  have hdist (z : Plane) : latticeDist (z - e) (0, 0) = latticeDist z e := by
    simp [latticeDist, Prod.fst_sub, Prod.snd_sub]
  calc
    _ = ((square (0, 0) 2).filter fun z =>
        0 < latticeDist z (0, 0) ∧ latticeDist z (0, 0) ≤ 2).card := by
      apply Finset.card_bij (fun z _ => z - e)
      · intro z hz
        obtain ⟨hzsq, hzd⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨(hsq z).mp hzsq, by simpa [hdist] using hzd⟩
      · intro x _ y _ hxy
        simpa using congrArg (fun z : Plane => z + e) hxy
      · intro z hz
        refine ⟨z + e, ?_, by abel⟩
        obtain ⟨hzsq, hzd⟩ := Finset.mem_filter.mp hz
        apply Finset.mem_filter.mpr
        refine ⟨(hsq (z + e)).mpr (by simpa using hzsq), ?_⟩
        simpa [← hdist (z + e)] using hzd
    _ = 12 := by decide +kernel

/-- Inject all exceptional U indices, wherever they occur, into the twelve
sites of the punctured radius-two diamond. Only the location premise remains. -/
theorem uncoveredCount_le_twelve_of_location {G : Finset Plane} (D : Network G)
    (u e : Plane) (incoming : Compass) {n : ℕ} (w : DirectionWord n)
    (hloc : ∀ i : Fin n,
      (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .U →
      ¬ AKLT.Blueprint.Rec.CoveredDepartureV2 (prefixNetwork D u w i.val) (wordVertex u w i.val)
        (wordIncoming incoming w i) (w i) →
      0 < latticeDist (wordVertex u w i.val) e ∧
        latticeDist (wordVertex u w i.val) e ≤ 2) :
    uncoveredCount D u incoming w ≤ 12 := by
  classical
  rw [← diamond_twelve e]
  apply Finset.card_le_card_of_injOn (fun i : Fin n => wordVertex u w i.val)
  · intro i hi
    obtain ⟨hiU, hiBad⟩ := (Finset.mem_filter.mp hi).2
    have hd := hloc i hiU hiBad
    refine Finset.mem_filter.mpr ⟨?_, hd⟩
    norm_num [square]
    unfold latticeDist at hd
    omega
  · intro i hi j hj heq
    exact u_departure_injective D u w i j (Finset.mem_filter.mp hi).2.1
      (Finset.mem_filter.mp hj).2.1 heq

end AKLT.W.REC080
