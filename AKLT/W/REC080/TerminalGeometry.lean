import AKLT.W.REC080.Expansion
import AKLT.W.REC080.Summation

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC080

theorem traceStep_active_subset {G : Finset Plane} (D : Network G) (y o : Plane) :
    (traceStep D y o).active ⊆ D.active := by
  classical
  intro x hx
  obtain ⟨hxG, hxS⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxG, ?_⟩
  by_cases hxy : x = y
  · subst x
    cases h : D.status y <;> simp_all [traceStep]
  · simpa [traceStep, Function.update_of_ne hxy] using hxS

theorem traceStep_kept_subset {G : Finset Plane} (D : Network G) (y o x : Plane) :
    (traceStep D y o).kept x ⊆ D.kept x := by
  classical
  dsimp [traceStep]
  split_ifs <;> first | exact Finset.erase_subset _ _ | exact Finset.Subset.refl _

theorem traceStep_present_subset {G : Finset Plane} (D : Network G) (y o x z : Plane)
    (h : (traceStep D y o).Present x z) : D.Present x z :=
  ⟨traceStep_active_subset D y o h.1, traceStep_active_subset D y o h.2.1,
    h.2.2.1, traceStep_kept_subset D y o x h.2.2.2.1,
    traceStep_kept_subset D y o z h.2.2.2.2⟩

theorem trace_present_subset {G : Finset Plane} (D : Network G) (xs : List Plane)
    (x z : Plane) (h : (traceNetwork D xs).Present x z) : D.Present x z := by
  induction xs generalizing D with
  | nil => exact h
  | cons y ys ih =>
    cases ys with
    | nil => exact h
    | cons o ys =>
      exact traceStep_present_subset D y o x z (ih _ h)

theorem trace_status_of_avoid {G : Finset Plane} (D : Network G) (xs : List Plane)
    (x : Plane) (havoid : ∀ y ∈ xs.dropLast, y ≠ x) :
    (traceNetwork D xs).status x = D.status x := by
  induction xs generalizing D with
  | nil => rfl
  | cons y ys ih =>
    cases ys with
    | nil => rfl
    | cons o ys =>
      have hxy : x ≠ y := (havoid y (by exact List.mem_cons_self)).symm
      change (traceNetwork (traceStep D y o) (o :: ys)).status x = _
      rw [ih (traceStep D y o) (fun z hz => havoid z (List.mem_cons_of_mem y hz))]
      simp [traceStep, Function.update_of_ne hxy]

theorem wordVertices_dropLast {n : ℕ} (u : Plane) (w : DirectionWord n) :
    (wordVertices u w).dropLast = (List.range n).map (wordVertex u w) := by
  rw [wordVertices, List.range_succ, List.map_append]
  exact List.dropLast_concat

theorem stopped_status_protected {G : Finset Plane} {n : ℕ} (D : Network G)
    (u : Plane) (T : Finset Plane) (w : DirectionWord n)
    (hw : StoppedNetworkTrail D u T w) (x : Plane) (hx : x ∈ protectedSites G) :
    (traceNetwork D (wordVertices u w)).status x = D.status x := by
  apply trace_status_of_avoid
  rw [wordVertices_dropLast]
  intro y hy heq
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
  exact (hw.2.2.1 j (List.mem_range.mp hj)).2 (heq ▸ hx)

theorem stopped_status_target {G : Finset Plane} {n : ℕ} (D : Network G)
    (u v : Plane) (w : DirectionWord n)
    (hw : StoppedNetworkTrail D u (insert v (protectedSites G)) w) :
    (traceNetwork D (wordVertices u w)).status v = D.status v := by
  apply trace_status_of_avoid
  rw [wordVertices_dropLast]
  intro y hy heq
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
  exact (hw.2.2.1 j (List.mem_range.mp hj)).1
    (Finset.mem_insert.mpr (Or.inl heq))

theorem trace_append_pair {G : Finset Plane} (D : Network G) (xs : List Plane) (a b : Plane) :
    traceNetwork D (xs ++ [a, b]) = traceStep (traceNetwork D (xs ++ [a])) a b := by
  induction xs generalizing D with
  | nil => rfl
  | cons y ys ih =>
    cases ys with
    | nil => rfl
    | cons o ys =>
      change traceNetwork (traceStep D y o) ((o :: ys) ++ [a, b]) =
        traceStep (traceNetwork (traceStep D y o) ((o :: ys) ++ [a])) a b
      exact ih _

theorem traceStep_arrival_absent {G : Finset Plane} (D : Network G) (a b : Plane) :
    a ∉ (traceStep D a b).kept b := by
  classical
  by_cases h : b = a
  · subst b
    simp [traceStep]
  · simp [traceStep, h]

/-- The final arrival bond has actually been erased at the protected target. -/
theorem trace_last_arrival_absent {G : Finset Plane} (D : Network G) (u : Plane)
    (k : ℕ) (w : DirectionWord (k + 1)) :
    wordVertex u w k ∉ (traceNetwork D (wordVertices u w)).kept (wordVertex u w (k + 1)) := by
  have hxs : wordVertices u w = (List.range k).map (wordVertex u w) ++
      [wordVertex u w k, wordVertex u w (k + 1)] := by
    simp [wordVertices, List.range_succ, List.map_append, List.append_assoc]
  rw [hxs, trace_append_pair]
  exact traceStep_arrival_absent _ _ _

theorem neighbours_card (x : Plane) : (neighbours x).card = 4 := by
  have hi : Function.Injective (fun d : Compass => x + d.step) := by
    intro a b hab
    have h : a.step = b.step := add_left_cancel hab
    cases a <;> cases b <;> simp_all [Compass.step]
  rw [neighbours, Finset.card_image_of_injective _ hi]
  decide

theorem neighbour_of_adjacent {x y : Plane} (h : Adjacent x y) : x ∈ neighbours y := by
  obtain ⟨d, hd⟩ := adjacent_direction h
  exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, hd.symm⟩

theorem removed_neighbour_degree {G : Finset Plane} (D : Network G) (v c : Plane)
    (hvc : Adjacent v c) (hc : D.status c = .X) : (D.presentNeighbours v).card ≤ 3 := by
  classical
  obtain ⟨incoming, hi⟩ := adjacent_direction hvc
  have hcv : c ∈ neighbours v := by
    apply Finset.mem_image.mpr
    refine ⟨incoming.reverse, Finset.mem_univ _, ?_⟩
    rw [reverse_step, hi]
    abel
  have hnot : c ∉ D.presentNeighbours v := by
    intro h
    have hcAct := (Finset.mem_filter.mp h).2.2.1
    exact (Finset.mem_filter.mp hcAct).2 hc
  have hsub : D.presentNeighbours v ⊆ (neighbours v).erase c := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun h => hnot (h ▸ hx), (Finset.mem_filter.mp hx).1⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hcv, neighbours_card] at hcard
  exact hcard

theorem terminal_present (p : PairData) {n : ℕ} (w : DirectionWord n) (x y : Plane) :
    (terminalNetwork p w).Present x y ↔
      (traceNetwork p.normalized (wordVertices p.u w)).Present x y := by
  apply normalize_present
  exact trace_removed p.normalized p.c p.pair.2.2.2.2.1 (wordVertices p.u w)

theorem terminal_neighbours_subset (p : PairData) {n : ℕ} (w : DirectionWord n) (x : Plane) :
    (terminalNetwork p w).presentNeighbours x ⊆ p.D.presentNeighbours x := by
  classical
  intro y hy
  obtain ⟨hneigh, hp⟩ := Finset.mem_filter.mp hy
  refine Finset.mem_filter.mpr ⟨hneigh, ?_⟩
  have hp' := trace_present_subset p.normalized (wordVertices p.u w) x y
    ((terminal_present p w x y).mp hp)
  exact (normalize_present p.D p.u p.c p.pair.2.2.2.2.1 x y).mp hp'

theorem terminal_start_admissible (p : PairData) (hv : p.v ∉ protectedSites p.G)
    {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w) :
    (terminalNetwork p w).AdmissibleStart p.v := by
  have hstat : (terminalNetwork p w).status p.v = p.D.status p.v :=
    stopped_status_target p.normalized p.u p.v w hw
  have hvAct := p.pair.2.2.1
  have hvG : p.v ∈ p.G := (Finset.mem_filter.mp hvAct).1
  have hactive : p.v ∈ (terminalNetwork p w).active := by
    exact Finset.mem_filter.mpr ⟨hvG, by simpa [hstat] using (Finset.mem_filter.mp hvAct).2⟩
  refine ⟨hactive, hv, ?_⟩
  rcases p.pair.2.2.2.2.2.2.2.2.2 with hU | ⟨hD, hdeg⟩
  · exact Or.inl ⟨hstat.trans hU,
      removed_neighbour_degree _ p.v p.c p.pair.2.2.2.2.2.2.1 (terminal_centre_removed p w)⟩
  · exact Or.inr ⟨hstat.trans hD,
      (Finset.card_le_card (terminal_neighbours_subset p w p.v)).trans hdeg⟩

/-- At the first protected terminal, the unchanged U law and the erased
arrival bond give degree at most three, including all original legs. -/
theorem terminal_target_admissible (p : PairData) (hu : p.u ∉ protectedSites p.G)
    {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (he : wordVertex p.u w n ∈ protectedSites p.G) :
    AdmissibleTarget (terminalNetwork p w) (wordVertex p.u w n) := by
  classical
  have hn : n ≠ 0 := by
    intro hn
    subst n
    exact hu (by simpa using he)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let e := wordVertex p.u w (k + 1)
  let a := wordVertex p.u w k
  have heG : e ∈ p.G := (Finset.mem_filter.mp he).1
  have heU : p.D.status e = .U := (p.pair.1.1.2 e he).1
  have hstat : (terminalNetwork p w).status e = .U :=
    (stopped_status_protected p.normalized p.u (insert p.v (protectedSites p.G)) w hw e he).trans heU
  have heActive : e ∈ p.D.active := Finset.mem_filter.mpr ⟨heG, by simp [heU]⟩
  have hbase : (p.D.presentNeighbours e).card +
      ((originalLegs p.G).filter fun t => t.1 = e).card ≤ 4 :=
    p.pair.1.1.1.2.2.2 e heActive
  have harrival : p.normalized.Present a e := hw.2.1 ⟨k, Nat.lt_succ_self k⟩
  have haNeigh : a ∈ neighbours e := neighbour_of_adjacent harrival.2.2.1
  have haBase : a ∈ p.D.presentNeighbours e := by
    apply Finset.mem_filter.mpr
    refine ⟨haNeigh, ?_⟩
    exact (normalize_present p.D p.u p.c p.pair.2.2.2.2.1 e a).mp
      (present_symm p.normalized harrival)
  have haAbsent : a ∉ (terminalNetwork p w).presentNeighbours e := by
    intro h
    have hp := (terminal_present p w e a).mp (Finset.mem_filter.mp h).2
    exact trace_last_arrival_absent p.normalized p.u k w hp.2.2.2.1
  have hsub : (terminalNetwork p w).presentNeighbours e ⊆ (p.D.presentNeighbours e).erase a := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨fun h => haAbsent (h ▸ hx), terminal_neighbours_subset p w e hx⟩
  have hdeg := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem haBase] at hdeg
  have hpos : 0 < (p.D.presentNeighbours e).card := Finset.card_pos.mpr ⟨a, haBase⟩
  refine ⟨Finset.mem_filter.mpr ⟨heG, ?_⟩, Or.inl ⟨hstat, ?_⟩⟩
  · change (terminalNetwork p w).status e ≠ .X
    rw [hstat]
    decide
  · change ((terminalNetwork p w).presentNeighbours e).card +
      ((originalLegs p.G).filter fun t => t.1 = e).card ≤ 3
    omega

end AKLT.W.REC080
