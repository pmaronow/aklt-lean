import AKLT.W.REC082.Geometry

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC082

theorem adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  unfold Adjacent latticeDist at *
  omega

theorem present_symm {G : Finset Plane} {D : Network G} {x y : Plane}
    (h : D.Present x y) : D.Present y x :=
  ⟨h.2.1, h.1, adjacent_symm h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem present_mem_neighbours {G : Finset Plane} {D : Network G} {x y : Plane}
    (h : D.Present x y) : y ∈ D.presentNeighbours x :=
  Finset.mem_filter.mpr ⟨(adjacent_iff_mem_neighbours x y).mp h.2.2.1, h⟩

theorem traceStep_active_subset {G : Finset Plane} (D : Network G) (y o : Plane) :
    (traceStep D y o).active ⊆ D.active := by
  intro x hx
  have hx' : x ∈ G ∧ (traceStep D y o).status x ≠ .X := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨hx'.1, ?_⟩
  by_cases hxy : x = y
  · subst x
    by_cases hU : D.status y = .U
    · simp [hU]
    · simp [traceStep, hU] at hx'
  · simpa [traceStep, Function.update_of_ne hxy] using hx'.2

theorem traceStep_kept_subset {G : Finset Plane} (D : Network G) (y o x : Plane) :
    (traceStep D y o).kept x ⊆ D.kept x := by
  dsimp [traceStep]
  split_ifs <;> simp only [Finset.erase_subset, Finset.Subset.refl]

theorem traceStep_present_mono {G : Finset Plane} (D : Network G) (y o x z : Plane)
    (h : (traceStep D y o).Present x z) : D.Present x z :=
  ⟨traceStep_active_subset D y o h.1, traceStep_active_subset D y o h.2.1,
    h.2.2.1, traceStep_kept_subset D y o x h.2.2.2.1,
    traceStep_kept_subset D y o z h.2.2.2.2⟩

theorem traceStep_not_present {G : Finset Plane} (D : Network G) (y o : Plane) :
    ¬ (traceStep D y o).Present y o := by
  intro h
  have hk := h.2.2.2.1
  simp [traceStep] at hk

theorem traceNetwork_present_mono {G : Finset Plane} (D : Network G) (l : List Plane)
    (x z : Plane) (h : (traceNetwork D l).Present x z) : D.Present x z := by
  induction l generalizing D with
  | nil => exact h
  | cons y rest ih =>
    cases rest with
    | nil => exact h
    | cons o tail =>
      exact traceStep_present_mono D y o x z (ih (traceStep D y o) h)

/-- A traversed bond is absent from every subsequent network. -/
theorem traceNetwork_not_present_edge {G : Finset Plane} (D : Network G) (l : List Plane)
    (i : ℕ) (hi : i + 1 < l.length) :
    ¬ (traceNetwork D l).Present l[i] l[i+1] := by
  induction l generalizing D i with
  | nil => simp at hi
  | cons y rest ih =>
    cases rest with
    | nil => simp at hi
    | cons o tail =>
      cases i with
      | zero =>
        intro h
        exact traceStep_not_present D y o
          (traceNetwork_present_mono (traceStep D y o) (o :: tail) y o h)
      | succ i =>
        have hi' : i + 1 < (o :: tail).length := by simpa using hi
        exact ih (traceStep D y o) i hi'

/-- A site which has not been departed keeps its original law. -/
theorem traceNetwork_status_of_not_departed {G : Finset Plane} (D : Network G)
    (l : List Plane) (v : Plane) (hv : v ∉ l.dropLast) :
    (traceNetwork D l).status v = D.status v := by
  induction l generalizing D with
  | nil => rfl
  | cons y rest ih =>
    cases rest with
    | nil => rfl
    | cons o tail =>
      have hv' : v ≠ y ∧ v ∉ (o :: tail).dropLast := by simpa using hv
      rw [traceNetwork, ih (traceStep D y o) hv'.2]
      simp [traceStep, Function.update_of_ne hv'.1]

theorem wordVertex_zero {n : ℕ} (u : Plane) (w : DirectionWord n) :
    wordVertex u w 0 = u := by simp [wordVertex]

theorem wordVertices_length {n : ℕ} (u : Plane) (w : DirectionWord n) :
    (wordVertices u w).length = n + 1 := by simp [wordVertices]

theorem wordVertices_getElem {n : ℕ} (u : Plane) (w : DirectionWord n)
    (i : ℕ) (hi : i < (wordVertices u w).length) :
    (wordVertices u w)[i] = wordVertex u w i := by simp [wordVertices]

theorem stopped_target_not_departed {G : Finset Plane} {D : Network G}
    {u v : Plane} {n : ℕ} {w : DirectionWord n}
    (hw : StoppedNetworkTrail D u (insert v (protectedSites G)) w) :
    v ∉ (wordVertices u w).dropLast := by
  classical
  have hr : (List.range (n + 1)).dropLast = List.range n := by
    rw [List.range_succ]
    simp
  simp only [wordVertices, ← List.map_dropLast, hr, List.mem_map,
    List.mem_range, not_exists]
  intro j hj
  have h := (hw.2.2.1 j hj.1).1
  exact h (Finset.mem_insert.mpr (Or.inl hj.2))

theorem stopped_target_status {G : Finset Plane} {D : Network G}
    {u v : Plane} {n : ℕ} {w : DirectionWord n}
    (hw : StoppedNetworkTrail D u (insert v (protectedSites G)) w) :
    (traceNetwork D (wordVertices u w)).status v = D.status v :=
  traceNetwork_status_of_not_departed D _ v (stopped_target_not_departed hw)

/-- At a first hit, a target of initial degree at most one is isolated. -/
theorem stopped_target_isolated {G : Finset Plane} {D : Network G}
    {u v : Plane} {n : ℕ} {w : DirectionWord n} (huv : u ≠ v)
    (hdeg : (D.presentNeighbours v).card ≤ 1)
    (hw : StoppedNetworkTrail D u (insert v (protectedSites G)) w)
    (he : wordVertex u w n = v) :
    (traceNetwork D (wordVertices u w)).presentNeighbours v = ∅ := by
  classical
  have hn : 0 < n := by
    by_contra h
    have hz : n = 0 := by omega
    have he0 : wordVertex u w 0 = v := by simpa only [hz] using he
    exact huv ((wordVertex_zero u w).symm.trans he0)
  let q := wordVertex u w (n - 1)
  have hsucc : n - 1 + 1 = n := by omega
  have hp : D.Present q v := by
    have h := hw.2.1 ⟨n - 1, by omega⟩
    simpa only [hsucc, he] using h
  have hq : q ∈ D.presentNeighbours v := present_mem_neighbours (present_symm hp)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hp' := (Finset.mem_filter.mp hz).2
  have hz' : z ∈ D.presentNeighbours v :=
    present_mem_neighbours (traceNetwork_present_mono D _ v z hp')
  have hzq : z = q := Finset.card_le_one.mp hdeg z hz' q hq
  subst z
  have hnot := traceNetwork_not_present_edge D (wordVertices u w) (n - 1)
    (by rw [wordVertices_length]; omega)
  simp only [wordVertices_getElem, hsucc, he] at hnot
  exact hnot (present_symm hp')

end AKLT.W.REC082
