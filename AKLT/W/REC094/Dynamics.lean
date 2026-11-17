module
public import AKLT.W.REC094.TraceAlgebra

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC094

theorem adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  change (y.1 - x.1).natAbs + (y.2 - x.2).natAbs = 1
  rw [← Int.natAbs_neg (y.1 - x.1), ← Int.natAbs_neg (y.2 - x.2)]
  simpa only [Adjacent, latticeDist, neg_sub] using h

theorem adjacent_ne {x y : Plane} (h : Adjacent x y) : x ≠ y := by
  rintro rfl
  norm_num [Adjacent, latticeDist] at h

theorem adjacent_mem_neighbors {x y : Plane} (h : Adjacent x y) : y ∈ neighbors x := by
  have hh : (x.1 - y.1).natAbs + (x.2 - y.2).natAbs = 1 := h
  have hx' := Int.natAbs_eq (x.1 - y.1)
  have hy' := Int.natAbs_eq (x.2 - y.2)
  have hc : y = x + Compass.east.step ∨ y = x + Compass.north.step ∨
      y = x + Compass.west.step ∨ y = x + Compass.south.step := by
    simp only [Compass.step, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
    omega
  rcases hc with rfl | rfl | rfl | rfl <;>
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

theorem present_symm {G : Finset Plane} {D : Network G} {x y : Plane}
    (h : D.Present x y) : D.Present y x :=
  ⟨h.2.1, h.1, adjacent_symm h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem present_mem_neighbors {G : Finset Plane} {D : Network G} {x y : Plane}
    (h : D.Present x y) : y ∈ D.presentNeighbors x :=
  Finset.mem_filter.mpr ⟨adjacent_mem_neighbors h.2.2.1, h⟩

theorem traceStep_active_subset {G : Finset Plane} (D : Network G) (y o : Plane) :
    (traceStep D y o).active ⊆ D.active := by
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxG, hx⟩
  apply Finset.mem_filter.mpr
  refine ⟨hxG, ?_⟩
  by_cases he : x = y
  · subst x
    by_cases hU : D.status y = .U
    · simp [hU]
    · simp [traceStep, hU] at hx
  · simpa [traceStep, he] using hx

theorem traceStep_present_subset {G : Finset Plane} (D : Network G) (y o : Plane)
    {x z : Plane} (h : (traceStep D y o).Present x z) : D.Present x z := by
  refine ⟨traceStep_active_subset D y o h.1, traceStep_active_subset D y o h.2.1,
    h.2.2.1, ?_, ?_⟩
  all_goals
    have hh := h.2.2.2
    dsimp [traceStep] at hh
    split_ifs at hh <;> simp_all

theorem traceStep_neighbors_subset {G : Finset Plane} (D : Network G) (y o x : Plane) :
    (traceStep D y o).presentNeighbors x ⊆ D.presentNeighbors x := by
  intro z hz
  exact present_mem_neighbors (traceStep_present_subset D y o (Finset.mem_filter.mp hz).2)

theorem traceStep_not_present {G : Finset Plane} (D : Network G) (y o : Plane) :
    ¬ (traceStep D y o).Present y o := by
  intro h
  have hh := h.2.2.2.1
  simp [traceStep] at hh

theorem traceStep_neighbors_subset_erase {G : Finset Plane} (D : Network G)
    (y o : Plane) :
    (traceStep D y o).presentNeighbors y ⊆ (D.presentNeighbors y).erase o := by
  intro z hz
  refine Finset.mem_erase.mpr ⟨?_, traceStep_neighbors_subset D y o y hz⟩
  intro he
  apply traceStep_not_present D y o
  simpa only [he] using (Finset.mem_filter.mp hz).2

theorem traceStep_arrival_neighbors_subset_erase {G : Finset Plane} (D : Network G)
    (y o : Plane) :
    (traceStep D y o).presentNeighbors o ⊆ (D.presentNeighbors o).erase y := by
  intro z hz
  refine Finset.mem_erase.mpr ⟨?_, traceStep_neighbors_subset D y o o hz⟩
  intro he
  apply traceStep_not_present D y o
  simpa only [he] using (present_symm (Finset.mem_filter.mp hz).2)

theorem traceStep_auxiliary {G : Finset Plane} {D : Network G} {y o : Plane}
    (hD : D.Auxiliary) (hy : D.AdmissibleStart y) (ho : D.Present y o) :
    (traceStep D y o).Auxiliary := by
  have hne := adjacent_ne ho.2.2.1
  have hom := present_mem_neighbors ho
  have hcard : ((traceStep D y o).presentNeighbors y).card ≤ 2 := by
    have hc := Finset.card_le_card (traceStep_neighbors_subset_erase D y o)
    have he := Finset.card_erase_of_mem hom
    rcases hy.2.2 with ⟨hu, hcU⟩ | ⟨hd, hcD⟩ <;> omega
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      have hxy : x ≠ y := fun he => hx (he ▸ (Finset.mem_filter.mp hy.1).1)
      simpa [traceStep, hxy] using hD.1.1 x hx
    · intro x
      have hk := hD.1.2.1 x
      intro z hz
      dsimp [traceStep] at hz
      split_ifs at hz <;>
        first | exact hk (Finset.mem_of_mem_erase hz) | exact hk hz
    · intro x hx hxD
      by_cases he : x = y
      · subst x; exact hcard
      · have hstatus : D.status x = .D := by simpa [traceStep, he] using hxD
        exact (Finset.card_le_card (traceStep_neighbors_subset D y o x)).trans
          (hD.1.2.2.1 x hx hstatus)
    · intro x hx
      have hc := hD.1.2.2.2 x (traceStep_active_subset D y o hx)
      have hd := Finset.card_le_card (traceStep_neighbors_subset D y o x)
      omega
  · intro x hx
    have he : x ≠ y := fun he => hy.2.1 (he ▸ hx)
    simpa [traceStep, he] using hD.2 x hx

theorem traceStep_arrival_admissible {G : Finset Plane} {D : Network G} {y o : Plane}
    (hD : D.Auxiliary) (ho : D.Present y o) (hprot : o ∉ protectedSites G) :
    (traceStep D y o).AdmissibleStart o := by
  have hne := adjacent_ne ho.2.2.1
  have hos : (traceStep D y o).status o = D.status o := by simp [traceStep, Ne.symm hne]
  have hactive : o ∈ (traceStep D y o).active := by
    simpa only [AKLT.Defs.Network.active, Finset.mem_filter, hos] using ho.2.1
  refine ⟨hactive, hprot, ?_⟩
  have hoG := (Finset.mem_filter.mp ho.2.1).1
  have hostat := (Finset.mem_filter.mp ho.2.1).2
  have hm := present_mem_neighbors (present_symm ho)
  have hc := Finset.card_le_card (traceStep_arrival_neighbors_subset_erase D y o)
  have he := Finset.card_erase_of_mem hm
  cases hs : D.status o with
  | U =>
    left
    refine ⟨hos.trans hs, ?_⟩
    have hb := hD.1.2.2.2 o ho.2.1
    omega
  | D =>
    right
    refine ⟨hos.trans hs, ?_⟩
    have hb := hD.1.2.2.1 o hoG hs
    omega
  | X => exact False.elim (hostat hs)

theorem traceStep_present_of_distinct {G : Finset Plane} {D : Network G}
    {y o x z : Plane} (hy : D.AdmissibleStart y) (ho : D.Present y o)
    (hp : D.Present x z) (hb : ({x, z} : Finset Plane) ≠ {y, o}) :
    (traceStep D y o).Present x z := by
  have hno : ¬ (x = y ∧ z = o) := by
    rintro ⟨rfl, rfl⟩; exact hb rfl
  have hon : ¬ (z = y ∧ x = o) := by
    rintro ⟨rfl, rfl⟩; exact hb (Finset.pair_comm _ _)
  have ha (v t : Plane) (hvt : D.Present v t) (ht : v = y → t ≠ o) :
      v ∈ (traceStep D y o).active := by
    have hvG := (Finset.mem_filter.mp hvt.1).1
    have hvX := (Finset.mem_filter.mp hvt.1).2
    apply Finset.mem_filter.mpr
    refine ⟨hvG, ?_⟩
    by_cases hv : v = y
    · subst v
      rcases hy.2.2 with ⟨hu, _⟩ | ⟨hd, hc⟩
      · simp [traceStep, hu]
      · have hto := Finset.card_le_one_iff.mp hc
          (present_mem_neighbors hvt) (present_mem_neighbors ho)
        exact False.elim (ht rfl hto)
    · simpa [traceStep, hv] using hvX
  refine ⟨ha x z hp (fun hxy hzo => hno ⟨hxy, hzo⟩),
    ha z x (present_symm hp) (fun hzy hxo => hon ⟨hzy, hxo⟩), hp.2.2.1, ?_, ?_⟩
  · dsimp [traceStep]
    split_ifs with hxy hxo
    · exact Finset.mem_erase.mpr ⟨fun hzo => hno ⟨hxy, hzo⟩, hp.2.2.2.1⟩
    · exact Finset.mem_erase.mpr ⟨fun hzy => hon ⟨hzy, hxo⟩, hp.2.2.2.1⟩
    · exact hp.2.2.2.1
  · dsimp [traceStep]
    split_ifs with hzy hzo
    · exact Finset.mem_erase.mpr ⟨fun hxo => hon ⟨hzy, hxo⟩, hp.2.2.2.2⟩
    · exact Finset.mem_erase.mpr ⟨fun hxy => hno ⟨hxy, hzo⟩, hp.2.2.2.2⟩
    · exact hp.2.2.2.2

theorem vertexList_dynamics {G : Finset Plane} {D : Network G}
    (hD : D.Auxiliary) (v : ℕ → Plane) (n : ℕ)
    (hstart : D.AdmissibleStart (v 0))
    (hp : ∀ i < n, D.Present (v i) (v (i + 1)))
    (hprot : ∀ i < n, v i ∉ protectedSites G)
    (hb : ∀ i < n, ∀ j < n,
      ({v i, v (i + 1)} : Finset Plane) = {v j, v (j + 1)} → i = j) :
    ∀ j ≤ n,
      (traceNetwork D (vertexList v j)).Auxiliary ∧
      (j < n → (traceNetwork D (vertexList v j)).AdmissibleStart (v j)) ∧
      ∀ i, j ≤ i → i < n →
        (traceNetwork D (vertexList v j)).Present (v i) (v (i + 1)) := by
  intro j
  induction j with
  | zero =>
    intro _
    change D.Auxiliary ∧ (0 < n → D.AdmissibleStart (v 0)) ∧
      ∀ i, 0 ≤ i → i < n → D.Present (v i) (v (i + 1))
    exact ⟨hD, (fun _ => hstart), (fun i _ hi => hp i hi)⟩
  | succ j ih =>
    intro hj
    have hjn : j < n := by omega
    obtain ⟨haux, hadm, hpres⟩ := ih (by omega)
    have hout := hpres j (by omega) hjn
    rw [traceNetwork_vertexList_succ]
    refine ⟨traceStep_auxiliary haux (hadm hjn) hout, ?_, ?_⟩
    · intro hn
      exact traceStep_arrival_admissible haux hout (hprot (j + 1) hn)
    · intro i hji hin
      apply traceStep_present_of_distinct (hadm hjn) hout (hpres i (by omega) hin)
      intro heq
      have he := hb i hin j hjn heq
      omega

/-- Closure and admissibility along every stopped network trail. -/
theorem trail_dynamics {G : Finset Plane} {n : ℕ} {D : Network G}
    (hD : D.Auxiliary) {u : Plane} (hu : D.AdmissibleStart u)
    {T : Finset Plane} {w : DirectionWord n} (hw : StoppedNetworkTrail D u T w) :
    (∀ j ≤ n, (AKLT.Blueprint.Rec.prefixNetwork D u w j).Auxiliary) ∧
    ∀ i : Fin n,
      (AKLT.Blueprint.Rec.prefixNetwork D u w i.val).AdmissibleStart
        (wordVertex u w i.val) ∧
      (AKLT.Blueprint.Rec.prefixNetwork D u w i.val).Present
        (wordVertex u w i.val) (wordVertex u w (i.val + 1)) := by
  have hs : D.AdmissibleStart (wordVertex u w 0) := by simpa [wordVertex] using hu
  have hpres : ∀ i < n, D.Present (wordVertex u w i) (wordVertex u w (i + 1)) :=
    fun i hi => hw.2.1 ⟨i, hi⟩
  have hprot : ∀ i < n, wordVertex u w i ∉ protectedSites G :=
    fun i hi => (hw.2.2.1 i hi).2
  have hb : ∀ i < n, ∀ j < n,
      ({wordVertex u w i, wordVertex u w (i + 1)} : Finset Plane) =
      {wordVertex u w j, wordVertex u w (j + 1)} → i = j := by
    intro i hi j hj he
    have hf : (⟨i, hi⟩ : Fin n) = ⟨j, hj⟩ := hw.1 he
    exact congrArg Fin.val hf
  have hdyn := vertexList_dynamics hD (wordVertex u w) n hs hpres hprot hb
  constructor
  · intro j hj
    rw [prefixNetwork_eq_vertexList D u w j hj]
    exact (hdyn j hj).1
  · intro i
    rw [prefixNetwork_eq_vertexList D u w i.val (Nat.le_of_lt i.isLt)]
    exact ⟨(hdyn i.val (Nat.le_of_lt i.isLt)).2.1 i.isLt,
      (hdyn i.val (Nat.le_of_lt i.isLt)).2.2 i.val (by omega) i.isLt⟩

#print axioms trail_dynamics

end AKLT.W.REC094
