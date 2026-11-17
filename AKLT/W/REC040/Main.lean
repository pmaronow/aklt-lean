module
public import AKLT.Blueprint.Rec.NodesWalk

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Rec

namespace AKLT.W.REC040

lemma adjacent_mem_neighbours {x y : Plane} (h : Adjacent x y) : y ∈ neighbours x := by
  have hsum : (x.1 - y.1).natAbs + (x.2 - y.2).natAbs = 1 := h
  have hcases : ((x.1 - y.1).natAbs = 1 ∧ (x.2 - y.2).natAbs = 0) ∨
      ((x.1 - y.1).natAbs = 0 ∧ (x.2 - y.2).natAbs = 1) := by omega
  have hzero {z : ℤ} (hz : z.natAbs = 0) : z = 0 := by
    have hs : z * z = 0 := by
      have h' : z.natAbs = Int.natAbs (0 : ℤ) := by
        simpa only [Int.natAbs_zero] using hz
      have := (Int.natAbs_eq_iff_sq_eq).mp h'
      norm_num at this ⊢
      exact this
    nlinarith
  have hone {z : ℤ} (hz : z.natAbs = 1) : z = 1 ∨ z = -1 := by
    have hs : z ^ 2 = 1 := by
      have h' : z.natAbs = Int.natAbs (1 : ℤ) := by
        simpa only [Int.natAbs_one] using hz
      simpa using (Int.natAbs_eq_iff_sq_eq).mp h'
    by_cases hn : z < 0
    · right
      nlinarith
    · left
      nlinarith
  rcases hcases with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hdx := hone hx
    have hdy := hzero hy
    rcases hdx with hdx | hdx
    · have hpt : y = x + Compass.west.step := by
        rcases x with ⟨a,b⟩
        rcases y with ⟨c,d⟩
        simp [Compass.step]
        omega
      rw [hpt]
      change x + Compass.west.step ∈ Finset.univ.image (fun d : Compass => x + d.step)
      refine Finset.mem_image.mpr ⟨.west, Finset.mem_univ _, ?_⟩
      rfl
    · have hpt : y = x + Compass.east.step := by
        rcases x with ⟨a,b⟩
        rcases y with ⟨c,d⟩
        simp [Compass.step]
        omega
      rw [hpt]
      change x + Compass.east.step ∈ Finset.univ.image (fun d : Compass => x + d.step)
      refine Finset.mem_image.mpr ⟨.east, Finset.mem_univ _, ?_⟩
      rfl
  · have hdx := hzero hx
    have hdy := hone hy
    rcases hdy with hdy | hdy
    · have hpt : y = x + Compass.south.step := by
        rcases x with ⟨a,b⟩
        rcases y with ⟨c,d⟩
        simp [Compass.step]
        omega
      rw [hpt]
      change x + Compass.south.step ∈ Finset.univ.image (fun d : Compass => x + d.step)
      refine Finset.mem_image.mpr ⟨.south, Finset.mem_univ _, ?_⟩
      rfl
    · have hpt : y = x + Compass.north.step := by
        rcases x with ⟨a,b⟩
        rcases y with ⟨c,d⟩
        simp [Compass.step]
        omega
      rw [hpt]
      change x + Compass.north.step ∈ Finset.univ.image (fun d : Compass => x + d.step)
      refine Finset.mem_image.mpr ⟨.north, Finset.mem_univ _, ?_⟩
      rfl

lemma adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  have h1 : (y.1 - x.1).natAbs = (x.1 - y.1).natAbs := by
    rw [show y.1 - x.1 = -(x.1 - y.1) by omega, Int.natAbs_neg]
  have h2 : (y.2 - x.2).natAbs = (x.2 - y.2).natAbs := by
    rw [show y.2 - x.2 = -(x.2 - y.2) by omega, Int.natAbs_neg]
  change latticeDist y x = 1
  unfold latticeDist
  rw [h1, h2]
  exact h

lemma present_symm {G : Finset Plane} (D : Network G) {x y : Plane}
    (h : D.Present x y) : D.Present y x := by
  exact ⟨h.2.1, h.1, adjacent_symm h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

lemma present_mem_neighbours {G : Finset Plane} (D : Network G) {x y : Plane}
    (h : D.Present x y) : y ∈ D.presentNeighbours x := by
  exact Finset.mem_filter.mpr ⟨adjacent_mem_neighbours h.2.2.1, h⟩

def tailWord {n : ℕ} (w : DirectionWord (n + 1)) : DirectionWord n :=
  fun i => w i.succ

theorem wordVertex_zero {n : ℕ} (u : Plane) (w : DirectionWord n) :
    wordVertex u w 0 = u := by
  simp [wordVertex]

theorem wordVertex_succ {n : ℕ} (u : Plane) (w : DirectionWord (n + 1)) (j : ℕ) :
    wordVertex u w (j + 1) =
      wordVertex (wordVertex u w 1) (tailWord w) j := by
  simp only [wordVertex, tailWord]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ]
  have hsum : (∑ i : Fin n, (if 1 + i.val < j + 1 then (w i.succ).step else 0)) =
      ∑ i : Fin n, (if i.val < j then (w i.succ).step else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : 1 + i.val < j + 1
    · have h' : i.val < j := by omega
      simp [h, h']
    · have h' : ¬ i.val < j := by omega
      simp [h, h']
  have hzero : (∑ i : Fin n, (if 1 + i.val < 1 then (w i.succ).step else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have h : ¬ 1 + i.val < 1 := by omega
    simp [h]
  simp [hsum, hzero]
  abel

theorem wordVertices_cons {n : ℕ} (u : Plane) (w : DirectionWord (n + 1)) :
    wordVertices u w = u :: wordVertices (wordVertex u w 1) (tailWord w) := by
  unfold wordVertices
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Function.comp_apply, wordVertex_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  change wordVertex u w (i + 1) = wordVertex (wordVertex u w 1) (tailWord w) i
  exact wordVertex_succ u w i

theorem wordBond_tail_eq {n : ℕ} (u : Plane) (w : DirectionWord (n + 1)) (i : Fin n) :
    wordBond u w i.succ = wordBond (wordVertex u w 1) (tailWord w) i := by
  have h0 : wordVertex u w (i.val + 1) =
      wordVertex (wordVertex u w 1) (tailWord w) i.val := by
    simpa using wordVertex_succ u w i.val
  have h1 : wordVertex u w (i.val + 1 + 1) =
      wordVertex (wordVertex u w 1) (tailWord w) (i.val + 1) := by
    simpa using wordVertex_succ u w (i.val + 1)
  simp [wordBond, h0, h1]

def traceDCount {G : Finset Plane} (D : Network G) : List Plane → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: rest =>
      (if D.status x = .D then 1 else 0) +
        traceDCount (traceStep D x y) (y :: rest)

def TraceGood {G : Finset Plane} (D : Network G) : List Plane → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest =>
      (D.status x = .U ∨ D.status x = .D) ∧
        TraceGood (traceStep D x y) (y :: rest)

lemma traceStep_present_old {G : Finset Plane} (D : Network G) (y o x z : Plane)
    (h : (traceStep D y o).Present x z) : D.Present x z := by
  rcases h with ⟨hx, hz, hadj, hzx, hxz⟩
  have activeOld (a : Plane) (ha : a ∈ (traceStep D y o).active) : a ∈ D.active := by
    rcases Finset.mem_filter.mp ha with ⟨hag, hast⟩
    apply Finset.mem_filter.mpr
    refine ⟨hag, ?_⟩
    by_cases hay : a = y
    · subst a
      simp [traceStep] at hast ⊢
      cases hsy : D.status y <;> simp_all [traceStep]
    · simpa [traceStep, hay] using hast
  have keptOld (a b : Plane) (hk : b ∈ (traceStep D y o).kept a) : b ∈ D.kept a := by
    by_cases hay : a = y
    · subst a
      simp only [traceStep, if_pos rfl] at hk
      exact (Finset.mem_erase.mp hk).2
    · by_cases hao : a = o
      · subst a
        simp only [traceStep, if_neg hay, if_pos rfl] at hk
        exact (Finset.mem_erase.mp hk).2
      · simpa [traceStep, hay, hao] using hk
  exact ⟨activeOld x hx, activeOld z hz, hadj, keptOld x z hzx, keptOld z x hxz⟩

lemma traceStep_neighbours_subset {G : Finset Plane} (D : Network G) (y o x : Plane) :
    (traceStep D y o).presentNeighbours x ⊆ D.presentNeighbours x := by
  intro z hz
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
    traceStep_present_old D y o x z (Finset.mem_filter.mp hz).2⟩

lemma traceStep_active_subset {G : Finset Plane} (D : Network G) (y o : Plane) :
    (traceStep D y o).active ⊆ D.active := by
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxG, hxstatus⟩
  apply Finset.mem_filter.mpr
  refine ⟨hxG, ?_⟩
  by_cases hxy : x = y
  · subst x
    simp [traceStep] at hxstatus ⊢
    cases hs : D.status y <;> simp_all [traceStep]
  · simpa [traceStep, hxy] using hxstatus

lemma traceStep_kept_subset {G : Finset Plane} (D : Network G) (y o x : Plane) :
    (traceStep D y o).kept x ⊆ D.kept x := by
  intro z hz
  by_cases hxy : x = y
  · subst x
    simp only [traceStep, if_pos rfl] at hz
    exact (Finset.mem_erase.mp hz).2
  · by_cases hxo : x = o
    · subst x
      simp only [traceStep, if_neg hxy, if_pos rfl] at hz
      exact (Finset.mem_erase.mp hz).2
    · simpa [traceStep, hxy, hxo] using hz

lemma traceStep_outgoing_not_present {G : Finset Plane} (D : Network G) (y o : Plane)
    (hyo : y ≠ o) : ¬ (traceStep D y o).Present y o := by
  intro h
  rcases h with ⟨_, _, _, ho, _⟩
  have ho' : o ∈ (D.kept y).erase o := by
    simpa [traceStep, hyo] using ho
  exact (Finset.mem_erase.mp ho').1 rfl

lemma traceStep_departure_neighbours_subset_erase {G : Finset Plane} (D : Network G)
    (y o : Plane) (hp : D.Present y o) :
    (traceStep D y o).presentNeighbours y ⊆ (D.presentNeighbours y).erase o := by
  rcases hp with ⟨_, _, hadj, _, _⟩
  have hyo : y ≠ o := by
    intro h
    subst o
    simp [Adjacent, latticeDist] at hadj
  intro z hz
  have hz' := Finset.mem_filter.mp hz
  have hne : z ≠ o := by
    intro h
    subst z
    exact traceStep_outgoing_not_present D y o hyo hz'.2
  refine Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨hz'.1, ?_⟩⟩
  exact traceStep_present_old D y o y z hz'.2

lemma traceStep_arrival_neighbours_subset_erase {G : Finset Plane} (D : Network G)
    (y o : Plane) (hp : D.Present y o) :
    (traceStep D y o).presentNeighbours o ⊆ (D.presentNeighbours o).erase y := by
  rcases hp with ⟨_, _, hadj, _, _⟩
  have hyo : y ≠ o := by
    intro h
    subst o
    simp [Adjacent, latticeDist] at hadj
  intro z hz
  have hz' := Finset.mem_filter.mp hz
  have hne : z ≠ y := by
    intro h
    subst z
    have hnot : ¬ (traceStep D y o).Present o y := by
      intro hp'
      rcases hp' with ⟨_, _, _, hy, _⟩
      have hy' : y ∈ (D.kept o).erase y := by
        simpa [traceStep, hyo.symm] using hy
      exact (Finset.mem_erase.mp hy').1 rfl
    exact hnot hz'.2
  refine Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨hz'.1, ?_⟩⟩
  exact traceStep_present_old D y o o z hz'.2

lemma traceStep_auxiliary {G : Finset Plane} (D : Network G) (y o : Plane)
    (hAux : D.Auxiliary) (hstart : D.AdmissibleStart y) (hp : D.Present y o)
    (hyProtected : y ∉ protectedSites G) : (traceStep D y o).Auxiliary := by
  rcases hAux with ⟨⟨houtside, hkept, hDdegree, hdegree⟩, hprotected⟩
  rcases hstart with ⟨hyactive, _, hstartStatus⟩
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hxG
      by_cases hxy : x = y
      · subst x
        exact False.elim (hxG (Finset.mem_filter.mp hyactive).1)
      · simpa [traceStep, hxy] using houtside x hxG
    · intro x z hz
      exact hkept x (traceStep_kept_subset D y o x hz)
    · intro x hx hDx
      by_cases hxy : x = y
      · subst x
        have hU : D.status y = .U := by
          by_cases h : D.status y = .U
          · exact h
          · simp [traceStep, h] at hDx
        have hdegStart : (D.presentNeighbours y).card ≤ 3 := by
          rcases hstartStatus with ⟨hu, hdeg⟩ | ⟨hd, hdeg⟩
          · exact hdeg
          · rw [hU] at hd
            contradiction
        have ho : o ∈ D.presentNeighbours y := by
          have hadj : Adjacent y o := hp.2.2.1
          exact Finset.mem_filter.mpr ⟨adjacent_mem_neighbours hadj, hp⟩
        have hcard : ((traceStep D y o).presentNeighbours y).card ≤
            (D.presentNeighbours y).card - 1 := by
          calc
            _ ≤ ((D.presentNeighbours y).erase o).card :=
              Finset.card_le_card (traceStep_departure_neighbours_subset_erase D y o hp)
            _ = _ := Finset.card_erase_of_mem ho
        omega
      · have hDxOld : D.status x = .D := by
          simpa [traceStep, hxy] using hDx
        have hxOld : x ∈ D.active := by
          exact Finset.mem_filter.mpr ⟨hx, by simp [hDxOld]⟩
        have hbound := hDdegree x hx hDxOld
        have hcard := Finset.card_le_card (traceStep_neighbours_subset D y o x)
        omega
    · intro x hx
      have hxOld : x ∈ D.active := traceStep_active_subset D y o hx
      have hbound := hdegree x hxOld
      have hcard := Finset.card_le_card (traceStep_neighbours_subset D y o x)
      omega
  · intro x hx
    have hxy : x ≠ y := by
      intro h
      subst x
      exact hyProtected hx
    simpa [traceStep, hxy] using hprotected x hx

lemma traceStep_next_admissible {G : Finset Plane} (D : Network G) (y o : Plane)
    (hAux : D.Auxiliary) (hp : D.Present y o) (hoProtected : o ∉ protectedSites G) :
    (traceStep D y o).AdmissibleStart o := by
  rcases hAux with ⟨⟨_, _, hDdegree, hdegree⟩, _⟩
  have hyo : y ≠ o := by
    intro h
    subst o
    have hadj := hp.2.2.1
    simp [Adjacent, latticeDist] at hadj
  have hoOld : o ∈ D.active := hp.2.1
  have hoNew : o ∈ (traceStep D y o).active := by
    rcases Finset.mem_filter.mp hoOld with ⟨hoG, hos⟩
    apply Finset.mem_filter.mpr
    refine ⟨hoG, ?_⟩
    simpa [traceStep, hyo.symm] using hos
  have hoStatus : (traceStep D y o).status o = D.status o := by
    simp [traceStep, hyo.symm]
  have hyNeighbor : y ∈ D.presentNeighbours o := by
    have hadjSymm : Adjacent o y := by
      have h1 : (o.1 - y.1).natAbs = (y.1 - o.1).natAbs := by
        rw [show o.1 - y.1 = -(y.1 - o.1) by omega, Int.natAbs_neg]
      have h2 : (o.2 - y.2).natAbs = (y.2 - o.2).natAbs := by
        rw [show o.2 - y.2 = -(y.2 - o.2) by omega, Int.natAbs_neg]
      change latticeDist o y = 1
      unfold latticeDist
      rw [h1, h2]
      exact hp.2.2.1
    have hpSymm : D.Present o y :=
      ⟨hp.2.1, hp.1, hadjSymm, hp.2.2.2.2, hp.2.2.2.1⟩
    exact Finset.mem_filter.mpr ⟨adjacent_mem_neighbours hadjSymm, hpSymm⟩
  have hcard : ((traceStep D y o).presentNeighbours o).card ≤
      (D.presentNeighbours o).card - 1 := by
    calc
      _ ≤ ((D.presentNeighbours o).erase y).card :=
        Finset.card_le_card (traceStep_arrival_neighbours_subset_erase D y o hp)
      _ = _ := Finset.card_erase_of_mem hyNeighbor
  have hstatusOld : D.status o ≠ .X := (Finset.mem_filter.mp hoOld).2
  have hcases : D.status o = .U ∨ D.status o = .D := by
    cases hs : D.status o <;> simp_all
  refine ⟨hoNew, hoProtected, ?_⟩
  rcases hcases with hU | hD
  · left
    refine ⟨?_, ?_⟩
    · simpa [hoStatus] using hU
    · have htotal := hdegree o hoOld
      omega
  · right
    refine ⟨?_, ?_⟩
    · simpa [hoStatus] using hD
    · have hbound := hDdegree o (Finset.mem_filter.mp hoOld).1 hD
      omega

lemma traceStep_future_present {G : Finset Plane} (D : Network G) (y o a b : Plane)
    (hstart : D.AdmissibleStart y) (hout : D.Present y o) (hab : D.Present a b)
    (hbond : ({a, b} : Finset Plane) ≠ {y, o}) :
    (traceStep D y o).Present a b := by
  rcases hstart with ⟨_, _, hstartStatus⟩
  have hyo : y ≠ o := by
    intro h
    subst o
    have hadj := hout.2.2.1
    simp [Adjacent, latticeDist] at hadj
  have hya : a = y → b ≠ o := by
    intro ha hb
    subst a
    subst b
    exact hbond rfl
  have hyo' : a = o → b ≠ y := by
    intro ha hb
    subst a
    subst b
    apply hbond
    ext z
    simp [or_comm]
  have hyb : b = y → a ≠ o := by
    intro hb ha
    subst b
    subst a
    apply hbond
    ext z
    simp [or_comm]
  have hob : b = o → a ≠ y := by
    intro hb ha
    subst b
    subst a
    exact hbond rfl
  have hNoY : D.status y = .D → a ≠ y ∧ b ≠ y := by
    intro hD
    have hdegree : (D.presentNeighbours y).card ≤ 1 := by
      rcases hstartStatus with ⟨hU, _⟩ | ⟨_, hdeg⟩
      · rw [hD] at hU
        contradiction
      · exact hdeg
    have ho : o ∈ D.presentNeighbours y := present_mem_neighbours D hout
    constructor
    · intro ha
      subst a
      have hb : b ∈ D.presentNeighbours y := present_mem_neighbours D hab
      have hne : b ≠ o := hya rfl
      have hsub : ({o, b} : Finset Plane) ⊆ D.presentNeighbours y := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact ho
        · exact hb
      have hcard := Finset.card_le_card hsub
      have hpair : ({o, b} : Finset Plane).card = 2 := Finset.card_pair hne.symm
      rw [hpair] at hcard
      omega
    · intro hbEq
      subst b
      have haMem : a ∈ D.presentNeighbours y :=
        present_mem_neighbours D (present_symm D hab)
      have hne : a ≠ o := hyb rfl
      have hsub : ({o, a} : Finset Plane) ⊆ D.presentNeighbours y := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact ho
        · exact haMem
      have hcard := Finset.card_le_card hsub
      have hpair : ({o, a} : Finset Plane).card = 2 := Finset.card_pair hne.symm
      rw [hpair] at hcard
      omega
  have hkeepAfter (x z : Plane) (hkeep : z ∈ D.kept x)
      (hneOut : x = y → z ≠ o) (hneIn : x = o → z ≠ y) :
      z ∈ (traceStep D y o).kept x := by
    by_cases hxy : x = y
    · subst x
      have hmem : z ∈ (D.kept y).erase o := Finset.mem_erase.mpr ⟨hneOut rfl, hkeep⟩
      simpa [traceStep] using hmem
    · by_cases hxo : x = o
      · subst x
        simpa [traceStep, hxy] using Finset.mem_erase.mpr ⟨hneIn rfl, hkeep⟩
      · simpa [traceStep, hxy, hxo] using hkeep
  have hstatusU : D.status y = .U ∨ D.status y = .D := by
    rcases hstartStatus with ⟨hU, _⟩ | ⟨hD, _⟩
    · exact Or.inl hU
    · exact Or.inr hD
  have hAna : a ≠ y ∨ D.status y = .U := by
    rcases hstatusU with hU | hD
    · exact Or.inr hU
    · exact Or.inl (hNoY hD).1
  have hBnb : b ≠ y ∨ D.status y = .U := by
    rcases hstatusU with hU | hD
    · exact Or.inr hU
    · exact Or.inl (hNoY hD).2
  have hactiveAfter (x : Plane) (hx : x ∈ D.active)
      (hxy : x = y → D.status y = .U) : x ∈ (traceStep D y o).active := by
    rcases Finset.mem_filter.mp hx with ⟨hxG, hxs⟩
    apply Finset.mem_filter.mpr
    refine ⟨hxG, ?_⟩
    by_cases hxy' : x = y
    · subst x
      have hU := hxy rfl
      simpa [traceStep, hU]
    · simpa [traceStep, hxy'] using hxs
  have haNew : a ∈ (traceStep D y o).active := hactiveAfter a hab.1 (by
    intro ha
    subst a
    rcases hAna with hne | hU
    · exact False.elim (hne rfl)
    · exact hU)
  have hbNew : b ∈ (traceStep D y o).active := hactiveAfter b hab.2.1 (by
    intro hb
    subst b
    rcases hBnb with hne | hU
    · exact False.elim (hne rfl)
    · exact hU)
  refine ⟨haNew, hbNew, hab.2.2.1,
    hkeepAfter a b hab.2.2.2.1 hya hyo',
    hkeepAfter b a hab.2.2.2.2 hyb hob⟩

theorem traceCoefficient_eq_count {G : Finset Plane} (D : Network G) (l : List Plane)
    (hgood : TraceGood D l) :
    traceCoefficient D l = (1 / 3 : ℚ) ^ (l.length - 1) *
      (3 / 5 : ℚ) ^ traceDCount D l := by
  induction l generalizing D with
  | nil => simp [traceCoefficient, traceDCount]
  | cons x xs ih =>
      cases xs with
      | nil => simp [traceCoefficient, traceDCount]
      | cons y rest =>
          simp only [TraceGood] at hgood
          rcases hgood with ⟨hstatus, htail⟩
          rcases hstatus with hu | hd
          · simp only [traceCoefficient, traceDCount, hu, if_true, if_false]
            rw [ih (D := traceStep D x y) htail]
            norm_num [pow_succ]
            ring
          · simp only [traceCoefficient, traceDCount, hd, if_false, if_true]
            rw [ih (D := traceStep D x y) htail]
            norm_num [pow_succ]
            ring

def listPrefixDCount {G : Finset Plane} (D : Network G) (l : List Plane) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    (traceNetwork D (l.take (i.val + 1))).status (l.getD i.val (0, 0)) = .D).card

lemma listPrefixDCount_cons_cons {G : Finset Plane} (D : Network G) (x y : Plane)
    (rest : List Plane) :
    listPrefixDCount D (x :: y :: rest) (rest.length + 1) =
      (if D.status x = .D then 1 else 0) +
        listPrefixDCount (traceStep D x y) (y :: rest) rest.length := by
  classical
  unfold listPrefixDCount
  rw [Finset.card_filter, Finset.card_filter]
  simp only [Fin.sum_univ_succ]
  congr 1

theorem traceDCount_eq_listPrefixDCount {G : Finset Plane} (D : Network G)
    (l : List Plane) :
    traceDCount D l = listPrefixDCount D l (l.length - 1) := by
  induction l generalizing D with
  | nil => simp [traceDCount, listPrefixDCount]
  | cons x xs ih =>
      cases xs with
      | nil => simp [traceDCount, listPrefixDCount]
      | cons y rest =>
          classical
          change traceDCount D (x :: y :: rest) =
            listPrefixDCount D (x :: y :: rest) (rest.length + 1)
          rw [traceDCount, listPrefixDCount_cons_cons]
          have ht : traceDCount (traceStep D x y) (y :: rest) =
              listPrefixDCount (traceStep D x y) (y :: rest) rest.length := by
            simpa [List.length_cons] using ih (D := traceStep D x y)
          rw [ht]

theorem listPrefixDCount_wordVertices {G : Finset Plane} (D : Network G)
    (u : Plane) {n : ℕ} (w : DirectionWord n) :
    listPrefixDCount D (wordVertices u w) n =
      (Finset.univ.filter fun i : Fin n =>
        (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .D).card := by
  classical
  simp [listPrefixDCount, prefixNetwork, wordVertices, List.getD]
  rfl

lemma stoppedNetworkTrail_tail {G : Finset Plane} {n : ℕ}
    (D : Network G) (u : Plane) (T : Finset Plane) (w : DirectionWord (n + 1))
    (hstart : D.AdmissibleStart u)
    (htrail : StoppedNetworkTrail D u T w) :
    StoppedNetworkTrail (traceStep D u (wordVertex u w 1))
      (wordVertex u w 1) T (tailWord w) := by
  rcases htrail with ⟨hinj, hpresent, hstop, hterminal⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    have hEq : wordBond u w i.succ = wordBond u w j.succ := by
      rw [wordBond_tail_eq, wordBond_tail_eq]
      exact hij
    have hidx := hinj hEq
    have hval := congrArg Fin.val hidx
    simp only [Fin.val_succ] at hval
    change i.val = j.val
    omega
  · intro i
    have hfirst : D.Present u (wordVertex u w 1) := by
      simpa [wordVertex_zero] using hpresent ⟨0, by omega⟩
    have hnext : D.Present (wordVertex u w (i.val + 1))
        (wordVertex u w (i.val + 2)) := by
      simpa using hpresent i.succ
    have hbond₀ : wordBond u w 0 ≠ wordBond u w i.succ := by
      intro heq
      have hidx := hinj heq
      have hval := congrArg Fin.val hidx
      simp at hval
    have hdistinct :
        ({wordVertex u w (i.val + 1), wordVertex u w (i.val + 2)} : Finset Plane) ≠
          {u, wordVertex u w 1} := by
      simpa [wordBond, wordVertex_zero] using hbond₀.symm
    have hfuture := traceStep_future_present D u (wordVertex u w 1)
      (wordVertex u w (i.val + 1)) (wordVertex u w (i.val + 2))
      hstart hfirst hnext hdistinct
    rw [← wordVertex_succ u w i.val, ← wordVertex_succ u w (i.val + 1)]
    exact hfuture
  · intro j hj
    have h := hstop (j + 1) (by omega)
    have hvertex := wordVertex_succ u w j
    constructor
    · rw [← hvertex]
      exact h.1
    · rw [← hvertex]
      exact h.2
  · rw [← wordVertex_succ u w n]
    exact hterminal

theorem traceGood_of_stopped {G : Finset Plane} :
    ∀ (D : Network G) (u : Plane) (T : Finset Plane) (n : ℕ)
      (w : DirectionWord n), D.Auxiliary → D.AdmissibleStart u →
      StoppedNetworkTrail D u T w → TraceGood D (wordVertices u w) := by
  intro D u T n
  induction n generalizing D u T with
  | zero =>
      intro w hAux hstart htrail
      simp [wordVertices, wordVertex_zero, TraceGood]
  | succ n ih =>
      cases n with
      | zero =>
          intro w hAux hstart htrail
          have hstatus : D.status u = .U ∨ D.status u = .D := by
            rcases hstart.2.2 with hU | hD
            · exact Or.inl hU.1
            · exact Or.inr hD.1
          rw [wordVertices_cons]
          simp only [wordVertices, wordVertex_zero, List.range_succ,
            List.range_zero, List.nil_append, List.map_singleton]
          change (D.status u = .U ∨ D.status u = .D) ∧ True
          exact ⟨hstatus, trivial⟩
      | succ n =>
          intro w hAux hstart htrail
          let v := wordVertex u w 1
          have hfirst : D.Present u v := by
            have h := htrail.2.1 ⟨0, by omega⟩
            simpa [v, wordVertex_zero] using h
          have hnotProtected : v ∉ protectedSites G := by
            have h := htrail.2.2.1 1 (by omega)
            exact h.2
          have hAux' := traceStep_auxiliary D u v hAux hstart hfirst hstart.2.1
          have hstart' := traceStep_next_admissible D u v hAux hfirst hnotProtected
          have htrail' := stoppedNetworkTrail_tail D u T w hstart htrail
          have hgood' := ih (traceStep D u v) v T (tailWord w)
            hAux' hstart' htrail'
          have hstatus : D.status u = .U ∨ D.status u = .D := by
            rcases hstart.2.2 with hU | hD
            · exact Or.inl hU.1
            · exact Or.inr hD.1
          rw [wordVertices_cons u w, wordVertices_cons v (tailWord w)]
          change (D.status u = .U ∨ D.status u = .D) ∧
            TraceGood (traceStep D u v)
              (v :: wordVertices (wordVertex v (tailWord w) 1) (tailWord (tailWord w)))
          have hgood'' : TraceGood (traceStep D u v)
              (v :: wordVertices (wordVertex v (tailWord w) 1) (tailWord (tailWord w))) := by
            rw [← wordVertices_cons v (tailWord w)]
            exact hgood'
          exact ⟨hstatus, hgood''⟩

theorem traceDCount_wordVertices {G : Finset Plane} (D : Network G)
    (u : Plane) {n : ℕ} (w : DirectionWord n) :
    traceDCount D (wordVertices u w) =
      (Finset.univ.filter fun i : Fin n =>
        (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .D).card := by
  rw [traceDCount_eq_listPrefixDCount]
  have hlen : (wordVertices u w).length - 1 = n := by
    simp [wordVertices]
  rw [hlen]
  exact listPrefixDCount_wordVertices D u w

theorem main : AKLT.Blueprint.Rec.TraceCoefficientStatement := by
  unfold AKLT.Blueprint.Rec.TraceCoefficientStatement
  intro G D hAux u hstart T n w htrail
  let ND := (Finset.univ.filter fun i : Fin n =>
    (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .D).card
  have hgood := traceGood_of_stopped D u T n w hAux hstart htrail
  have hcoeff := traceCoefficient_eq_count D (wordVertices u w) hgood
  have hcount := traceDCount_wordVertices D u w
  have hlen : (wordVertices u w).length - 1 = n := by
    simp [wordVertices]
  have hformula : traceCoefficient D (wordVertices u w) =
      (1 / 3 : ℚ) ^ n * (3 / 5 : ℚ) ^ ND := by
    dsimp [ND]
    rw [hcoeff, hlen, hcount]
  constructor
  · rw [hformula]
    positivity
  · exact hformula

end AKLT.W.REC040

namespace AKLT.W

end AKLT.W
