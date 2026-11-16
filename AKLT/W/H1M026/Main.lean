import AKLT.Blueprint.H1.NodesReduction

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.W.H1M026

open AKLT.Blueprint.H1

private lemma reduced_subset_active (π : PatternData) (r : Representation) :
    reducedSpinSites π r ⊆ π.active := by
  classical
  intro x hx
  exact Finset.mem_filter.mp hx |>.1

private lemma active_partition (π : PatternData) (r : Representation) :
    Disjoint (reducedSpinSites π r) (deletedLeafSites π r) ∧
      reducedSpinSites π r ∪ deletedLeafSites π r = π.active := by
  classical
  constructor
  · rw [deletedLeafSites]
    exact Finset.disjoint_sdiff
  · rw [deletedLeafSites]
    exact Finset.union_sdiff_of_subset (reduced_subset_active π r)

private lemma deleted_mem_active {π : PatternData} {r : Representation} {x : Plane}
    (hx : x ∈ deletedLeafSites π r) : x ∈ π.active := by
  exact (Finset.mem_sdiff.mp hx).1

private lemma deleted_not_retained {π : PatternData} {r : Representation} {x : Plane}
    (hx : x ∈ deletedLeafSites π r) : x ∉ reducedSpinSites π r := by
  exact (Finset.mem_sdiff.mp hx).2

private lemma active_status_ne_X {π : PatternData} {x : Plane} (hx : x ∈ π.active) :
    π.statusAt x ≠ .X := (Finset.mem_filter.mp hx).2

private lemma external_site_template (j : Fin 20) :
    (externalSlot j).1 ∈ templateSites := by
  fin_cases j <;> norm_num [externalSlot, templateSites, square, latticeDist]

private lemma external_site_active_iff {π : PatternData} (j : Fin 20) :
    (externalSlot j).1 ∈ π.active ↔ π.statusAt (externalSlot j).1 ≠ .X := by
  rw [PatternData.active, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨external_site_template j, h⟩⟩

private def slotTerm (m : Fin 20 → UnitVector) (n : Plane → Vec3) (j : Fin 20) : ℝ :=
  1 + dot (m j).val (n (externalSlot j).1)

private lemma splitSlotProduct (π : PatternData) (r : Representation)
    (hπ : π.Covered) (rgeom : PeripheralGeometry π r) (m : Fin 20 → UnitVector)
    (n : Plane → Vec3) :
    (∏ j : Fin 20, if π.statusAt (externalSlot j).1 = .X then 1 else slotTerm m n j) =
      (∏ j : Fin 20, if (externalSlot j).1 ∈ reducedSpinSites π r then slotTerm m n j else 1) *
      ∏ x ∈ deletedLeafSites π r, coveredSiteField m x (n x) := by
  classical
  let D := deletedLeafSites π r
  let V := reducedSpinSites π r
  have hfield :
    (∏ x ∈ D, coveredSiteField m x (n x)) =
        ∏ j : Fin 20, if (externalSlot j).1 ∈ D then slotTerm m n j else 1 := by
    calc
      (∏ x ∈ D, coveredSiteField m x (n x)) =
          ∏ x ∈ D, ∏ j ∈ Finset.univ.filter (fun j : Fin 20 => (externalSlot j).1 = x),
            slotTerm m n j := by
        apply Finset.prod_congr rfl
        intro x hx
        simp only [coveredSiteField, slotTerm]
        calc
          (∏ j : Fin 20, if (externalSlot j).1 = x then
              1 + dot (m j).val (n x) else 1) =
              ∏ j : Fin 20, if j ∈ Finset.univ.filter
                (fun j : Fin 20 => (externalSlot j).1 = x) then
                1 + dot (m j).val (n (externalSlot j).1) else 1 := by
            apply Finset.prod_congr rfl
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            by_cases h : (externalSlot j).1 = x <;> simp [h]
          _ = _ := by rw [Finset.prod_ite_mem_eq]
      _ = ∏ j : Fin 20, if (externalSlot j).1 ∈ D then slotTerm m n j else 1 := by
        rw [Finset.prod_fiberwise_eq_prod_filter (s := Finset.univ) (t := D)
          (g := fun j : Fin 20 => (externalSlot j).1) (f := fun j => slotTerm m n j)]
        rw [← Finset.prod_ite_mem_eq]
        simp [Finset.mem_filter]
  have hpoint (j : Fin 20) :
      (if π.statusAt (externalSlot j).1 = .X then 1 else slotTerm m n j) =
        (if (externalSlot j).1 ∈ V then slotTerm m n j else 1) *
        (if (externalSlot j).1 ∈ D then slotTerm m n j else 1) := by
    by_cases hv : (externalSlot j).1 ∈ V
    · have hs := active_status_ne_X (reduced_subset_active π r hv)
      have hnotD : (externalSlot j).1 ∉ D :=
        Finset.disjoint_left.mp (active_partition π r).1 hv
      simp [hv, hs, hnotD]
    · by_cases hd : (externalSlot j).1 ∈ D
      · have hs := active_status_ne_X (deleted_mem_active hd)
        simp [hv, hd, hs]
      · have hs : π.statusAt (externalSlot j).1 = .X := by
          by_contra hn
          have ha := (external_site_active_iff (π := π) j).2 hn
          rcases Finset.mem_union.mp ((active_partition π r).2 ▸ ha) with hV | hD
          · exact hv hV
          · exact hd hD
        simp [hv, hd, hs]
  calc
    _ = ∏ j : Fin 20,
          ((if (externalSlot j).1 ∈ V then slotTerm m n j else 1) *
           (if (externalSlot j).1 ∈ D then slotTerm m n j else 1)) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact hpoint j
    _ = (∏ j : Fin 20, if (externalSlot j).1 ∈ V then slotTerm m n j else 1) *
        ∏ j : Fin 20, if (externalSlot j).1 ∈ D then slotTerm m n j else 1 := by
      rw [Finset.prod_mul_distrib]
    _ = _ := by rw [← hfield]

private def incidentBondSet (π : PatternData) (x : Plane) : Finset (Plane × Plane) :=
  π.bonds.filter fun e => e.1 = x ∨ e.2 = x

private lemma filterMap_headD_eq_of_forall_none_or_same {α β : Type*} {l : List α}
    {f : α → Option β} {b d : β}
    (hall : ∀ a ∈ l, f a = none ∨ f a = some b)
    (hex : ∃ a ∈ l, f a = some b) : (l.filterMap f).headD d = b := by
  induction l with
  | nil =>
      rcases hex with ⟨a, ha, _⟩
      simp at ha
  | cons a l ih =>
      rcases hall a (by simp) with ha | ha
      · simp only [List.filterMap_cons, ha]
        apply ih
        · intro x hx
          exact hall x (by simp [hx])
        · obtain ⟨x, hx, hxf⟩ := hex
          by_cases hxa : x = a
          · subst x
            simp [ha] at hxf
          · have hxl : x ∈ l := by simpa [hxa] using hx
            exact ⟨x, hxl, hxf⟩
      · simp only [List.filterMap_cons, ha]
        simp

private lemma bond_endpoints_active (π : PatternData) (e : Plane × Plane)
    (he : e ∈ π.bonds) : e.1 ∈ π.active ∧ e.2 ∈ π.active := by
  classical
  have hf := Finset.mem_filter.mp he
  have hsites : e.1 ∈ templateSites ∧ e.2 ∈ templateSites := by
    have hi := hf.1
    simp only [internalBonds, Finset.mem_biUnion, Finset.mem_inter, Finset.mem_image] at hi
    obtain ⟨x, hx, y, hy, hxy⟩ := hi
    cases hxy
    exact ⟨hx, hy.2⟩
  exact ⟨Finset.mem_filter.mpr ⟨hsites.1, hf.2.1⟩,
    Finset.mem_filter.mpr ⟨hsites.2, hf.2.2.1⟩⟩

private lemma bond_adjacent (π : PatternData) (e : Plane × Plane) (he : e ∈ π.bonds) :
    Adjacent e.1 e.2 := by
  classical
  have hf := Finset.mem_filter.mp he
  have hi := hf.1
  simp only [internalBonds, Finset.mem_biUnion, Finset.mem_inter, Finset.mem_image] at hi
  obtain ⟨x, hx, y, hy, hxy⟩ := hi
  cases hxy
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy.1 with h | h
  · subst y
    simp [Adjacent, latticeDist]
  · subst y
    simp [Adjacent, latticeDist] <;> omega

private lemma leafNeighbour_eq_other_of_degree_one (π : PatternData) (x : Plane)
    (hdeg : patternDegree π x = 1) :
    ∃ e ∈ π.bonds, (e.1 = x ∨ e.2 = x) ∧
      leafNeighbour π x = (if e.1 = x then e.2 else e.1) := by
  classical
  have hcard : (incidentBondSet π x).card = 1 := by
    simpa [patternDegree, incidentBondSet] using hdeg
  obtain ⟨e, hset⟩ := Finset.card_eq_one.mp hcard
  have heinc : e ∈ incidentBondSet π x := by rw [hset]; simp
  have he : e ∈ π.bonds := (Finset.mem_filter.mp heinc).1
  have hendpoint : e.1 = x ∨ e.2 = x := (Finset.mem_filter.mp heinc).2
  have hadj := bond_adjacent π e he
  have hne : e.1 ≠ e.2 := by
    intro heq
    have hzero : latticeDist e.1 e.2 = 0 := by rw [heq]; simp [latticeDist]
    change latticeDist e.1 e.2 = 1 at hadj
    omega
  let other : Plane := if e.1 = x then e.2 else e.1
  have hmap : ∀ f ∈ π.bonds.toList,
      (if f.1 = x then some f.2 else if f.2 = x then some f.1 else none) =
        (if f = e then some other else none) := by
    intro f hf
    have hfb : f ∈ π.bonds := by simpa using hf
    by_cases hfe : f = e
    · subst f
      rcases hendpoint with h1 | h2
      · simp [other, h1]
      · have hnot1 : e.1 ≠ x := by
          intro h1
          exact hne (h1.trans h2.symm)
        simp [other, h2, hnot1]
    · have hnot : ¬ (f.1 = x ∨ f.2 = x) := by
        intro hinc
        have hmem : f ∈ incidentBondSet π x := Finset.mem_filter.mpr ⟨hfb, hinc⟩
        have : f = e := by rw [hset] at hmem; simpa using hmem
        exact hfe this
      have hn1 : f.1 ≠ x := fun h => hnot (Or.inl h)
      have hn2 : f.2 ≠ x := fun h => hnot (Or.inr h)
      simp [hn1, hn2, hfe]
  have hlist := List.filterMap_congr hmap
  have helist : e ∈ π.bonds.toList := by simpa using he
  have hhead : (π.bonds.toList.filterMap
      (fun f => if f = e then some other else none)).headD (0, 0) = other := by
    apply filterMap_headD_eq_of_forall_none_or_same
    · intro f hf
      by_cases h : f = e <;> simp [h]
    · exact ⟨e, helist, by simp⟩
  refine ⟨e, he, hendpoint, ?_⟩
  dsimp [leafNeighbour]
  rw [hlist]
  exact hhead

private lemma peripheral_not_passage_endpoints (π : PatternData) {x : Plane}
    (hx : x ∈ templateCorners ∪ templateTips) :
    x ≠ (0, 0) ∧ x ≠ π.outgoing.step := by
  cases π.outgoing <;>
    simp [templateCorners, templateTips, Compass.step] at hx <;>
    rcases hx with h | h | h | h | h | h | h | h <;> subst x <;>
      simp [Compass.step]

private def bondTerm (n : Plane → Vec3) (e : Plane × Plane) : ℝ :=
  1 + dot (n e.1) (n e.2)

private abbrev droppedPassageBond (π : PatternData) (next : Bool) (e : Plane × Plane) : Prop :=
  next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step}

private lemma splitBondProduct (π : PatternData) (r : Representation)
    (hπ : π.Covered) (hgeo : PeripheralGeometry π r) (next : Bool)
    (n : Plane → Vec3) :
    (∏ e ∈ π.bonds, if droppedPassageBond π next e then 1 else bondTerm n e) =
      (∏ e ∈ π.bonds, if e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r ∧
          ¬ droppedPassageBond π next e then bondTerm n e else 1) *
        ∏ x ∈ deletedLeafSites π r,
          if patternDegree π x = 0 then 1 else 1 + dot (n x) (n (leafNeighbour π x)) := by
  classical
  let V := reducedSpinSites π r
  let D := deletedLeafSites π r
  let cross (e : Plane × Plane) : Prop := e.1 ∈ D ∨ e.2 ∈ D
  let owner (e : Plane × Plane) : Plane := if e.1 ∈ D then e.1 else e.2
  have hnotDD (e : Plane × Plane) (he : e ∈ π.bonds) :
      ¬ (e.1 ∈ D ∧ e.2 ∈ D) := by
    intro hboth
    have hper := hgeo e.1 hboth.1
    exact hper.2.2.2 e.2 hboth.2 (bond_adjacent π e he)
  have hdrop_cross (e : Plane × Plane) (he : e ∈ π.bonds) (hc : cross e) :
      ¬ droppedPassageBond π next e := by
    intro hd
    have hpair : ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} := hd.2
    rcases hc with h1 | h2
    · have hm : e.1 ∈ ({e.1, e.2} : Finset Plane) := by simp
      rw [hpair] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      have hper := hgeo e.1 h1
      rcases peripheral_not_passage_endpoints π hper.1 with ⟨hn0, hno⟩
      rcases hm with hm | hm
      · exact hn0 hm
      · exact hno hm
    · have hm : e.2 ∈ ({e.1, e.2} : Finset Plane) := by simp
      rw [hpair] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      have hper := hgeo e.2 h2
      rcases peripheral_not_passage_endpoints π hper.1 with ⟨hn0, hno⟩
      rcases hm with hm | hm
      · exact hn0 hm
      · exact hno hm
  have hendpoint (e : Plane × Plane) (he : e ∈ π.bonds) :
      (e.1 ∈ V ∨ e.1 ∈ D) ∧ (e.2 ∈ V ∨ e.2 ∈ D) := by
    have ha := bond_endpoints_active π e he
    exact ⟨Finset.mem_union.mp ((active_partition π r).2 ▸ ha.1),
      Finset.mem_union.mp ((active_partition π r).2 ▸ ha.2)⟩
  have hclass (e : Plane × Plane) (he : e ∈ π.bonds) :
      (e.1 ∈ V ∧ e.2 ∈ V) ∨ cross e := by
    rcases hendpoint e he with ⟨h1 | h1, h2 | h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inr h2)
    · exact Or.inr (Or.inl h1)
    · exact False.elim (hnotDD e he ⟨h1, h2⟩)
  have hpoint (e : Plane × Plane) (he : e ∈ π.bonds) :
      (if droppedPassageBond π next e then 1 else bondTerm n e) =
        (if e.1 ∈ V ∧ e.2 ∈ V ∧ ¬ droppedPassageBond π next e then bondTerm n e else 1) *
          (if cross e then bondTerm n e else 1) := by
    rcases hclass e he with hret | hcross
    · have hnotcross : ¬ cross e := by
        rintro (h | h)
        · exact Finset.disjoint_left.mp (active_partition π r).1 hret.1 h
        · exact Finset.disjoint_left.mp (active_partition π r).1 hret.2 h
      by_cases hd : droppedPassageBond π next e
      · simp [hd, hret, hnotcross]
      · simp [hd, hret, hnotcross]
    · have hnotboth : ¬ (e.1 ∈ V ∧ e.2 ∈ V) := by
        rintro ⟨h1, h2⟩
        rcases hcross with hD | hD
        · exact (deleted_not_retained hD h1)
        · exact (deleted_not_retained hD h2)
      have hnd := hdrop_cross e he hcross
      have hnotret : ¬ (e.1 ∈ V ∧ e.2 ∈ V ∧ ¬ droppedPassageBond π next e) := by
        rintro ⟨h1, h2, _⟩
        exact hnotboth ⟨h1, h2⟩
      simp only [if_neg hnd, if_neg hnotret, if_pos hcross, one_mul]
  have hcrossprod :
      (∏ e ∈ π.bonds, if cross e then bondTerm n e else 1) =
        ∏ x ∈ D, if patternDegree π x = 0 then 1 else 1 + dot (n x) (n (leafNeighbour π x)) := by
    let C := π.bonds.filter cross
    have hfiltered :
        (∏ e ∈ π.bonds, if cross e then bondTerm n e else 1) = ∏ e ∈ C, bondTerm n e := by
      rw [Finset.prod_ite]
      simp [C]
    rw [hfiltered]
    have howner (e : Plane × Plane) (he : e ∈ C) : owner e ∈ D := by
      have he' : e ∈ π.bonds := (Finset.mem_filter.mp he).1
      have hc : cross e := (Finset.mem_filter.mp he).2
      by_cases h : e.1 ∈ D
      · simp [owner, h]
      · rcases hc with h1 | h2
        · exact False.elim (h h1)
        · simpa [owner, h] using h2
    rw [← Finset.prod_fiberwise_of_maps_to (s := C) (t := D) (g := owner)
      (f := fun e => bondTerm n e) howner]
    apply Finset.prod_congr rfl
    intro x hx
    have hfiber : C.filter (fun e => owner e = x) = incidentBondSet π x := by
      ext e
      simp only [Finset.mem_filter, C, cross, owner, incidentBondSet]
      constructor
      · rintro ⟨⟨he, hc⟩, howner⟩
        refine ⟨he, ?_⟩
        by_cases h : e.1 ∈ D
        · simp [h] at howner
          exact Or.inl howner
        · simp [h] at howner
          exact Or.inr howner
      · rintro ⟨he, hi⟩
        have hnotDD' : ¬ (e.1 ∈ D ∧ e.2 ∈ D) := hnotDD e he
        have hc : e.1 ∈ D ∨ e.2 ∈ D := by
          rcases hi with h1 | h2
          · exact Or.inl (by simpa [h1] using hx)
          · exact Or.inr (by simpa [h2] using hx)
        refine ⟨⟨he, hc⟩, ?_⟩
        rcases hi with h1 | h2
        · simp [owner, h1, hx]
        · have hnot1 : e.1 ∉ D := by
            intro h1
            exact hnotDD' ⟨h1, by simpa [h2] using hx⟩
          simp [owner, hnot1, h2, hx]
    rw [hfiber]
    have hdeg := (hgeo x hx).2.1
    by_cases hz : patternDegree π x = 0
    · have hc : incidentBondSet π x = ∅ := by
        apply Finset.card_eq_zero.mp
        simpa [patternDegree, incidentBondSet] using hz
      simp [hz, hc]
    · have h1 : patternDegree π x = 1 := by omega
      obtain ⟨e, he, hi, hleaf⟩ := leafNeighbour_eq_other_of_degree_one π x h1
      have hcExists : ∃ e₀, incidentBondSet π x = {e₀} :=
        Finset.card_eq_one.mp (by simpa [patternDegree, incidentBondSet] using h1)
      obtain ⟨e₀, hc⟩ := hcExists
      have he₀ : e₀ = e := by
        have hm : e ∈ incidentBondSet π x := Finset.mem_filter.mpr ⟨he, hi⟩
        rw [hc] at hm
        have heq : e = e₀ := by simpa using hm
        exact heq.symm
      subst e₀
      rw [hc]
      have hadj := bond_adjacent π e he
      have hne : e.1 ≠ e.2 := by
        intro h
        have hz : latticeDist e.1 e.2 = 0 := by rw [h]; simp [latticeDist]
        change latticeDist e.1 e.2 = 1 at hadj
        omega
      rcases hi with hi | hi
      · simp [h1, hleaf, hi, bondTerm, dot]
      · have hnot : e.1 ≠ x := by
          intro h
          exact hne (h.trans hi.symm)
        simp [h1, hleaf, hnot, hi, bondTerm, dot, mul_comm]
  calc
    _ = (∏ e ∈ π.bonds,
          if e.1 ∈ V ∧ e.2 ∈ V ∧ ¬ droppedPassageBond π next e then bondTerm n e else 1) *
        (∏ e ∈ π.bonds, if cross e then bondTerm n e else 1) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro e he
      exact hpoint e he
    _ = _ := by rw [hcrossprod]

private def joinAssignments (π : PatternData) (r : Representation)
    (a : reducedSpinSites π r → SpinLetter)
    (d : deletedLeafSites π r → SpinLetter) : π.active → SpinLetter :=
  fun x => if h : x.val ∈ reducedSpinSites π r then a ⟨x.val, h⟩
    else d ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, h⟩⟩

private def assignmentEquiv (π : PatternData) (r : Representation) :
    (π.active → SpinLetter) ≃
      ((reducedSpinSites π r → SpinLetter) × (deletedLeafSites π r → SpinLetter)) where
  toFun n :=
    (fun x => n ⟨x.val, reduced_subset_active π r x.property⟩,
     fun x => n ⟨x.val, deleted_mem_active x.property⟩)
  invFun p := joinAssignments π r p.1 p.2
  left_inv n := by
    funext x
    simp only [joinAssignments]
    split
    · rfl
    · rfl
  right_inv p := by
    rcases p with ⟨a, d⟩
    apply Prod.ext
    · funext x
      simp only [joinAssignments]
      split
      · rfl
      · rename_i hx
        exact False.elim (hx x.property)
    · funext x
      simp only [joinAssignments]
      split
      · rename_i hx
        have hnot : x.val ∉ deletedLeafSites π r :=
          Finset.disjoint_left.mp (active_partition π r).1 hx
        exact False.elim (hnot x.property)
      · rfl

private def activeSiteEquiv (π : PatternData) (r : Representation) :
    π.active ≃ (reducedSpinSites π r ⊕ deletedLeafSites π r) where
  toFun x := if h : x.val ∈ reducedSpinSites π r then Sum.inl ⟨x.val, h⟩
    else Sum.inr ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, h⟩⟩
  invFun
    | Sum.inl x => ⟨x.val, reduced_subset_active π r x.property⟩
    | Sum.inr x => ⟨x.val, deleted_mem_active x.property⟩
  left_inv x := by
    apply Subtype.ext
    dsimp
    split_ifs <;> rfl
  right_inv x := by
    cases x with
    | inl x =>
        dsimp
        simp [x.property]
    | inr x =>
        dsimp
        simp [deleted_not_retained x.property]

private lemma activeSiteEquiv_symm_inl (π : PatternData) (r : Representation)
    (x : reducedSpinSites π r) :
    (activeSiteEquiv π r).symm (Sum.inl x) =
      ⟨x.val, reduced_subset_active π r x.property⟩ := by
  apply Subtype.ext
  rfl

private lemma activeSiteEquiv_symm_inr (π : PatternData) (r : Representation)
    (x : deletedLeafSites π r) :
    (activeSiteEquiv π r).symm (Sum.inr x) =
      ⟨x.val, deleted_mem_active x.property⟩ := by
  apply Subtype.ext
  rfl

private lemma prod_active_partition (π : PatternData) (r : Representation)
    {M : Type*} [CommMonoid M] (f : π.active → M) :
    (∏ x : π.active, f x) =
      (∏ x : reducedSpinSites π r, f ((activeSiteEquiv π r).symm (Sum.inl x))) *
        ∏ x : deletedLeafSites π r, f ((activeSiteEquiv π r).symm (Sum.inr x)) := by
  classical
  let e := activeSiteEquiv π r
  calc
    (∏ x : π.active, f x) = ∏ y : reducedSpinSites π r ⊕ deletedLeafSites π r,
        f (e.symm y) := by
      exact Fintype.prod_equiv e f (fun y => f (e.symm y)) (by intro x; simp [e])
    _ = (∏ x : reducedSpinSites π r, f (e.symm (Sum.inl x))) *
        ∏ x : deletedLeafSites π r, f (e.symm (Sum.inr x)) := by
      rw [Fintype.prod_sum_type]

private def joinedSpin (π : PatternData) (r : Representation)
    (a : reducedSpinSites π r → SpinLetter)
    (d : deletedLeafSites π r → SpinLetter) : Plane → Vec3 :=
  π.spins (joinAssignments π r a d)

private lemma joinedSpin_retained (π : PatternData) (r : Representation)
    (a : reducedSpinSites π r → SpinLetter) (d : deletedLeafSites π r → SpinLetter)
    {x : Plane} (hx : x ∈ reducedSpinSites π r) :
    joinedSpin π r a d x = supportSpins (reducedSpinSites π r) a x := by
  classical
  have ha : x ∈ π.active := reduced_subset_active π r hx
  simp [joinedSpin, PatternData.spins, joinAssignments, supportSpins, ha, hx]

private lemma joinedSpin_deleted (π : PatternData) (r : Representation)
    (a : reducedSpinSites π r → SpinLetter) (d : deletedLeafSites π r → SpinLetter)
    {x : Plane} (hx : x ∈ deletedLeafSites π r) :
    joinedSpin π r a d x = spinVector (d ⟨x, hx⟩) := by
  classical
  have ha : x ∈ π.active := deleted_mem_active hx
  have hn : x ∉ reducedSpinSites π r := deleted_not_retained hx
  simp [joinedSpin, PatternData.spins, joinAssignments, ha, hn]

private def deletedSummandFactor (π : PatternData) (r : Representation)
    (next : Bool) (m : Fin 20 → UnitVector)
    (a : reducedSpinSites π r → SpinLetter)
    (d : deletedLeafSites π r → SpinLetter) (x : deletedLeafSites π r) : ℝ :=
  spinWeight (π.statusAt x.val) (d x) *
    coveredSiteField m x.val (spinVector (d x)) *
    (if patternDegree π x.val = 0 then 1 else
      1 + dot (spinVector (d x))
        (supportSpins (reducedSpinSites π r) a (leafNeighbour π x.val)))

private def retainedSummandFactor (π : PatternData) (r : Representation)
    (next : Bool) (m : Fin 20 → UnitVector)
    (a : reducedSpinSites π r → SpinLetter) : ℝ :=
  (∏ x : reducedSpinSites π r,
    spinWeight (nextStatus π next x.val) (a x)) *
    retainedOriginalFactors π r next m (supportSpins (reducedSpinSites π r) a)

private lemma deleted_nextStatus (π : PatternData) (r : Representation)
    (hgeo : PeripheralGeometry π r) {x : Plane}
    (hx : x ∈ deletedLeafSites π r) (next : Bool) :
    nextStatus π next x = π.statusAt x := by
  have hper := hgeo x hx
  have hneq := (peripheral_not_passage_endpoints π hper.1).1
  simp [nextStatus, hneq]

private lemma assignmentTermFactorization (π : PatternData) (r : Representation)
    (hπ : π.Covered) (hgeo : PeripheralGeometry π r) (next : Bool)
    (m : Fin 20 → UnitVector)
    (a : reducedSpinSites π r → SpinLetter)
    (d : deletedLeafSites π r → SpinLetter) :
    (∏ x : π.active,
      spinWeight (nextStatus π next x.val) (joinAssignments π r a d x)) *
      (∏ e ∈ π.bonds,
        if droppedPassageBond π next e then 1 else bondTerm (joinedSpin π r a d) e) *
      (∏ j : Fin 20,
        if π.statusAt (externalSlot j).1 = .X then 1 else
          slotTerm m (joinedSpin π r a d) j) =
      retainedSummandFactor π r next m a *
        ∏ x : deletedLeafSites π r, deletedSummandFactor π r next m a d x := by
  classical
  let V := reducedSpinSites π r
  let D := deletedLeafSites π r
  let n := joinedSpin π r a d
  let nV := supportSpins V a
  have hw :
      (∏ x : π.active,
        spinWeight (nextStatus π next x.val) (joinAssignments π r a d x)) =
        (∏ x : V, spinWeight (nextStatus π next x.val) (a x)) *
          ∏ x : D, spinWeight (π.statusAt x.val) (d x) := by
    let f : π.active → ℝ := fun x =>
      spinWeight (nextStatus π next x.val) (joinAssignments π r a d x)
    rw [prod_active_partition π r f]
    congr 1
    · apply Finset.prod_congr rfl
      intro x hx
      rw [activeSiteEquiv_symm_inl]
      simp [f, joinAssignments]
    · apply Finset.prod_congr rfl
      intro x hx
      rw [activeSiteEquiv_symm_inr]
      dsimp only [f]
      rw [deleted_nextStatus π r hgeo x.property next]
      simp [joinAssignments, deleted_not_retained x.property]
  have hb := splitBondProduct π r hπ hgeo next n
  have hs := splitSlotProduct π r hπ hgeo m n
  have hbr :
      (∏ e ∈ π.bonds,
        if e.1 ∈ V ∧ e.2 ∈ V ∧ ¬droppedPassageBond π next e then bondTerm n e else 1) =
        (∏ e ∈ π.bonds,
          if e.1 ∈ V ∧ e.2 ∈ V ∧ ¬droppedPassageBond π next e then bondTerm nV e else 1) := by
    dsimp only [n, nV]
    apply Finset.prod_congr rfl
    intro e he
    by_cases hcondition : e.1 ∈ V ∧ e.2 ∈ V ∧ ¬droppedPassageBond π next e
    · simp only [if_pos hcondition, bondTerm]
      rw [joinedSpin_retained π r a d hcondition.1,
        joinedSpin_retained π r a d hcondition.2.1]
    · have hnotRight :
          ¬ (e.1 ∈ V ∧ e.2 ∈ V ∧
            (next = true → ({e.1, e.2} : Finset Plane) ≠ {(0, 0), π.outgoing.step})) := by
        rintro ⟨h1, h2, hnd⟩
        apply hcondition
        refine ⟨h1, h2, ?_⟩
        intro hd
        exact hnd hd.1 hd.2
      simp [hcondition, hnotRight]
  have hbrD :
      (∏ x ∈ D, if patternDegree π x = 0 then 1 else
        1 + dot (n x) (n (leafNeighbour π x))) =
        ∏ x : D, if patternDegree π x.val = 0 then 1 else
          1 + dot (spinVector (d x)) (nV (leafNeighbour π x.val)) := by
    calc
      _ = ∏ x : D, if patternDegree π x.val = 0 then 1 else
          1 + dot (n x.val) (n (leafNeighbour π x.val)) :=
        (Finset.prod_coe_sort D _).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro x hx
        dsimp only [n, nV]
        by_cases hz : patternDegree π x.val = 0
        · simp [hz]
        · have hdeg := (hgeo x.val x.property).2.1
          have hone : patternDegree π x.val = 1 := by omega
          have hneighbor := (hgeo x.val x.property).2.2.1 hone
          rw [joinedSpin_deleted π r a d x.property,
            joinedSpin_retained π r a d hneighbor]
  have hsr :
      (∏ j : Fin 20, if (externalSlot j).1 ∈ V then slotTerm m n j else 1) =
        ∏ j : Fin 20, if (externalSlot j).1 ∈ V then slotTerm m nV j else 1 := by
    dsimp only [n, nV]
    apply Finset.prod_congr rfl
    intro j hj
    by_cases h : (externalSlot j).1 ∈ V
    · simp only [if_pos h, slotTerm]
      rw [joinedSpin_retained π r a d h]
    · simp [h]
  have hsd :
      (∏ x ∈ D, coveredSiteField m x (n x)) =
        ∏ x : D, coveredSiteField m x.val (spinVector (d x)) := by
    calc
      _ = ∏ x : D, coveredSiteField m x.val (n x.val) :=
        (Finset.prod_coe_sort D _).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro x hx
        dsimp only [n]
        rw [joinedSpin_deleted π r a d x.property]
  have hleaf :
      (∏ x : D, deletedSummandFactor π r next m a d x) =
        (∏ x : D, spinWeight (π.statusAt x.val) (d x)) *
          (∏ x : D, coveredSiteField m x.val (spinVector (d x))) *
          ∏ x : D, if patternDegree π x.val = 0 then 1 else
            1 + dot (spinVector (d x)) (nV (leafNeighbour π x.val)) := by
    calc
      _ = ∏ x : D,
          ((spinWeight (π.statusAt x.val) (d x) *
              coveredSiteField m x.val (spinVector (d x))) *
            (if patternDegree π x.val = 0 then 1 else
              1 + dot (spinVector (d x)) (nV (leafNeighbour π x.val)))) := by
        apply Finset.prod_congr rfl
        intro x hx
        simp [deletedSummandFactor, nV, V, mul_assoc]
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [n] at hb hs
  rw [hb, hs, hw]
  rw [hbr, hbrD, hsr, hsd]
  simp only [retainedSummandFactor, retainedOriginalFactors, nV, V]
  rw [hleaf]
  simp only [droppedPassageBond, bondTerm, slotTerm]
  dsimp [nV, V]
  ac_rfl

private lemma deletedAssignmentSum (π : PatternData) (r : Representation)
    (next : Bool) (m : Fin 20 → UnitVector)
    (a : reducedSpinSites π r → SpinLetter) :
    (∑ d : deletedLeafSites π r → SpinLetter,
      ∏ x : deletedLeafSites π r, deletedSummandFactor π r next m a d x) =
      ∏ x : deletedLeafSites π r,
        integratedLeafFactor π m x.val (supportSpins (reducedSpinSites π r) a) := by
  classical
  let g : deletedLeafSites π r → SpinLetter → ℝ := fun x z =>
    spinWeight (π.statusAt x.val) z *
      (coveredSiteField m x.val (spinVector z) *
        (if patternDegree π x.val = 0 then 1 else
          1 + dot (spinVector z)
            (supportSpins (reducedSpinSites π r) a (leafNeighbour π x.val))))
  calc
    _ = ∑ d : deletedLeafSites π r → SpinLetter, ∏ x, g x (d x) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.prod_congr rfl
      intro x hx
      simp [g, deletedSummandFactor, mul_assoc]
    _ = ∏ x : deletedLeafSites π r, ∑ z : SpinLetter, g x z :=
      (Fintype.prod_sum (f := g)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro x hx
      simp [g, integratedLeafFactor, siteFunctional]

private lemma patternFunctional_eq_separated (π : PatternData) (r : Representation)
    (hπ : π.Covered) (hgeo : PeripheralGeometry π r) (next : Bool)
    (m : Fin 20 → UnitVector) :
    patternFunctional π next m (fun _ => 1) = separatedLeafFunctional π r next m := by
  classical
  let originalTerm (n : π.active → SpinLetter) : ℝ :=
    (∏ x : π.active, spinWeight (nextStatus π next x.val) (n x)) *
      (∏ e ∈ π.bonds,
        if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1 else
          1 + dot (π.spins n e.1) (π.spins n e.2)) *
      ∏ j : Fin 20, if π.statusAt (externalSlot j).1 = .X then 1 else
        1 + dot (m j).val (π.spins n (externalSlot j).1)
  simp only [patternFunctional, mul_one, one_mul]
  change (∑ n : π.active → SpinLetter, originalTerm n) = _
  let pairTerm (p : (reducedSpinSites π r → SpinLetter) ×
      (deletedLeafSites π r → SpinLetter)) : ℝ :=
    originalTerm (joinAssignments π r p.1 p.2)
  calc
    (∑ n : π.active → SpinLetter, originalTerm n) =
        ∑ p : (reducedSpinSites π r → SpinLetter) ×
          (deletedLeafSites π r → SpinLetter), pairTerm p := by
      apply Fintype.sum_equiv (assignmentEquiv π r) originalTerm pairTerm
      intro n
      exact congrArg originalTerm ((assignmentEquiv π r).left_inv n).symm
    _ = ∑ a : reducedSpinSites π r → SpinLetter,
          ∑ d : deletedLeafSites π r → SpinLetter, pairTerm (a, d) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ a : reducedSpinSites π r → SpinLetter,
          retainedSummandFactor π r next m a *
            ∏ x : deletedLeafSites π r, integratedLeafFactor π m x.val
              (supportSpins (reducedSpinSites π r) a) := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        (∑ d : deletedLeafSites π r → SpinLetter, pairTerm (a, d)) =
            ∑ d : deletedLeafSites π r → SpinLetter,
              retainedSummandFactor π r next m a *
                ∏ x : deletedLeafSites π r, deletedSummandFactor π r next m a d x := by
          apply Finset.sum_congr rfl
          intro d hd
          simp only [pairTerm, originalTerm]
          simpa [joinedSpin, nextStatus, droppedPassageBond, bondTerm, slotTerm] using
            assignmentTermFactorization π r hπ hgeo next m a d
        _ = retainedSummandFactor π r next m a *
            ∑ d : deletedLeafSites π r → SpinLetter,
              ∏ x : deletedLeafSites π r, deletedSummandFactor π r next m a d x := by
          rw [Finset.mul_sum]
        _ = retainedSummandFactor π r next m a *
            ∏ x : deletedLeafSites π r,
              integratedLeafFactor π m x.val (supportSpins (reducedSpinSites π r) a) := by
          rw [deletedAssignmentSum]
    _ = separatedLeafFunctional π r next m := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [separatedLeafFunctional, retainedSummandFactor, retainedOriginalFactors]
      let f : Plane → ℝ := fun x =>
        integratedLeafFactor π m x (supportSpins (reducedSpinSites π r) a)
      have hprod := Finset.prod_coe_sort (deletedLeafSites π r) f
      rw [← hprod]

end AKLT.W.H1M026

theorem AKLT.W.H1M026.main : AKLT.Blueprint.H1.PeripheralFubiniStatement := by
  intro π hπ r hgeo next m
  cases next with
  | false =>
      simpa [AKLT.Defs.patternNext, AKLT.Defs.patternCurrent] using
        AKLT.W.H1M026.patternFunctional_eq_separated π r hπ hgeo false m
  | true =>
      simpa [AKLT.Defs.patternNext, AKLT.Defs.patternCurrent] using
        AKLT.W.H1M026.patternFunctional_eq_separated π r hπ hgeo true m

