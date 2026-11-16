import AKLT.Blueprint.H1.NodesReduction

open AKLT.Defs

namespace AKLT.W.H1M025

open AKLT.Blueprint.H1

private theorem template_bounds {x : Plane} (hx : x ∈ templateSites) :
    -2 ≤ x.1 ∧ x.1 ≤ 2 ∧ -2 ≤ x.2 ∧ x.2 ≤ 2 := by
  have hs : x ∈ square (0, 0) 2 := (Finset.mem_filter.mp hx).1
  simp [square] at hs
  omega

private theorem template_distance_bound {x : Plane} (hx : x ∈ templateSites) :
    latticeDist x (0, 0) ≤ 2 :=
  (Finset.mem_filter.mp hx).2

private theorem tip_edge (π : PatternData) {x : Plane} (hx : x ∈ templateTips)
    {e : Plane × Plane} (he : e ∈ π.bonds) (hi : e.1 = x ∨ e.2 = x) :
    (x = (2, 0) ∧ e = ((1, 0), (2, 0))) ∨
    (x = (0, 2) ∧ e = ((0, 1), (0, 2))) ∨
    (x = (-2, 0) ∧ e = ((-2, 0), (-1, 0))) ∨
    (x = (0, -2) ∧ e = ((0, -2), (0, -1))) := by
  classical
  have hb : e ∈ internalBonds templateSites := (Finset.mem_filter.mp he).1
  rcases Finset.mem_biUnion.mp hb with ⟨p, hp, hImage⟩
  rcases Finset.mem_image.mp hImage with ⟨q, hq, rfl⟩
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  have hqPos : (c, d) ∈ positiveNeighbours (a, b) := (Finset.mem_inter.mp hq).1
  have hqSite : (c, d) ∈ templateSites := (Finset.mem_inter.mp hq).2
  have hpB := template_bounds hp
  have hqB := template_bounds hqSite
  have hpD := template_distance_bound hp
  have hqD := template_distance_bound hqSite
  have hqCases : (c = a + 1 ∧ d = b) ∨ (c = a ∧ d = b + 1) := by
    simpa [positiveNeighbours] using hqPos
  simp [templateTips] at hx
  rcases hx with hxt | hxt | hxt | hxt
  · subst x
    have hi' : (a, b) = (2, 0) ∨ (c, d) = (2, 0) := by simpa using hi
    rcases hqCases with hqE | hqN
    · rcases hi' with hpX | hqX
      · simp only [Prod.mk.injEq] at hpX
        rcases hqE with ⟨hc, hd⟩
        omega
      · simp only [Prod.mk.injEq] at hqX
        rcases hqE with ⟨hc, hd⟩
        have ha : a = 1 := by omega
        have hb' : b = 0 := by omega
        subst_vars
        left
        simp
    · rcases hi' with hpX | hqX
      · simp only [Prod.mk.injEq] at hpX
        rcases hqN with ⟨hc, hd⟩
        have hc' : c = 2 := by omega
        have hd' : d = 1 := by omega
        subst_vars
        norm_num [latticeDist] at hqD <;> omega
      · simp only [Prod.mk.injEq] at hqX
        rcases hqN with ⟨hc, hd⟩
        have ha : a = 2 := by omega
        have hb' : b = -1 := by omega
        subst_vars
        norm_num [latticeDist] at hpD
  · subst x
    have hi' : (a, b) = (0, 2) ∨ (c, d) = (0, 2) := by simpa using hi
    rcases hqCases with hqE | hqN
    · rcases hi' with hpX | hqX
      · simp only [Prod.mk.injEq] at hpX
        rcases hqE with ⟨hc, hd⟩
        have hc' : c = 1 := by omega
        have hd' : d = 2 := by omega
        subst_vars
        norm_num [latticeDist] at hqD <;> omega
      · simp only [Prod.mk.injEq] at hqX
        rcases hqE with ⟨hc, hd⟩
        have ha : a = -1 := by omega
        have hb' : b = 2 := by omega
        subst_vars
        norm_num [latticeDist] at hpD
    · rcases hi' with hpX | hqX
      · simp only [Prod.mk.injEq] at hpX
        rcases hqN with ⟨hc, hd⟩
        omega
      · simp only [Prod.mk.injEq] at hqX
        rcases hqN with ⟨hc, hd⟩
        have ha : a = 0 := by omega
        have hb' : b = 1 := by omega
        subst_vars
        right
        left
        simp
  · subst x
    have hi' : (a, b) = (-2, 0) ∨ (c, d) = (-2, 0) := by simpa using hi
    rcases hqCases with hqE | hqN
    · rcases hi' with hpX | hqX
      · simp only [Prod.mk.injEq] at hpX
        rcases hqE with ⟨hc, hd⟩
        have ha : a = -2 := by omega
        have hb' : b = 0 := by omega
        subst_vars
        right
        right
        left
        simp
      · simp only [Prod.mk.injEq] at hqX
        rcases hqE with ⟨hc, hd⟩
        omega
    · rcases hi' with hpX | hqX
      · simp only [Prod.mk.injEq] at hpX
        rcases hqN with ⟨hc, hd⟩
        have hc' : c = -2 := by omega
        have hd' : d = 1 := by omega
        subst_vars
        norm_num [latticeDist] at hqD <;> omega
      · simp only [Prod.mk.injEq] at hqX
        rcases hqN with ⟨hc, hd⟩
        have ha : a = -2 := by omega
        have hb' : b = -1 := by omega
        subst_vars
        norm_num [latticeDist] at hpD
  · subst x
    have hi' : (a, b) = (0, -2) ∨ (c, d) = (0, -2) := by simpa using hi
    rcases hqCases with hqE | hqN
    · rcases hi' with hpX | hqX
      · simp only [Prod.mk.injEq] at hpX
        rcases hqE with ⟨hc, hd⟩
        have hc' : c = 1 := by omega
        have hd' : d = -2 := by omega
        subst_vars
        norm_num [latticeDist] at hqD <;> omega
      · simp only [Prod.mk.injEq] at hqX
        rcases hqE with ⟨hc, hd⟩
        have ha : a = -1 := by omega
        have hb' : b = -2 := by omega
        subst_vars
        norm_num [latticeDist] at hpD
    · rcases hi' with hpX | hqX
      · simp only [Prod.mk.injEq] at hpX
        rcases hqN with ⟨hc, hd⟩
        have ha : a = 0 := by omega
        have hb' : b = -2 := by omega
        subst_vars
        right
        right
        right
        simp
      · simp only [Prod.mk.injEq] at hqX
        rcases hqN with ⟨hc, hd⟩
        omega

private theorem adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  change latticeDist x y = 1 at h
  change latticeDist y x = 1
  unfold latticeDist at *
  omega

private theorem peripheral_not_adjacent {x y : Plane}
    (hx : x ∈ templateCorners ∪ templateTips)
    (hy : y ∈ templateCorners ∪ templateTips) : ¬ Adjacent x y := by
  simp [templateCorners, templateTips] at hx hy
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx <;>
    rcases hy with hy | hy | hy | hy | hy | hy | hy | hy <;>
    subst_vars <;> norm_num [Adjacent, latticeDist]

private theorem corner_not_tip {x : Plane} (hc : x ∈ templateCorners) :
    x ∉ templateTips := by
  intro ht
  simp [templateCorners, templateTips] at hc ht
  rcases hc with hc | hc | hc | hc <;>
    rcases ht with ht | ht | ht | ht <;> simp_all

private theorem bond_adjacent (π : PatternData) {e : Plane × Plane}
    (he : e ∈ π.bonds) : Adjacent e.1 e.2 := by
  classical
  have hb : e ∈ internalBonds templateSites := (Finset.mem_filter.mp he).1
  rcases Finset.mem_biUnion.mp hb with ⟨p, hp, hImage⟩
  rcases Finset.mem_image.mp hImage with ⟨q, hq, rfl⟩
  have hqPos : q ∈ positiveNeighbours p := (Finset.mem_inter.mp hq).1
  change Adjacent p q
  have hqCases : q = (p.1 + 1, p.2) ∨ q = (p.1, p.2 + 1) := by
    simpa [positiveNeighbours] using hqPos
  rcases hqCases with h | h
  · subst q
    norm_num [Adjacent, latticeDist]
  · subst q
    norm_num [Adjacent, latticeDist]

private theorem bond_endpoints_active (π : PatternData) {e : Plane × Plane}
    (he : e ∈ π.bonds) : e.1 ∈ π.active ∧ e.2 ∈ π.active := by
  classical
  rcases Finset.mem_filter.mp he with ⟨hb, ⟨hs₁, hs₂, _⟩⟩
  rcases Finset.mem_biUnion.mp hb with ⟨p, hp, hImage⟩
  rcases Finset.mem_image.mp hImage with ⟨q, hq, rfl⟩
  have hqInter := hq
  have hqSite : q ∈ templateSites := (Finset.mem_inter.mp hqInter).2
  change p ∈ π.active ∧ q ∈ π.active
  constructor
  · exact Finset.mem_filter.mpr ⟨hp, hs₁⟩
  · exact Finset.mem_filter.mpr ⟨hqSite, hs₂⟩

private theorem headD_filterMap_eq {α β : Type} (l : List α) (f : α → Option β)
    (q fallback : β) (hall : ∀ a ∈ l, f a = none ∨ f a = some q)
    (hq : q ∈ l.filterMap f) : (l.filterMap f).headD fallback = q := by
  induction l with
  | nil => simp at hq
  | cons a l ih =>
      have ha := hall a (by simp)
      cases hfa : f a with
      | none =>
          have hq' : q ∈ l.filterMap f := by
            simpa [List.filterMap_cons, hfa] using hq
          have hall' : ∀ b ∈ l, f b = none ∨ f b = some q := by
            intro b hb
            exact hall b (by simp [hb])
          simpa [List.filterMap_cons, hfa] using ih hall' hq'
      | some b =>
          have hbq : b = q := by
            rcases ha with hnone | hsome
            · simp [hfa] at hnone
            · simp [hfa] at hsome
              exact hsome
          simp [hfa, hbq]

private theorem leaf_neighbour_eq_other (π : PatternData) (x : Plane)
    {e : Plane × Plane} (he : e ∈ π.bonds) (hi : e.1 = x ∨ e.2 = x)
    (huniq : ∀ f ∈ π.bonds, (f.1 = x ∨ f.2 = x) → f = e) :
    leafNeighbour π x = if e.1 = x then e.2 else e.1 := by
  classical
  let q : Plane := if e.1 = x then e.2 else e.1
  let f : Plane × Plane → Option Plane := fun z =>
    if z.1 = x then some z.2 else if z.2 = x then some z.1 else none
  have heList : e ∈ π.bonds.toList := Finset.mem_toList.mpr he
  have hf : f e = some q := by
    dsimp [f, q]
    by_cases h : e.1 = x
    · simp [h]
    · have h₂ : e.2 = x := hi.resolve_left h
      simp [h, h₂]
  have hall : ∀ z ∈ π.bonds.toList, f z = none ∨ f z = some q := by
    intro z hz
    by_cases hinc : z.1 = x ∨ z.2 = x
    · have hzB : z ∈ π.bonds := Finset.mem_toList.mp hz
      have hze : z = e := huniq z hzB hinc
      subst z
      exact Or.inr hf
    · have h₁ : z.1 ≠ x := fun hz' => hinc (Or.inl hz')
      have h₂ : z.2 ≠ x := fun hz' => hinc (Or.inr hz')
      simp [f, h₁, h₂]
  have hmem : q ∈ π.bonds.toList.filterMap f :=
    (List.mem_filterMap).2 ⟨e, heList, hf⟩
  change (π.bonds.toList.filterMap (fun z =>
    if z.1 = x then some z.2 else if z.2 = x then some z.1 else none)).headD (0, 0) = _
  change (π.bonds.toList.filterMap f).headD (0, 0) = q
  simpa [q] using headD_filterMap_eq π.bonds.toList f q (0, 0) hall hmem

private theorem deleted_peripheral (π : PatternData) (r : Representation) {x : Plane}
    (hx : x ∈ deletedLeafSites π r) : x ∈ templateCorners ∪ templateTips := by
  have hx' := Finset.mem_sdiff.mp hx
  by_cases ht : x ∈ templateTips
  · exact Finset.mem_union.mpr (Or.inr ht)
  · by_cases hc : x ∈ templateCorners
    · exact Finset.mem_union.mpr (Or.inl hc)
    · have hr : x ∈ reducedSpinSites π r := by
        simp [reducedSpinSites, hx'.1, ht, hc]
      exact (hx'.2 hr).elim

private theorem tip_incident_eq (π : PatternData) {x : Plane} (hx : x ∈ templateTips)
    {e f : Plane × Plane} (he : e ∈ π.bonds) (hi : e.1 = x ∨ e.2 = x)
    (hf : f ∈ π.bonds) (hj : f.1 = x ∨ f.2 = x) : e = f := by
  have he' := tip_edge π hx he hi
  have hf' := tip_edge π hx hf hj
  rcases he' with ⟨hx, he⟩ | ⟨hx, he⟩ | ⟨hx, he⟩ | ⟨hx, he⟩ <;>
    rcases hf' with ⟨hy, hf⟩ | ⟨hy, hf⟩ | ⟨hy, hf⟩ | ⟨hy, hf⟩ <;>
    simp_all

private theorem tip_degree_bound (π : PatternData) {x : Plane}
    (hx : x ∈ templateTips) : patternDegree π x ≤ 1 := by
  unfold patternDegree
  apply Finset.card_le_one.mpr
  intro e he f hf
  exact tip_incident_eq π hx (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
    (Finset.mem_filter.mp hf).1 (Finset.mem_filter.mp hf).2

private theorem deleted_degree_le_one (π : PatternData) (r : Representation) {x : Plane}
    (hx : x ∈ deletedLeafSites π r) : patternDegree π x ≤ 1 := by
  have hx' := Finset.mem_sdiff.mp hx
  have hper := deleted_peripheral π r hx
  rcases Finset.mem_union.mp hper with hc | ht
  · by_contra hle
    have hge : 2 ≤ patternDegree π x := by omega
    have hne : patternDegree π x ≠ 0 := by omega
    have htip := corner_not_tip hc
    have hsingle : ¬ SingleReplacement π r x := by
      intro hs
      simp only [SingleReplacement] at hs
      omega
    have hr : x ∈ reducedSpinSites π r := by
      simp [reducedSpinSites, hx'.1, htip, hc, hne, hsingle]
    exact hx'.2 hr
  · exact tip_degree_bound π ht

theorem main : AKLT.Blueprint.H1.PeripheralGeometryStatement := by
  intro π hCovered r x hx
  have hper : x ∈ templateCorners ∪ templateTips := deleted_peripheral π r hx
  have hdeg : patternDegree π x ≤ 1 := deleted_degree_le_one π r hx
  refine ⟨hper, hdeg, ?_, ?_⟩
  · intro hd
    let S : Finset (Plane × Plane) := π.bonds.filter fun e => e.1 = x ∨ e.2 = x
    have hdS : S.card = 1 := by simpa [S, patternDegree] using hd
    have hpos : 0 < S.card := by simp [hdS]
    rcases Finset.card_pos.mp hpos with ⟨e, heS⟩
    have heB : e ∈ π.bonds := (Finset.mem_filter.mp heS).1
    have hi : e.1 = x ∨ e.2 = x := (Finset.mem_filter.mp heS).2
    have hcard : S.card ≤ 1 := by simp [hdS]
    have huniq : ∀ f ∈ π.bonds, (f.1 = x ∨ f.2 = x) → f = e := by
      intro f hf hfi
      have hfS : f ∈ S := Finset.mem_filter.mpr ⟨hf, hfi⟩
      exact (Finset.card_le_one.mp hcard) f hfS e heS
    have hleaf : leafNeighbour π x = if e.1 = x then e.2 else e.1 :=
      leaf_neighbour_eq_other π x heB hi huniq
    let q : Plane := if e.1 = x then e.2 else e.1
    have hqactive : q ∈ π.active := by
      dsimp [q]
      split_ifs with h
      · exact (bond_endpoints_active π heB).2
      · have h₂ : e.2 = x := hi.resolve_left h
        simpa [h₂] using (bond_endpoints_active π heB).1
    have hqadj : Adjacent x q := by
      dsimp [q]
      split_ifs with h
      · simpa [h] using bond_adjacent π heB
      · have h₂ : e.2 = x := hi.resolve_left h
        simpa [h, h₂] using adjacent_symm (bond_adjacent π heB)
    have hqper : q ∉ templateCorners ∪ templateTips := by
      intro hq
      exact (peripheral_not_adjacent hper hq) hqadj
    have hret : q ∈ reducedSpinSites π r := by
      have htip : q ∉ templateTips := fun ht => hqper (Finset.mem_union.mpr (Or.inr ht))
      have hcorner : q ∉ templateCorners := fun hc => hqper (Finset.mem_union.mpr (Or.inl hc))
      simp [reducedSpinSites, hqactive, htip, hcorner]
    simpa [hleaf, q] using hret
  · intro y hy
    exact peripheral_not_adjacent hper (deleted_peripheral π r hy)

end AKLT.W.H1M025
