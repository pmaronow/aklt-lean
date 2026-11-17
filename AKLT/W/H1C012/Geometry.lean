module
public import AKLT.Cert.H1.Production.Leaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C012

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

noncomputable section

private theorem mem_internal_iff {G : Finset Plane} {a b : Plane} :
    (a,b) ∈ internalBonds G ↔ a ∈ G ∧ b ∈ G ∧
      (b = (a.1+1,a.2) ∨ b = (a.1,a.2+1)) := by
  simp [internalBonds, positiveNeighbours, and_assoc, and_left_comm, and_comm]

private theorem internal_no_reverse {G : Finset Plane} {a b : Plane}
    (h : (a,b) ∈ internalBonds G) : (b,a) ∉ internalBonds G := by
  intro hr
  have hp := (mem_internal_iff.mp h).2.2
  have hq := (mem_internal_iff.mp hr).2.2
  rcases a with ⟨ax,ay⟩
  rcases b with ⟨bx,by'⟩
  simp only [Prod.mk.injEq] at hp hq
  omega

private theorem bond_iff_present (π : PatternData) {a b : Plane}
    (h : (a,b) ∈ internalBonds templateSites) :
    (a,b) ∈ π.bonds ↔ presentBond π a b = true := by
  have hn : (b,a) ∉ π.bonds := fun hm => internal_no_reverse h
    (Finset.mem_filter.mp hm).1
  simp only [presentBond, decide_eq_true_eq, hn, or_false]

private theorem present_symm (π : PatternData) (a b : Plane) :
    presentBond π a b = presentBond π b a := by
  simp only [presentBond, or_comm]

private theorem present_iff (π : PatternData) {a b : Plane}
    (h : (a,b) ∈ internalBonds templateSites ∨ (b,a) ∈ internalBonds templateSites) :
    presentBond π a b = true ↔
      π.statusAt a ≠ .X ∧ π.statusAt b ≠ .X ∧
      (a ∈ templateTips ∨ b ∈ π.keptAt a) ∧
      (b ∈ templateTips ∨ a ∈ π.keptAt b) := by
  rcases h with h | h
  · rw [← bond_iff_present π h]
    simp only [PatternData.bonds, Finset.mem_filter, h, true_and]
  · rw [present_symm, ← bond_iff_present π h]
    simp only [PatternData.bonds, Finset.mem_filter, h, true_and]
    tauto

private theorem internal_incident_cases {G : Finset Plane} {x : Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds G) (hx : e.1 = x ∨ e.2 = x) :
    e = (x,(x.1+1,x.2)) ∨ e = (x,(x.1,x.2+1)) ∨
      e = ((x.1-1,x.2),x) ∨ e = ((x.1,x.2-1),x) := by
  rcases e with ⟨a,b⟩
  have hp := (mem_internal_iff.mp he).2.2
  rcases a with ⟨ax,ay⟩
  rcases b with ⟨bx,by'⟩
  rcases x with ⟨xx,xy⟩
  simp only [Prod.mk.injEq] at hx hp ⊢
  omega

/-- The one or two positively oriented template edges incident to each group. -/
private def groupEdges (i : Nat) : Finset (Plane × Plane) :=
  ([{((1,0),(2,0))},
    {((1,0),(1,1)),((0,1),(1,1))},
    {((0,1),(0,2))},
    {((-1,1),(0,1)),((-1,0),(-1,1))},
    {((-2,0),(-1,0))},
    {((-1,-1),(-1,0)),((-1,-1),(0,-1))},
    {((0,-2),(0,-1))},
    {((0,-1),(1,-1)),((1,-1),(1,0))}] : List (Finset (Plane × Plane))).getD i ∅

private theorem group_incident (i : Fin 8) :
    (internalBonds templateSites).filter (fun e =>
      e.1 = groupPoint i.val ∨ e.2 = groupPoint i.val) = groupEdges i.val := by
  apply Finset.ext
  intro e
  constructor
  · intro he
    rcases Finset.mem_filter.mp he with ⟨he,hx⟩
    have hc := internal_incident_cases he hx
    fin_cases i <;>
      simp only [groupPoint, ringSites, List.getD_cons_zero, List.getD_cons_succ,
        Nat.reduceMod, beq_self_eq_true, Nat.reduceBEq, ite_true] at hc
    all_goals
      rcases hc with rfl | rfl | rfl | rfl <;>
        norm_num [mem_internal_iff, templateSites, square, latticeDist] at he
    all_goals norm_num [groupEdges]
  · intro he
    fin_cases i <;> norm_num [groupEdges] at he
    all_goals
      rcases he with rfl | rfl <;>
        norm_num [Finset.mem_filter, mem_internal_iff, groupPoint, ringSites,
          templateSites, square, latticeDist]

private theorem group_degree (π : PatternData) (i : Fin 8) :
    patternDegree π (groupPoint i.val) =
      if i.val % 2 == 0 then
        (presentBond π (ringSites.getD i.val (0,0)) (groupPoint i.val)).toNat
      else
        (presentBond π (ringSites.getD i.val (0,0))
          (ringSites.getD ((i.val+1)%8) (0,0))).toNat +
        (presentBond π (ringSites.getD ((i.val+7)%8) (0,0))
          (ringSites.getD i.val (0,0))).toNat := by
  have hb : π.bonds = (internalBonds templateSites).filter
      (fun e => presentBond π e.1 e.2 = true) := by
    ext e
    constructor
    · intro he
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1,
        (bond_iff_present π (Finset.mem_filter.mp he).1).mp he⟩
    · intro he
      exact (bond_iff_present π (Finset.mem_filter.mp he).1).mpr
        (Finset.mem_filter.mp he).2
  rw [patternDegree, hb, Finset.filter_comm, group_incident]
  fin_cases i <;>
    simp [groupEdges, groupPoint, ringSites, Finset.card_filter,
      present_symm, Bool.toNat, Nat.add_comm, -Finset.sum_boole]

private theorem optionAt_ring (a : Input) (i : Fin 8) :
    a.optionAt (ringSites.getD i.val (0,0)) =
      (ringOptions a.axes a.corners).getD i.val ⟨0,0⟩ := by
  fin_cases i <;> simp [Input.optionAt, ringSites, ringOptions, List.range_succ]

private theorem input_status (a : Input) (x : Plane) (hx : x ∈ templateSites)
    (h0 : x ≠ (0,0)) (ht : x ∉ templateTips) :
    (inputPattern a).statusAt x =
      if (a.optionAt x).status == 1 then .U else
        if (a.optionAt x).status == 2 then .D else .X := by
  have ht' : x ≠ (2,0) ∧ x ≠ (0,2) ∧ x ≠ (-2,0) ∧ x ≠ (0,-2) := by
    simpa [templateTips] using ht
  simp [PatternData.statusAt, hx, inputPattern, h0, ht'.1, ht'.2.1,
    ht'.2.2.1, ht'.2.2.2]

private theorem input_tip_status (a : Input) (x : Plane) (hx : x ∈ templateTips) :
    (inputPattern a).statusAt x = .U := by
  simp only [templateTips, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    norm_num [PatternData.statusAt, inputPattern, templateSites, square, latticeDist]

private theorem input_kept_direction (a : Input) (x : Plane) (hx : x ∈ templateSites)
    (h0 : x ≠ (0,0)) (d : Fin 4) :
    x + (compassAt d.val).step ∈ (inputPattern a).keptAt x ↔
      hasDirection (a.optionAt x).mask d.val = true := by
  simp only [PatternData.keptAt, hx, dite_true, inputPattern, beq_iff_eq, h0,
    ite_false, Finset.mem_image]
  constructor
  · rintro ⟨c,hc,hc'⟩
    have hc' := add_left_cancel hc'
    simp only [List.mem_toFinset, List.mem_map] at hc
    obtain ⟨k,hk,rfl⟩ := hc
    simp only [List.mem_filter, List.mem_range] at hk
    have hkd : k = d.val := by
      have hk4 := hk.1
      interval_cases k <;> fin_cases d <;>
        norm_num [compassAt, Compass.step] at hc'
      all_goals rfl
    simpa only [hkd] using hk.2
  · intro hd
    refine ⟨compassAt d.val, ?_, rfl⟩
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨d.val, by simp [d.isLt, hd], rfl⟩

local instance : LawfulBEq RawOption where
  rfl := by rintro ⟨s,m⟩; change (s == s && m == m) = true; simp
  eq_of_beq := by
    rintro ⟨s,m⟩ ⟨t,n⟩ h
    change (s == t && m == n) = true at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl,rfl⟩
    rfl

private theorem ring_facts (i : Fin 8) :
    ringSites.getD i.val (0,0) ∈ templateSites ∧
      ringSites.getD i.val (0,0) ≠ (0,0) ∧
      ringSites.getD i.val (0,0) ∉ templateTips := by
  fin_cases i <;> norm_num [ringSites, templateSites, templateTips, square, latticeDist]

private theorem input_ring_status_bound (a : Input) (h : inputCheck a = true) (i : Fin 8) :
    (a.optionAt (ringSites.getD i.val (0,0))).status ≤ 2 := by
  simp only [inputCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.forall_mem_zipIdx, Nat.zero_add] at h
  have hal : a.axes.length = 4 := by tauto
  have hcl : a.corners.length = 4 := by tauto
  have ha : ∀ k (hk : k < a.axes.length), a.axes[k] ∈ axialOptions k := by
    simpa only [List.contains_iff_mem] using (show ∀ k (hk : k < a.axes.length),
      (axialOptions k).contains a.axes[k] = true by tauto)
  have hc : ∀ k (hk : k < a.corners.length), a.corners[k] ∈ cornerOptions := by
    have hall : ∀ k (hk : k < a.corners.length),
        cornerOptions.contains a.corners[k] = true ∧
          cornerCompatible a.axes k a.corners[k] = true := h.1.1.1.1.2
    intro k hk
    exact List.contains_iff_mem.mp (hall k hk).1
  have ha' : ∀ k : Fin 4, (a.axes.getD k.val ⟨0,0⟩).status ≤ 2 := by
    intro k
    have hk : k.val < a.axes.length := by omega
    rw [List.getD_eq_getElem a.axes ⟨0,0⟩ hk]
    have hp := ha k.val hk
    fin_cases k <;> norm_num [axialOptions, List.range_succ] at hp
    all_goals aesop
  have hc' : ∀ k : Fin 4, (a.corners.getD k.val ⟨0,0⟩).status ≤ 2 := by
    intro k
    have hk : k.val < a.corners.length := by omega
    rw [List.getD_eq_getElem a.corners ⟨0,0⟩ hk]
    have hp := hc k.val hk
    norm_num [cornerOptions] at hp
    aesop
  rw [optionAt_ring]
  simp only [ringOptions]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map,
    List.getElem_range]
  split
  · exact ha' ⟨i.val/2,by omega⟩
  · exact hc' ⟨i.val/2,by omega⟩

private theorem input_status_nonzero (a : Input) (x : Plane) (hx : x ∈ templateSites)
    (h0 : x ≠ (0,0)) (ht : x ∉ templateTips) (hs : (a.optionAt x).status ≤ 2) :
    (inputPattern a).statusAt x ≠ .X ↔ (a.optionAt x).status ≠ 0 := by
  rw [input_status a x hx h0 ht]
  simp only [beq_iff_eq]
  by_cases h1 : (a.optionAt x).status = 1
  · simp [h1]
  · by_cases h2 : (a.optionAt x).status = 2
    · simp [h1,h2]
    · have hz : (a.optionAt x).status = 0 := by omega
      simp [hz]

private theorem input_status_D (a : Input) (x : Plane) (hx : x ∈ templateSites)
    (h0 : x ≠ (0,0)) (ht : x ∉ templateTips) :
    (inputPattern a).statusAt x = .D ↔ (a.optionAt x).status = 2 := by
  rw [input_status a x hx h0 ht]
  simp only [beq_iff_eq]
  split_ifs <;> simp_all

private theorem input_non_tip_edge (a : Input) (x y : Plane) (d e : Fin 4)
    (hx : x ∈ templateSites) (hy : y ∈ templateSites)
    (hx0 : x ≠ (0,0)) (hy0 : y ≠ (0,0))
    (hxt : x ∉ templateTips) (hyt : y ∉ templateTips)
    (hsx : (a.optionAt x).status ≤ 2) (hsy : (a.optionAt y).status ≤ 2)
    (hxy : x + (compassAt d.val).step = y)
    (hyx : y + (compassAt e.val).step = x)
    (hi : (x,y) ∈ internalBonds templateSites ∨ (y,x) ∈ internalBonds templateSites) :
    presentBond (inputPattern a) x y =
      ((a.optionAt x).status != 0 && (a.optionAt y).status != 0 &&
        hasDirection (a.optionAt x).mask d.val && hasDirection (a.optionAt y).mask e.val) := by
  have hkx := input_kept_direction a x hx hx0 d
  have hky := input_kept_direction a y hy hy0 e
  rw [hxy] at hkx
  rw [hyx] at hky
  apply Bool.eq_iff_iff.mpr
  rw [present_iff _ hi]
  simp only [input_status_nonzero a x hx hx0 hxt hsx,
    input_status_nonzero a y hy hy0 hyt hsy, hxt, hyt, false_or,
    hkx, hky, Bool.and_eq_true, bne_iff_ne, and_assoc]

private def cycleDirection (i : Nat) : Fin 4 :=
  ⟨edgeDirections.getD i 0 % 4, Nat.mod_lt _ (by omega)⟩

private theorem input_cycle_edge (a : Input) (h : inputCheck a = true) (i : Fin 8) :
    presentBond (inputPattern a) (ringSites.getD i.val (0,0))
      (ringSites.getD ((i.val+1)%8) (0,0)) =
        (rawEdges a.axes a.corners).getD (4+i.val) false := by
  let j : Fin 8 := ⟨(i.val+1)%8, Nat.mod_lt _ (by omega)⟩
  let d := cycleDirection i.val
  let e : Fin 4 := ⟨(d.val+2)%4, Nat.mod_lt _ (by omega)⟩
  have hxy : ringSites.getD i.val (0,0) + (compassAt d.val).step =
      ringSites.getD j.val (0,0) := by
    fin_cases i <;> norm_num [j,d,cycleDirection,edgeDirections,ringSites,
      compassAt,Compass.step,Prod.mk_add_mk]
  have hyx : ringSites.getD j.val (0,0) + (compassAt e.val).step =
      ringSites.getD i.val (0,0) := by
    fin_cases i <;> norm_num [j,d,e,cycleDirection,edgeDirections,ringSites,
      compassAt,Compass.step,Prod.mk_add_mk]
  have hi : (ringSites.getD i.val (0,0),ringSites.getD j.val (0,0)) ∈
      internalBonds templateSites ∨
      (ringSites.getD j.val (0,0),ringSites.getD i.val (0,0)) ∈
      internalBonds templateSites := by
    fin_cases i <;> norm_num [j,ringSites,mem_internal_iff,templateSites,square,latticeDist]
  have hp := input_non_tip_edge a _ _ d e (ring_facts i).1 (ring_facts j).1
    (ring_facts i).2.1 (ring_facts j).2.1 (ring_facts i).2.2 (ring_facts j).2.2
    (input_ring_status_bound a h i) (input_ring_status_bound a h j) hxy hyx hi
  rw [optionAt_ring a i, optionAt_ring a j] at hp
  fin_cases i <;> simpa [j,d,e,cycleDirection,rawEdges,ringOptions,
    edgeDirections,List.range_succ] using hp

private theorem input_tip_edge (a : Input) (h : inputCheck a = true) (i : Fin 4) :
    presentBond (inputPattern a) (ringSites.getD (2*i.val) (0,0))
      (groupPoint (2*i.val)) = (rawEdges a.axes a.corners).getD (12+i.val) false := by
  let j : Fin 8 := ⟨2*i.val, by omega⟩
  have ht : groupPoint j.val ∈ templateTips := by
    fin_cases i <;> norm_num [j,groupPoint,ringSites,templateTips]
  have hxy : ringSites.getD j.val (0,0) + (compassAt i.val).step = groupPoint j.val := by
    fin_cases i <;> norm_num [j,groupPoint,ringSites,compassAt,Compass.step,Prod.mk_add_mk]
  have hi : (ringSites.getD j.val (0,0),groupPoint j.val) ∈ internalBonds templateSites ∨
      (groupPoint j.val,ringSites.getD j.val (0,0)) ∈ internalBonds templateSites := by
    fin_cases i <;> norm_num [j,groupPoint,ringSites,mem_internal_iff,
      templateSites,square,latticeDist]
  have hk := input_kept_direction a _ (ring_facts j).1 (ring_facts j).2.1 i
  rw [hxy] at hk
  have hp : presentBond (inputPattern a) (ringSites.getD j.val (0,0)) (groupPoint j.val) =
      ((a.optionAt (ringSites.getD j.val (0,0))).status != 0 &&
        hasDirection (a.optionAt (ringSites.getD j.val (0,0))).mask i.val) := by
    apply Bool.eq_iff_iff.mpr
    rw [present_iff _ hi]
    have hUX : Status.U ≠ Status.X := by intro hh; cases hh
    simp only [input_status_nonzero a _ (ring_facts j).1 (ring_facts j).2.1
      (ring_facts j).2.2 (input_ring_status_bound a h j), input_tip_status a _ ht,
      (ring_facts j).2.2, ht, ne_eq, hUX, not_false_eq_true,
      false_or, true_or, and_true, true_and, hk,
      Bool.and_eq_true, bne_iff_ne]
  rw [optionAt_ring a j] at hp
  fin_cases i <;> simpa [j,rawEdges,ringOptions,List.range_succ] using hp

private theorem input_group_degree (a : Input) (h : inputCheck a = true) (i : Fin 8) :
    patternDegree (inputPattern a) (groupPoint i.val) =
      if i.val%2 == 0 then ((rawEdges a.axes a.corners).getD (12+i.val/2) false).toNat
      else ((rawEdges a.axes a.corners).getD (4+i.val) false).toNat +
        ((rawEdges a.axes a.corners).getD (4+(i.val+7)%8) false).toNat := by
  rw [group_degree]
  have hc := input_cycle_edge a h i
  have hprev := input_cycle_edge a h ⟨(i.val+7)%8,Nat.mod_lt _ (by omega)⟩
  have ht := input_tip_edge a h ⟨i.val/2,by omega⟩
  fin_cases i <;>
    simp only [Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
      Nat.reduceBEq, beq_self_eq_true, Bool.false_eq_true, ite_false, ite_true] at hc hprev ht ⊢
  all_goals
    first | exact congrArg Bool.toNat ht | rw [hc, hprev]

theorem input_group_slots (a : Input) (h : inputCheck a = true) (i : Fin 8) :
    groupSlots (inputPattern a) (inputRepresentation a) (groupPoint i.val) = inputSlots a i.val := by
  have hd := input_group_degree a h i
  have htips : (groupPoint i.val ∈ templateTips) ↔ i.val%2 = 0 := by
    fin_cases i <;> norm_num [groupPoint,ringSites,templateTips]
  have hcorners : (groupPoint i.val ∈ templateCorners) ↔ i.val%2 ≠ 0 := by
    fin_cases i <;> norm_num [groupPoint,ringSites,templateCorners]
  simp only [groupSlots, reductionGroups, Finset.mem_filter, Finset.mem_union,
    hcorners, htips, groupIsPair, SingleReplacement, inputRepresentation, hd, inputSlots]
  cases a.leafReduced <;>
    cases (rawEdges a.axes a.corners).getD (4+i.val) false <;>
    cases (rawEdges a.axes a.corners).getD (4+(i.val+7)%8) false <;>
    cases (rawEdges a.axes a.corners).getD (12+i.val/2) false <;>
    by_cases heven : i.val%2 = 0 <;>
    simp [heven,Bool.toNat]

theorem input_group_diluted (a : Input) (i : Fin 8) (hi : i.val%2 ≠ 0) :
    (inputPattern a).statusAt (groupPoint i.val) = .D ↔
      ((ringOptions a.axes a.corners).getD i.val ⟨0,0⟩).status = 2 := by
  have hg : groupPoint i.val = ringSites.getD i.val (0,0) := by
    simp [groupPoint,hi]
  rw [hg, input_status_D a _ (ring_facts i).1 (ring_facts i).2.1 (ring_facts i).2.2,
    optionAt_ring]

theorem geometry_specs (a : Input) (ss : List PackedSite) (h : geometryCheck a ss = true) :
    ss.length = 8 ∧ ∀ i (hi : i < ss.length), ss[i].spec = inputSpec a i := by
  have hbeq : ∀ s t : SiteSpec, (s == t) = true ↔ s = t := by
    intro s t
    cases s
    cases t
    simp [BEq.beq,instBEqSiteSpec.beq]
  simpa only [geometryCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.forall_mem_zipIdx, Nat.zero_add, hbeq] using h

#print axioms input_group_slots
#print axioms input_group_diluted
#print axioms geometry_specs

end
end AKLT.W.H1C012
