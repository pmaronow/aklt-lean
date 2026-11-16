import AKLT.W.H1C013.Geometry

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C013
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

deriving instance ReflBEq for RawOption
deriving instance LawfulBEq for RawOption
deriving instance ReflBEq for SiteSpec
deriving instance LawfulBEq for SiteSpec

def incidentEdges (i : Nat) : Finset (Plane × Plane) :=
  if i = 0 then {((1,0),(2,0))} else
  if i = 1 then {((0,1),(1,1)), ((1,0),(1,1))} else
  if i = 2 then {((0,1),(0,2))} else
  if i = 3 then {((-1,1),(0,1)), ((-1,0),(-1,1))} else
  if i = 4 then {((-2,0),(-1,0))} else
  if i = 5 then {((-1,-1),(0,-1)), ((-1,-1),(-1,0))} else
  if i = 6 then {((0,-2),(0,-1))} else
    {((0,-1),(1,-1)), ((1,-1),(1,0))}

theorem incident_template : ∀ i : Fin 8,
    ((internalBonds templateSites).filter fun e =>
      e.1 = groupPoint i.val ∨ e.2 = groupPoint i.val) = incidentEdges i.val := by
  decide +kernel

theorem ring_point_mem : ∀ i : Fin 8, ringSites.getD i.val (0,0) ∈ templateSites := by
  decide +kernel

theorem ring_point_not_center : ∀ i : Fin 8, ringSites.getD i.val (0,0) ≠ (0,0) := by
  decide +kernel

theorem ring_point_not_tip : ∀ i : Fin 8, ringSites.getD i.val (0,0) ∉ templateTips := by
  decide +kernel

theorem point_kinds : ∀ i : Fin 8,
    (groupPoint i.val ∈ templateCorners ↔ i.val % 2 = 1) ∧
    (groupPoint i.val ∈ templateTips ↔ i.val % 2 = 0) := by
  decide +kernel

theorem group_point_mem : ∀ i : Fin 8, groupPoint i.val ∈ templateSites := by
  decide +kernel

theorem optionAt_ring (a : Input) (ha : a.axes.length = 4) (hc : a.corners.length = 4)
    (i : Nat) (hi : i < 8) :
    a.optionAt (ringSites.getD i (0,0)) = (ringOptions a.axes a.corners).getD i ⟨0,0⟩ := by
  obtain ⟨a0,a1,a2,a3,ha⟩ := List.length_eq_four.mp ha
  obtain ⟨c0,c1,c2,c3,hc⟩ := List.length_eq_four.mp hc
  interval_cases i <;>
    simp [Input.optionAt, ringOptions, ringSites, ha, hc, List.range_succ]

def rawStatus (s : RawOption) : Status :=
  if s.status == 1 then .U else if s.status == 2 then .D else .X

theorem input_status_ring (a : Input) (i : Nat) (hi : i < 8) :
    (inputPattern a).statusAt (ringSites.getD i (0,0)) =
      rawStatus (a.optionAt (ringSites.getD i (0,0))) := by
  have hm := ring_point_mem ⟨i,hi⟩
  have hn := ring_point_not_center ⟨i,hi⟩
  have ht := ring_point_not_tip ⟨i,hi⟩
  have htb : ([(2,0),(0,2),(-2,0),(0,-2)] : List Plane).contains
      (ringSites.getD i (0,0)) = false := by
    apply Bool.eq_false_iff.mpr
    simpa [List.contains_iff_mem, templateTips] using ht
  rw [PatternData.statusAt, dif_pos hm]
  dsimp only [inputPattern]
  simp only [htb, Bool.or_false, beq_iff_eq, hn, ↓reduceIte, rawStatus]

theorem input_status_tip (a : Input) (x : Plane) (hx : x ∈ templateTips) :
    (inputPattern a).statusAt x = .U := by
  have hm : x ∈ templateSites := by
    simp only [templateTips, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel
  have ht : ([(2,0),(0,2),(-2,0),(0,-2)] : List Plane).contains x = true := by
    simpa [List.contains_iff_mem, templateTips] using hx
  rw [PatternData.statusAt, dif_pos hm]
  dsimp only [inputPattern]
  simp only [ht, Bool.or_true, ↓reduceIte]

def directionIndex : Compass → Nat
  | .east => 0 | .north => 1 | .west => 2 | .south => 3

theorem compass_direction (d : Compass) (k : Nat) (hk : k < 4) :
    (compassAt k).step = d.step ↔ k = directionIndex d := by
  cases d <;> interval_cases k <;> decide +kernel

theorem input_kept_direction (a : Input) (x : Plane) (hx : x ∈ templateSites)
    (hn : x ≠ (0,0)) (d : Compass) :
    x + d.step ∈ (inputPattern a).keptAt x ↔ hasDirection (a.optionAt x).mask (directionIndex d) = true := by
  simp only [PatternData.keptAt, dif_pos hx, inputPattern, hn, beq_iff_eq, ↓reduceIte,
    Finset.mem_image, List.mem_toFinset, List.mem_map, List.mem_filter, List.mem_range]
  simp only [add_left_cancel_iff]
  constructor
  · rintro ⟨c,⟨k,⟨hk,hm⟩,rfl⟩,he⟩
    have he' := (compass_direction d k hk).mp he
    simpa only [he'] using hm
  · intro hm
    refine ⟨compassAt (directionIndex d), ⟨directionIndex d, ⟨?_,hm⟩, rfl⟩, ?_⟩
    · cases d <;> decide +kernel
    · cases d <;> rfl

theorem rawStatus_live (s : RawOption) (hs : s.status ≤ 2) :
    rawStatus s ≠ .X ↔ s.status ≠ 0 := by
  unfold rawStatus
  simp only [beq_iff_eq]
  split_ifs <;> simp_all <;> omega

theorem rawStatus_D (s : RawOption) : rawStatus s = .D ↔ s.status = 2 := by
  unfold rawStatus
  simp only [beq_iff_eq]
  split_ifs <;> simp_all

theorem input_lengths (a : Input) (ha : inputCheck a = true) :
    a.axes.length = 4 ∧ a.corners.length = 4 := by
  simp only [inputCheck, Bool.and_eq_true, beq_iff_eq] at ha
  exact ⟨ha.1.1.1.1.1.1.1.1, ha.1.1.1.1.1.1.1.2⟩

theorem corner_status_le (s : RawOption) (hs : s ∈ cornerOptions) : s.status ≤ 2 := by
  simp only [cornerOptions, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem axial_status_le (j : Nat) (s : RawOption) (hs : s ∈ axialOptions j) : s.status ≤ 2 := by
  unfold axialOptions at hs
  split_ifs at hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> norm_num
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hs
    rcases hs with (rfl | rfl) | ⟨k,hk,rfl⟩ <;> norm_num

theorem input_status_le (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status ≤ 2 := by
  have hl := input_lengths a ha
  have ha' := ha
  simp only [inputCheck, Bool.and_eq_true, beq_iff_eq] at ha'
  have haxes := ha'.1.1.1.1.1.2
  have hcorners := ha'.1.1.1.1.2
  simp only [List.all_eq_true] at haxes hcorners
  have hj : i/2 < 4 := by omega
  have hjaxes : i/2 < a.axes.length := by omega
  have hjcorners : i/2 < a.corners.length := by omega
  have haxmem : (a.axes[i/2],i/2) ∈ a.axes.zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr; simp [hjaxes]
  have hcomem : (a.corners[i/2],i/2) ∈ a.corners.zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr; simp [hjcorners]
  have hax := haxes _ haxmem
  have hco := hcorners _ hcomem
  simp only [Bool.and_eq_true] at hco
  have haxi : a.axes[i/2] ∈ axialOptions (i/2) := by simpa using hax
  have hcoi : a.corners[i/2] ∈ cornerOptions := by simpa using hco.1
  unfold ringOptions
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  split_ifs
  · rw [List.getD_eq_getElem _ _ hjaxes]
    exact axial_status_le _ _ haxi
  · rw [List.getD_eq_getElem _ _ hjcorners]
    exact corner_status_le _ hcoi

def bondCondition (π : PatternData) (x y : Plane) : Prop :=
  π.statusAt x ≠ .X ∧ π.statusAt y ≠ .X ∧
    (x ∈ templateTips ∨ y ∈ π.keptAt x) ∧ (y ∈ templateTips ∨ x ∈ π.keptAt y)

instance bondCondition_decidable (π : PatternData) (x y : Plane) :
    Decidable (bondCondition π x y) := Classical.propDecidable _

theorem bondCondition_symm (π : PatternData) (x y : Plane) :
    bondCondition π x y ↔ bondCondition π y x := by unfold bondCondition; tauto

theorem degree_incident (π : PatternData) (i : Nat) (hi : i < 8) :
    patternDegree π (groupPoint i) =
      ((incidentEdges i).filter (fun e : Plane × Plane => bondCondition π e.1 e.2)).card := by
  classical
  have he : patternDegree π (groupPoint i) =
      (((internalBonds templateSites).filter (fun e => e.1 = groupPoint i ∨ e.2 = groupPoint i)).filter
        (fun e => bondCondition π e.1 e.2)).card := by
    unfold patternDegree
    congr 1
    apply Finset.ext
    intro e
    simp only [Finset.mem_filter]
    have hb : e ∈ π.bonds ↔ e ∈ internalBonds templateSites ∧ bondCondition π e.1 e.2 := by
      change (e ∈ (internalBonds templateSites).filter _) ↔ _
      rw [Finset.mem_filter]
      rfl
    rw [hb]
    tauto
  rw [he, incident_template ⟨i,hi⟩]

def cycleBool (π : PatternData) (i : Nat) : Bool :=
  decide (bondCondition π (ringSites.getD i (0,0)) (ringSites.getD ((i+1)%8) (0,0)))

def tipBool (π : PatternData) (i : Nat) : Bool :=
  decide (bondCondition π (ringSites.getD i (0,0)) (groupPoint i))

theorem card_filter_one {α : Type*} [DecidableEq α] (x : α)
    (p : α → Prop) [DecidablePred p] :
    (({x} : Finset α).filter p).card = (decide (p x)).toNat := by
  rw [Finset.card_filter, Finset.sum_singleton]
  by_cases h : p x <;> simp [h]

theorem card_filter_two {α : Type*} [DecidableEq α] (x y : α) (hne : x ≠ y)
    (p : α → Prop) [DecidablePred p] :
    (({x,y} : Finset α).filter p).card = (decide (p x)).toNat + (decide (p y)).toNat := by
  rw [Finset.card_filter, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  by_cases hx : p x <;> by_cases hy : p y <;> simp [hx,hy]

theorem decide_toNat (p : Prop) [Decidable p] : (decide p).toNat = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

theorem degree_bools (π : PatternData) (i : Nat) (hi : i < 8) :
    patternDegree π (groupPoint i) =
      if i%2 = 0 then (tipBool π i).toNat
      else (cycleBool π i).toNat + (cycleBool π ((i+7)%8)).toNat := by
  classical
  rw [degree_incident π i hi]
  interval_cases i <;> norm_num only [incidentEdges, ite_true, ite_false]
  all_goals first
    | rw [card_filter_one]
    | rw [card_filter_two (((0,1),(1,1)) : Plane × Plane) ((1,0),(1,1)) (by decide +kernel)]
    | rw [card_filter_two (((-1,1),(0,1)) : Plane × Plane) ((-1,0),(-1,1)) (by decide +kernel)]
    | rw [card_filter_two (((-1,-1),(0,-1)) : Plane × Plane) ((-1,-1),(-1,0)) (by decide +kernel)]
    | rw [card_filter_two (((0,-1),(1,-1)) : Plane × Plane) ((1,-1),(1,0)) (by decide +kernel)]
  all_goals norm_num only [cycleBool, tipBool, groupPoint, ringSites,
    List.getD_cons_succ, List.getD_cons_zero, ite_true, ite_false]
  all_goals simp only [decide_toNat, bondCondition_symm, Nat.add_comm,
    beq_self_eq_true, ↓reduceIte]

theorem cycle_neighbors : ∀ i : Fin 8,
    ringSites.getD ((i.val+1)%8) (0,0) = ringSites.getD i.val (0,0) +
      (compassAt (edgeDirections.getD i.val 0)).step ∧
    ringSites.getD i.val (0,0) = ringSites.getD ((i.val+1)%8) (0,0) +
      (compassAt ((edgeDirections.getD i.val 0+2)%4)).step := by
  decide +kernel

theorem tip_neighbors : ∀ i : Fin 8, i.val%2 = 0 →
    groupPoint i.val = ringSites.getD i.val (0,0) + (compassAt (i.val/2)).step := by
  decide +kernel

theorem compass_index (k : Nat) (hk : k < 4) : directionIndex (compassAt k) = k := by
  interval_cases k <;> rfl

theorem edge_direction_lt (i : Nat) (hi : i < 8) : edgeDirections.getD i 0 < 4 := by
  interval_cases i <;> decide +kernel

theorem raw_cycle (a : Input) (i : Nat) (hi : i < 8) :
    (rawEdges a.axes a.corners).getD (4+i) false =
      (((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status != 0 &&
       ((ringOptions a.axes a.corners).getD ((i+1)%8) ⟨0,0⟩).status != 0 &&
       hasDirection ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).mask (edgeDirections.getD i 0) &&
       hasDirection ((ringOptions a.axes a.corners).getD ((i+1)%8) ⟨0,0⟩).mask
         ((edgeDirections.getD i 0+2)%4)) := by
  interval_cases i <;> simp [rawEdges, List.range_succ]

theorem raw_tip (a : Input) (i : Nat) (hi : i < 8) :
    (rawEdges a.axes a.corners).getD (12+i/2) false =
      ((a.axes.getD (i/2) ⟨0,0⟩).status != 0 &&
       hasDirection (a.axes.getD (i/2) ⟨0,0⟩).mask (i/2)) := by
  have hj : i/2 < 4 := by omega
  generalize i/2 = j at *
  interval_cases j <;> simp [rawEdges, List.range_succ]

theorem ring_option_even (a : Input) (i : Nat) (hi : i < 8) (he : i%2 = 0) :
    (ringOptions a.axes a.corners).getD i ⟨0,0⟩ = a.axes.getD (i/2) ⟨0,0⟩ := by
  unfold ringOptions
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  simp only [he, beq_self_eq_true, ↓reduceIte]

theorem cycleBool_input (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    cycleBool (inputPattern a) i = (rawEdges a.axes a.corners).getD (4+i) false := by
  classical
  have hl := input_lengths a ha
  have hj : (i+1)%8 < 8 := Nat.mod_lt _ (by omega)
  have hni := ring_point_not_tip ⟨i,hi⟩
  have hnj := ring_point_not_tip ⟨(i+1)%8,hj⟩
  have hli : (inputPattern a).statusAt (ringSites.getD i (0,0)) ≠ .X ↔
      ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status ≠ 0 := by
    rw [input_status_ring a i hi, optionAt_ring a hl.1 hl.2 i hi]
    exact rawStatus_live _ (input_status_le a ha i hi)
  have hlj : (inputPattern a).statusAt (ringSites.getD ((i+1)%8) (0,0)) ≠ .X ↔
      ((ringOptions a.axes a.corners).getD ((i+1)%8) ⟨0,0⟩).status ≠ 0 := by
    rw [input_status_ring a _ hj, optionAt_ring a hl.1 hl.2 _ hj]
    exact rawStatus_live _ (input_status_le a ha _ hj)
  have hki : ringSites.getD ((i+1)%8) (0,0) ∈
      (inputPattern a).keptAt (ringSites.getD i (0,0)) ↔
      hasDirection ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).mask (edgeDirections.getD i 0) = true := by
    have h := input_kept_direction a _ (ring_point_mem ⟨i,hi⟩)
      (ring_point_not_center ⟨i,hi⟩) (compassAt (edgeDirections.getD i 0))
    rw [← (cycle_neighbors ⟨i,hi⟩).1, optionAt_ring a hl.1 hl.2 i hi,
      compass_index _ (edge_direction_lt i hi)] at h
    exact h
  have hkj : ringSites.getD i (0,0) ∈
      (inputPattern a).keptAt (ringSites.getD ((i+1)%8) (0,0)) ↔
      hasDirection ((ringOptions a.axes a.corners).getD ((i+1)%8) ⟨0,0⟩).mask
        ((edgeDirections.getD i 0+2)%4) = true := by
    have h := input_kept_direction a _ (ring_point_mem ⟨(i+1)%8,hj⟩)
      (ring_point_not_center ⟨(i+1)%8,hj⟩) (compassAt ((edgeDirections.getD i 0+2)%4))
    rw [← (cycle_neighbors ⟨i,hi⟩).2, optionAt_ring a hl.1 hl.2 _ hj,
      compass_index _ (Nat.mod_lt _ (by omega))] at h
    exact h
  rw [raw_cycle a i hi]
  apply Bool.eq_iff_iff.mpr
  simp only [cycleBool, decide_eq_true_eq, bondCondition, hni, hnj, false_or,
    hli, hlj, hki, hkj, Bool.and_eq_true, bne_iff_ne, and_assoc]

theorem tipBool_input (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8)
    (he : i%2 = 0) :
    tipBool (inputPattern a) i = (rawEdges a.axes a.corners).getD (12+i/2) false := by
  classical
  have hl := input_lengths a ha
  have htip : groupPoint i ∈ templateTips := ((point_kinds ⟨i,hi⟩).2).mpr he
  have hni := ring_point_not_tip ⟨i,hi⟩
  have hli : (inputPattern a).statusAt (ringSites.getD i (0,0)) ≠ .X ↔
      (a.axes.getD (i/2) ⟨0,0⟩).status ≠ 0 := by
    rw [input_status_ring a i hi, optionAt_ring a hl.1 hl.2 i hi]
    rw [rawStatus_live _ (input_status_le a ha i hi), ring_option_even a i hi he]
  have hki : groupPoint i ∈ (inputPattern a).keptAt (ringSites.getD i (0,0)) ↔
      hasDirection (a.axes.getD (i/2) ⟨0,0⟩).mask (i/2) = true := by
    have h := input_kept_direction a _ (ring_point_mem ⟨i,hi⟩)
      (ring_point_not_center ⟨i,hi⟩) (compassAt (i/2))
    rw [← tip_neighbors ⟨i,hi⟩ he, optionAt_ring a hl.1 hl.2 i hi,
      ring_option_even a i hi he, compass_index _ (by omega)] at h
    exact h
  rw [raw_tip a i hi]
  apply Bool.eq_iff_iff.mpr
  simp only [tipBool, decide_eq_true_eq, bondCondition, hni, htip, false_or, true_or,
    input_status_tip a _ htip, hli, hki, Bool.and_eq_true, bne_iff_ne, and_true,
    Status.noConfusion, ne_eq, reduceCtorEq, not_false_eq_true, true_and]

theorem input_degree (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    patternDegree (inputPattern a) (groupPoint i) =
      if i%2 = 0 then ((rawEdges a.axes a.corners).getD (12+i/2) false).toNat
      else ((rawEdges a.axes a.corners).getD (4+i) false).toNat +
        ((rawEdges a.axes a.corners).getD (4+(i+7)%8) false).toNat := by
  rw [degree_bools (inputPattern a) i hi]
  split_ifs with he
  · rw [tipBool_input a ha i hi he]
  · rw [cycleBool_input a ha i hi, cycleBool_input a ha _ (Nat.mod_lt _ (by omega))]

theorem input_slots (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    inputSlots a i = groupSlots (inputPattern a) (inputRepresentation a) (groupPoint i) := by
  classical
  have hd := input_degree a ha i hi
  have hk := point_kinds ⟨i,hi⟩
  change (groupPoint i ∈ templateCorners ↔ i%2=1) ∧
    (groupPoint i ∈ templateTips ↔ i%2=0) at hk
  have hm : groupPoint i ∈ templateCorners ∪ templateTips := by
    rw [← group_points]
    simp only [List.mem_toFinset, List.mem_map, positions, List.mem_range]
    exact ⟨i,hi,rfl⟩
  by_cases he : i%2 = 0
  · have hnc : groupPoint i ∉ templateCorners := by
      intro h
      have := hk.1.mp h
      omega
    have hp : groupIsPair (inputPattern a) (inputRepresentation a) (groupPoint i) = false := by
      simp [groupIsPair, hnc]
    cases hb : (rawEdges a.axes a.corners).getD (12+i/2) false <;>
      simp only [List.getD] at hb <;>
      simp [he, hb] at hd <;>
      simp [inputSlots, he, hb, groupSlots, reductionGroups, hm, hd, hp]
  · have he' : i%2 = 1 := by omega
    have hc := hk.1.mpr he'
    have ht : groupPoint i ∉ templateTips := by intro h; exact he (hk.2.mp h)
    cases hr : a.leafReduced <;>
      cases hb : (rawEdges a.axes a.corners).getD (4+i) false <;>
      cases hb' : (rawEdges a.axes a.corners).getD (4+(i+7)%8) false <;>
      simp only [List.getD] at hb hb' <;>
      simp [he, hb, hb'] at hd <;>
      simp [inputSlots, he, hb, hb', hr, groupSlots, reductionGroups, hm, hd,
        groupIsPair, SingleReplacement, hc, ht, inputRepresentation]

theorem input_dimensions (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    inputDimension a i = groupDim (inputPattern a) (inputRepresentation a) (groupPoint i) := by
  classical
  have hs := input_slots a ha i hi
  by_cases h0 : inputSlots a i = 0
  · simp [inputDimension, groupDim, ← hs, h0]
  by_cases h1 : inputSlots a i = 1
  · simp [inputDimension, groupDim, ← hs, h1]
  have hp : groupIsPair (inputPattern a) (inputRepresentation a) (groupPoint i) = true := by
    by_contra hn
    have hn' : groupIsPair (inputPattern a) (inputRepresentation a) (groupPoint i) = false :=
      Bool.eq_false_iff.mpr hn
    by_cases hm : groupPoint i ∈ reductionGroups (inputPattern a) <;>
      simp [groupSlots, hm, hn'] at hs <;> omega
  have hpoint := paired_point (inputPattern a) (inputRepresentation a) i hi hp
  have hl := input_lengths a ha
  have hstatus : (inputPattern a).statusAt (groupPoint i) = .D ↔
      ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status = 2 := by
    rw [hpoint, input_status_ring a i hi, optionAt_ring a hl.1 hl.2 i hi, rawStatus_D]
  simp [inputDimension, groupDim, ← hs, h0, h1, hstatus]

theorem input_diluted (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    (inputSpec a i).diluted = decide ((inputPattern a).statusAt (ringSites.getD i (0,0)) = .D) := by
  classical
  have hl := input_lengths a ha
  apply Bool.eq_iff_iff.mpr
  simp only [inputSpec, beq_iff_eq, decide_eq_true_eq, input_status_ring a i hi,
    optionAt_ring a hl.1 hl.2 i hi, rawStatus_D]

theorem checked_spec (a : Input) (ss : List PackedSite) (hg : geometryCheck a ss = true)
    (i : Nat) (hi : i < 8) : (siteAt ss i).spec = inputSpec a i := by
  simp only [geometryCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hg
  have hi' : i < ss.length := by omega
  have hm : (ss[i],i) ∈ ss.zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    simp [hi']
  simpa only [siteAt, List.getD_eq_getElem ss zeroSite hi'] using hg.2 _ hm

theorem checked_coordinates (a : Input) (ha : inputCheck a = true)
    (ss : List PackedSite) (hg : geometryCheck a ss = true) :
    CoordinateGeometry (inputPattern a) (inputRepresentation a) ss := by
  have hl : ss.length = 8 := by
    have hg' := hg
    simp only [geometryCheck, Bool.and_eq_true, beq_iff_eq] at hg'
    exact hg'.1
  have hdims : ss.map (fun s => s.spec.dim) = positions.map (inputDimension a) := by
    rw [list_sites ss hl, List.map_map]
    apply List.map_congr_left
    intro i hi
    rw [Function.comp_apply, checked_spec a ss hg i (by simpa [positions] using hi)]
    rfl
  refine ⟨hl, ?_⟩
  intro i hi
  rw [checked_spec a ss hg i hi]
  refine ⟨input_slots a ha i hi, input_dimensions a ha i hi, input_diluted a ha i hi, ?_⟩
  change (((List.range 8).drop (i+1)).map (inputDimension a)).prod = _
  rw [List.map_drop, List.map_drop, hdims]
  rfl

end AKLT.W.H1C013
