module
public import AKLT.W.H1C008.InputFacts

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C008

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

private theorem mem_internalBonds {G : Finset Plane} {s t : Plane} :
    (s,t) ∈ internalBonds G ↔ s ∈ G ∧ t ∈ G ∧
      (t = (s.1+1,s.2) ∨ t = (s.1,s.2+1)) := by
  simp [internalBonds, positiveNeighbours, and_assoc, and_left_comm, and_comm]

private def candidateEdges (x : Plane) : Finset (Plane × Plane) :=
  {((x.1 - 1, x.2), x), ((x.1, x.2 - 1), x), (x, (x.1 + 1, x.2)),
    (x, (x.1, x.2 + 1))}

private theorem incident_candidate {x : Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds templateSites) :
    (e.1 = x ∨ e.2 = x) ↔ e ∈ candidateEdges x := by
  rcases e with ⟨s,t⟩
  obtain ⟨_,_,ht⟩ := mem_internalBonds.mp he
  rcases ht with rfl | rfl <;>
    cases s with | mk sx sy =>
    cases x with | mk xx xy =>
    simp [candidateEdges] <;> omega

private theorem patternDegree_candidate (π : PatternData) (x : Plane) :
    patternDegree π x = ((candidateEdges x).filter (fun e => e ∈ π.bonds)).card := by
  classical
  have hset : π.bonds.filter (fun e => e.1 = x ∨ e.2 = x) =
      (candidateEdges x).filter (fun e => e ∈ π.bonds) := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨heBond, hinc⟩
      exact ⟨(incident_candidate (Finset.mem_filter.mp heBond).1).mp hinc, heBond⟩
    · rintro ⟨heCand, heBond⟩
      exact ⟨heBond, (incident_candidate (Finset.mem_filter.mp heBond).1).mpr heCand⟩
  exact congrArg Finset.card hset

private theorem status_ne_X (s : Nat) (hs : s ≤ 2) :
    (if s = 1 then Status.U else if s = 2 then Status.D else Status.X) ≠ .X ↔
      s ≠ 0 := by
  have : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  rcases this with rfl | rfl | rfl <;> simp

private theorem optionAt_ring (a : Input) (i : Nat) (hi : i < 8) :
    a.optionAt (ringSites.getD i (0,0)) =
      (ringOptions a.axes a.corners).getD i ⟨0,0⟩ := by
  interval_cases i <;>
    simp [Input.optionAt, ringSites, ringOptions, List.range_succ]

private theorem keptAt_iff (a : Input) (x y : Plane)
    (hx : x ∈ templateSites) (h0 : x ≠ (0,0)) :
    y ∈ (inputPattern a).keptAt x ↔
      ∃ d < 4, hasDirection (a.optionAt x).mask d = true ∧
        x + (compassAt d).step = y := by
  simp [PatternData.keptAt, hx, inputPattern, h0, List.mem_filter, List.mem_map,
    and_assoc]

private theorem keptAt_explicit (a : Input) (x y : Plane)
    (hx : x ∈ templateSites) (h0 : x ≠ (0,0)) :
    y ∈ (inputPattern a).keptAt x ↔
      (hasDirection (a.optionAt x).mask 0 = true ∧ x + (1,0) = y) ∨
      (hasDirection (a.optionAt x).mask 1 = true ∧ x + (0,1) = y) ∨
      (hasDirection (a.optionAt x).mask 2 = true ∧ x + (-1,0) = y) ∨
      (hasDirection (a.optionAt x).mask 3 = true ∧ x + (0,-1) = y) := by
  rw [keptAt_iff a x y hx h0]
  constructor
  · rintro ⟨d,hd,hm,hp⟩
    interval_cases d <;> simp [compassAt, Compass.step] at hp <;> aesop
  · intro h
    rcases h with h | h | h | h
    · exact ⟨0, by omega, h.1, by simpa [compassAt, Compass.step] using h.2⟩
    · exact ⟨1, by omega, h.1, by simpa [compassAt, Compass.step] using h.2⟩
    · exact ⟨2, by omega, h.1, by simpa [compassAt, Compass.step] using h.2⟩
    · exact ⟨3, by omega, h.1, by simpa [compassAt, Compass.step] using h.2⟩

private theorem statusAt_ring (a : Input) (i : Nat) (hi : i < 8) :
    (inputPattern a).statusAt (ringSites.getD i (0,0)) =
      (if ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status == 1 then .U
       else if ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status == 2 then .D else .X) := by
  have hop := optionAt_ring a i hi
  interval_cases i <;>
    simp_all [PatternData.statusAt, inputPattern, templateSites, square, latticeDist,
      ringSites]

private theorem ring_live (a : Input) (hs : ValidStatuses a) (i : Nat) (hi : i < 8) :
    (inputPattern a).statusAt (ringSites.getD i (0,0)) ≠ .X ↔
      ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status ≠ 0 := by
  have hbound : ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status ≤ 2 := by
    by_cases he : i % 2 = 0
    · simpa [ringOptions, hi, he] using hs.1 (i/2)
    · simpa [ringOptions, hi, he] using hs.2 (i/2)
  rw [statusAt_ring a i hi]
  simpa only [beq_iff_eq] using status_ne_X _ hbound

private theorem tip0 (a : Input) (hs : ValidStatuses a) :
    ((1,0),(2,0)) ∈ (inputPattern a).bonds ↔
      (rawEdges a.axes a.corners).getD 12 false = true := by
  have hstatus := ring_live a hs 0 (by omega)
  have hopt := optionAt_ring a 0 (by omega)
  have hkept := keptAt_explicit a (1,0) (2,0) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  simp [ringSites, ringOptions, List.range_succ] at hstatus hopt
  have htip : (inputPattern a).statusAt (2,0) = .U := by
    norm_num [PatternData.statusAt, inputPattern, templateSites, square, latticeDist]
  simp only [PatternData.bonds, Finset.mem_filter]
  simp only [ne_eq, hstatus, htip]
  norm_num [mem_internalBonds, templateSites, square, latticeDist, templateTips]
  rw [hkept]
  simp [hopt, rawEdges, List.range_succ, and_comm]

private theorem tip1 (a : Input) (hs : ValidStatuses a) :
    ((0,1),(0,2)) ∈ (inputPattern a).bonds ↔
      (rawEdges a.axes a.corners).getD 13 false = true := by
  have hstatus := ring_live a hs 2 (by omega)
  have hopt := optionAt_ring a 2 (by omega)
  have hkept := keptAt_explicit a (0,1) (0,2) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  simp [ringSites, ringOptions, List.range_succ] at hstatus hopt
  have htip : (inputPattern a).statusAt (0,2) = .U := by
    norm_num [PatternData.statusAt, inputPattern, templateSites, square, latticeDist]
  simp only [PatternData.bonds, Finset.mem_filter]
  simp only [ne_eq, hstatus, htip]
  norm_num [mem_internalBonds, templateSites, square, latticeDist, templateTips]
  rw [hkept]
  simp [hopt, rawEdges, List.range_succ, and_comm]

private theorem tip2 (a : Input) (hs : ValidStatuses a) :
    ((-2,0),(-1,0)) ∈ (inputPattern a).bonds ↔
      (rawEdges a.axes a.corners).getD 14 false = true := by
  have hstatus := ring_live a hs 4 (by omega)
  have hopt := optionAt_ring a 4 (by omega)
  have hkept := keptAt_explicit a (-1,0) (-2,0) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  simp [ringSites, ringOptions, List.range_succ] at hstatus hopt
  have htip : (inputPattern a).statusAt (-2,0) = .U := by
    norm_num [PatternData.statusAt, inputPattern, templateSites, square, latticeDist]
  simp only [PatternData.bonds, Finset.mem_filter]
  simp only [ne_eq, hstatus, htip]
  norm_num [mem_internalBonds, templateSites, square, latticeDist, templateTips]
  rw [hkept]
  simp [hopt, rawEdges, List.range_succ, and_comm]

private theorem tip3 (a : Input) (hs : ValidStatuses a) :
    ((0,-2),(0,-1)) ∈ (inputPattern a).bonds ↔
      (rawEdges a.axes a.corners).getD 15 false = true := by
  have hstatus := ring_live a hs 6 (by omega)
  have hopt := optionAt_ring a 6 (by omega)
  have hkept := keptAt_explicit a (0,-1) (0,-2) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  simp [ringSites, ringOptions, List.range_succ] at hstatus hopt
  have htip : (inputPattern a).statusAt (0,-2) = .U := by
    norm_num [PatternData.statusAt, inputPattern, templateSites, square, latticeDist]
  simp only [PatternData.bonds, Finset.mem_filter]
  simp only [ne_eq, hstatus, htip]
  norm_num [mem_internalBonds, templateSites, square, latticeDist, templateTips]
  rw [hkept]
  simp [hopt, rawEdges, List.range_succ, and_comm]

private theorem cycle0 (a : Input) (hs : ValidStatuses a) :
    ((1,0),(1,1)) ∈ (inputPattern a).bonds ↔
      (rawEdges a.axes a.corners).getD 4 false = true := by
  have hs0 := ring_live a hs 0 (by omega)
  have hs1 := ring_live a hs 1 (by omega)
  have ho0 := optionAt_ring a 0 (by omega)
  have ho1 := optionAt_ring a 1 (by omega)
  have hk0 := keptAt_explicit a (1,0) (1,1) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  have hk1 := keptAt_explicit a (1,1) (1,0) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  simp [ringSites, ringOptions, List.range_succ] at hs0 hs1 ho0 ho1
  simp only [PatternData.bonds, Finset.mem_filter]
  simp only [ne_eq, hs0, hs1]
  norm_num [mem_internalBonds, templateSites, square, latticeDist, templateTips]
  rw [hk0, hk1]
  simp [ho0, ho1, rawEdges, ringOptions, edgeDirections, List.range_succ,
    and_assoc, and_left_comm, and_comm]

private theorem cycle1 (a : Input) (hs : ValidStatuses a) :
    ((0,1),(1,1)) ∈ (inputPattern a).bonds ↔
      (rawEdges a.axes a.corners).getD 5 false = true := by
  have hs0 := ring_live a hs 1 (by omega)
  have hs1 := ring_live a hs 2 (by omega)
  have ho0 := optionAt_ring a 1 (by omega)
  have ho1 := optionAt_ring a 2 (by omega)
  have hk0 := keptAt_explicit a (1,1) (0,1) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  have hk1 := keptAt_explicit a (0,1) (1,1) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  simp [ringSites, ringOptions, List.range_succ] at hs0 hs1 ho0 ho1
  simp only [PatternData.bonds, Finset.mem_filter]
  simp only [ne_eq, hs0, hs1]
  norm_num [mem_internalBonds, templateSites, square, latticeDist, templateTips]
  rw [hk0, hk1]
  simp [ho0, ho1, rawEdges, ringOptions, edgeDirections, List.range_succ,
    and_assoc, and_left_comm, and_comm]

private theorem cycle2 (a : Input) (hs : ValidStatuses a) :
    ((-1,1),(0,1)) ∈ (inputPattern a).bonds ↔
      (rawEdges a.axes a.corners).getD 6 false = true := by
  have hs0 := ring_live a hs 2 (by omega)
  have hs1 := ring_live a hs 3 (by omega)
  have ho0 := optionAt_ring a 2 (by omega)
  have ho1 := optionAt_ring a 3 (by omega)
  have hk0 := keptAt_explicit a (0,1) (-1,1) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  have hk1 := keptAt_explicit a (-1,1) (0,1) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  simp [ringSites, ringOptions, List.range_succ] at hs0 hs1 ho0 ho1
  simp only [PatternData.bonds, Finset.mem_filter]
  simp only [ne_eq, hs0, hs1]
  norm_num [mem_internalBonds, templateSites, square, latticeDist, templateTips]
  rw [hk0, hk1]
  simp [ho0, ho1, rawEdges, ringOptions, edgeDirections, List.range_succ,
    and_assoc, and_left_comm, and_comm]

private theorem cycle3 (a : Input) (hs : ValidStatuses a) :
    ((-1,0),(-1,1)) ∈ (inputPattern a).bonds ↔
      (rawEdges a.axes a.corners).getD 7 false = true := by
  have hs0 := ring_live a hs 3 (by omega)
  have hs1 := ring_live a hs 4 (by omega)
  have ho0 := optionAt_ring a 3 (by omega)
  have ho1 := optionAt_ring a 4 (by omega)
  have hk0 := keptAt_explicit a (-1,1) (-1,0) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  have hk1 := keptAt_explicit a (-1,0) (-1,1) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  simp [ringSites, ringOptions, List.range_succ] at hs0 hs1 ho0 ho1
  simp only [PatternData.bonds, Finset.mem_filter]
  simp only [ne_eq, hs0, hs1]
  norm_num [mem_internalBonds, templateSites, square, latticeDist, templateTips]
  rw [hk0, hk1]
  simp [ho0, ho1, rawEdges, ringOptions, edgeDirections, List.range_succ,
    and_assoc, and_left_comm, and_comm]

private theorem cycle4 (a : Input) (hs : ValidStatuses a) :
    ((-1,-1),(-1,0)) ∈ (inputPattern a).bonds ↔
      (rawEdges a.axes a.corners).getD 8 false = true := by
  have hs0 := ring_live a hs 4 (by omega)
  have hs1 := ring_live a hs 5 (by omega)
  have ho0 := optionAt_ring a 4 (by omega)
  have ho1 := optionAt_ring a 5 (by omega)
  have hk0 := keptAt_explicit a (-1,0) (-1,-1) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  have hk1 := keptAt_explicit a (-1,-1) (-1,0) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  simp [ringSites, ringOptions, List.range_succ] at hs0 hs1 ho0 ho1
  simp only [PatternData.bonds, Finset.mem_filter]
  simp only [ne_eq, hs0, hs1]
  norm_num [mem_internalBonds, templateSites, square, latticeDist, templateTips]
  rw [hk0, hk1]
  simp [ho0, ho1, rawEdges, ringOptions, edgeDirections, List.range_succ,
    and_assoc, and_left_comm, and_comm]

private theorem cycle5 (a : Input) (hs : ValidStatuses a) :
    ((-1,-1),(0,-1)) ∈ (inputPattern a).bonds ↔
      (rawEdges a.axes a.corners).getD 9 false = true := by
  have hs0 := ring_live a hs 5 (by omega)
  have hs1 := ring_live a hs 6 (by omega)
  have ho0 := optionAt_ring a 5 (by omega)
  have ho1 := optionAt_ring a 6 (by omega)
  have hk0 := keptAt_explicit a (-1,-1) (0,-1) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  have hk1 := keptAt_explicit a (0,-1) (-1,-1) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  simp [ringSites, ringOptions, List.range_succ] at hs0 hs1 ho0 ho1
  simp only [PatternData.bonds, Finset.mem_filter]
  simp only [ne_eq, hs0, hs1]
  norm_num [mem_internalBonds, templateSites, square, latticeDist, templateTips]
  rw [hk0, hk1]
  simp [ho0, ho1, rawEdges, ringOptions, edgeDirections, List.range_succ,
    and_assoc, and_left_comm, and_comm]

private theorem cycle6 (a : Input) (hs : ValidStatuses a) :
    ((0,-1),(1,-1)) ∈ (inputPattern a).bonds ↔
      (rawEdges a.axes a.corners).getD 10 false = true := by
  have hs0 := ring_live a hs 6 (by omega)
  have hs1 := ring_live a hs 7 (by omega)
  have ho0 := optionAt_ring a 6 (by omega)
  have ho1 := optionAt_ring a 7 (by omega)
  have hk0 := keptAt_explicit a (0,-1) (1,-1) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  have hk1 := keptAt_explicit a (1,-1) (0,-1) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  simp [ringSites, ringOptions, List.range_succ] at hs0 hs1 ho0 ho1
  simp only [PatternData.bonds, Finset.mem_filter]
  simp only [ne_eq, hs0, hs1]
  norm_num [mem_internalBonds, templateSites, square, latticeDist, templateTips]
  rw [hk0, hk1]
  simp [ho0, ho1, rawEdges, ringOptions, edgeDirections, List.range_succ,
    and_assoc, and_left_comm, and_comm]

private theorem cycle7 (a : Input) (hs : ValidStatuses a) :
    ((1,-1),(1,0)) ∈ (inputPattern a).bonds ↔
      (rawEdges a.axes a.corners).getD 11 false = true := by
  have hs0 := ring_live a hs 7 (by omega)
  have hs1 := ring_live a hs 0 (by omega)
  have ho0 := optionAt_ring a 7 (by omega)
  have ho1 := optionAt_ring a 0 (by omega)
  have hk0 := keptAt_explicit a (1,-1) (1,0) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  have hk1 := keptAt_explicit a (1,0) (1,-1) (by
    norm_num [templateSites, square, latticeDist]) (by decide)
  simp [ringSites, ringOptions, List.range_succ] at hs0 hs1 ho0 ho1
  simp only [PatternData.bonds, Finset.mem_filter]
  simp only [ne_eq, hs0, hs1]
  norm_num [mem_internalBonds, templateSites, square, latticeDist, templateTips]
  rw [hk0, hk1]
  simp [ho0, ho1, rawEdges, ringOptions, edgeDirections, List.range_succ,
    and_assoc, and_left_comm, and_comm]

private theorem bond_not_of_outside (π : PatternData) (s t : Plane)
    (h : s ∉ templateSites ∨ t ∉ templateSites) : (s,t) ∉ π.bonds := by
  intro hb
  obtain ⟨hs,ht,_⟩ := mem_internalBonds.mp (Finset.mem_filter.mp hb).1
  exact h.elim (fun h => h hs) (fun h => h ht)

private theorem degree0 (π : PatternData) :
    patternDegree π (2,0) = (if ((1,0),(2,0)) ∈ π.bonds then 1 else 0) := by
  have hn0 : ((2,-1),(2,0)) ∉ π.bonds :=
    bond_not_of_outside π (2,-1) (2,0) (by
      norm_num [templateSites, square, latticeDist])
  have hn1 : ((2,0),(3,0)) ∉ π.bonds :=
    bond_not_of_outside π (2,0) (3,0) (by
      norm_num [templateSites, square, latticeDist])
  have hn2 : ((2,0),(2,1)) ∉ π.bonds :=
    bond_not_of_outside π (2,0) (2,1) (by
      norm_num [templateSites, square, latticeDist])
  rw [patternDegree_candidate]
  by_cases hb0 : ((1,0),(2,0)) ∈ π.bonds <;>
    norm_num [candidateEdges, Finset.filter_insert, Finset.filter_singleton,
      hn0, hn1, hn2, hb0]

private theorem degree1 (π : PatternData) :
    patternDegree π (1,1) = (if ((0,1),(1,1)) ∈ π.bonds then 1 else 0) + (if ((1,0),(1,1)) ∈ π.bonds then 1 else 0) := by
  have hn0 : ((1,1),(2,1)) ∉ π.bonds :=
    bond_not_of_outside π (1,1) (2,1) (by
      norm_num [templateSites, square, latticeDist])
  have hn1 : ((1,1),(1,2)) ∉ π.bonds :=
    bond_not_of_outside π (1,1) (1,2) (by
      norm_num [templateSites, square, latticeDist])
  rw [patternDegree_candidate]
  by_cases hb0 : ((0,1),(1,1)) ∈ π.bonds <;>
  by_cases hb1 : ((1,0),(1,1)) ∈ π.bonds <;>
    norm_num [candidateEdges, Finset.filter_insert, Finset.filter_singleton,
      hn0, hn1, hb0, hb1]

private theorem degree2 (π : PatternData) :
    patternDegree π (0,2) = (if ((0,1),(0,2)) ∈ π.bonds then 1 else 0) := by
  have hn0 : ((-1,2),(0,2)) ∉ π.bonds :=
    bond_not_of_outside π (-1,2) (0,2) (by
      norm_num [templateSites, square, latticeDist])
  have hn1 : ((0,2),(1,2)) ∉ π.bonds :=
    bond_not_of_outside π (0,2) (1,2) (by
      norm_num [templateSites, square, latticeDist])
  have hn2 : ((0,2),(0,3)) ∉ π.bonds :=
    bond_not_of_outside π (0,2) (0,3) (by
      norm_num [templateSites, square, latticeDist])
  rw [patternDegree_candidate]
  by_cases hb0 : ((0,1),(0,2)) ∈ π.bonds <;>
    norm_num [candidateEdges, Finset.filter_insert, Finset.filter_singleton,
      hn0, hn1, hn2, hb0]

private theorem degree3 (π : PatternData) :
    patternDegree π (-1,1) = (if ((-1,0),(-1,1)) ∈ π.bonds then 1 else 0) + (if ((-1,1),(0,1)) ∈ π.bonds then 1 else 0) := by
  have hn0 : ((-2,1),(-1,1)) ∉ π.bonds :=
    bond_not_of_outside π (-2,1) (-1,1) (by
      norm_num [templateSites, square, latticeDist])
  have hn1 : ((-1,1),(-1,2)) ∉ π.bonds :=
    bond_not_of_outside π (-1,1) (-1,2) (by
      norm_num [templateSites, square, latticeDist])
  rw [patternDegree_candidate]
  by_cases hb0 : ((-1,0),(-1,1)) ∈ π.bonds <;>
  by_cases hb1 : ((-1,1),(0,1)) ∈ π.bonds <;>
    norm_num [candidateEdges, Finset.filter_insert, Finset.filter_singleton,
      hn0, hn1, hb0, hb1]

private theorem degree4 (π : PatternData) :
    patternDegree π (-2,0) = (if ((-2,0),(-1,0)) ∈ π.bonds then 1 else 0) := by
  have hn0 : ((-3,0),(-2,0)) ∉ π.bonds :=
    bond_not_of_outside π (-3,0) (-2,0) (by
      norm_num [templateSites, square, latticeDist])
  have hn1 : ((-2,-1),(-2,0)) ∉ π.bonds :=
    bond_not_of_outside π (-2,-1) (-2,0) (by
      norm_num [templateSites, square, latticeDist])
  have hn2 : ((-2,0),(-2,1)) ∉ π.bonds :=
    bond_not_of_outside π (-2,0) (-2,1) (by
      norm_num [templateSites, square, latticeDist])
  rw [patternDegree_candidate]
  by_cases hb0 : ((-2,0),(-1,0)) ∈ π.bonds <;>
    norm_num [candidateEdges, Finset.filter_insert, Finset.filter_singleton,
      hn0, hn1, hn2, hb0]

private theorem degree5 (π : PatternData) :
    patternDegree π (-1,-1) = (if ((-1,-1),(0,-1)) ∈ π.bonds then 1 else 0) + (if ((-1,-1),(-1,0)) ∈ π.bonds then 1 else 0) := by
  have hn0 : ((-2,-1),(-1,-1)) ∉ π.bonds :=
    bond_not_of_outside π (-2,-1) (-1,-1) (by
      norm_num [templateSites, square, latticeDist])
  have hn1 : ((-1,-2),(-1,-1)) ∉ π.bonds :=
    bond_not_of_outside π (-1,-2) (-1,-1) (by
      norm_num [templateSites, square, latticeDist])
  rw [patternDegree_candidate]
  by_cases hb0 : ((-1,-1),(0,-1)) ∈ π.bonds <;>
  by_cases hb1 : ((-1,-1),(-1,0)) ∈ π.bonds <;>
    norm_num [candidateEdges, Finset.filter_insert, Finset.filter_singleton,
      hn0, hn1, hb0, hb1]

private theorem degree6 (π : PatternData) :
    patternDegree π (0,-2) = (if ((0,-2),(0,-1)) ∈ π.bonds then 1 else 0) := by
  have hn0 : ((-1,-2),(0,-2)) ∉ π.bonds :=
    bond_not_of_outside π (-1,-2) (0,-2) (by
      norm_num [templateSites, square, latticeDist])
  have hn1 : ((0,-3),(0,-2)) ∉ π.bonds :=
    bond_not_of_outside π (0,-3) (0,-2) (by
      norm_num [templateSites, square, latticeDist])
  have hn2 : ((0,-2),(1,-2)) ∉ π.bonds :=
    bond_not_of_outside π (0,-2) (1,-2) (by
      norm_num [templateSites, square, latticeDist])
  rw [patternDegree_candidate]
  by_cases hb0 : ((0,-2),(0,-1)) ∈ π.bonds <;>
    norm_num [candidateEdges, Finset.filter_insert, Finset.filter_singleton,
      hn0, hn1, hn2, hb0]

private theorem degree7 (π : PatternData) :
    patternDegree π (1,-1) = (if ((0,-1),(1,-1)) ∈ π.bonds then 1 else 0) + (if ((1,-1),(1,0)) ∈ π.bonds then 1 else 0) := by
  have hn0 : ((1,-2),(1,-1)) ∉ π.bonds :=
    bond_not_of_outside π (1,-2) (1,-1) (by
      norm_num [templateSites, square, latticeDist])
  have hn1 : ((1,-1),(2,-1)) ∉ π.bonds :=
    bond_not_of_outside π (1,-1) (2,-1) (by
      norm_num [templateSites, square, latticeDist])
  rw [patternDegree_candidate]
  by_cases hb0 : ((0,-1),(1,-1)) ∈ π.bonds <;>
  by_cases hb1 : ((1,-1),(1,0)) ∈ π.bonds <;>
    norm_num [candidateEdges, Finset.filter_insert, Finset.filter_singleton,
      hn0, hn1, hb0, hb1]

/-- The compiler's eight groups, expressed at their original tip/corner sites. -/
def compilerSite (i : Nat) : Plane :=
  ([(2,0),(1,1),(0,2),(-1,1),(-2,0),(-1,-1),(0,-2),(1,-1)] : List Plane).getD i (0,0)

private theorem bool_count (b : Bool) : (if b = true then 1 else 0) = b.toNat := by
  cases b <;> rfl

/-- The raw edge counts agree with the actual internal degree at every group. -/
theorem degree_compilerSite (a : Input) (hs : ValidStatuses a) (i : Nat) (hi : i < 8) :
    patternDegree (inputPattern a) (compilerSite i) =
      if i % 2 = 0 then ((rawEdges a.axes a.corners).getD (12+i/2) false).toNat
      else ((rawEdges a.axes a.corners).getD (4+i) false).toNat +
        ((rawEdges a.axes a.corners).getD (4+(i+7)%8) false).toNat := by
  interval_cases i
  · norm_num [compilerSite]
    rw [degree0]
    simp only [tip0 a hs, bool_count]
    simp [add_comm]
  · norm_num [compilerSite]
    rw [degree1]
    simp only [cycle1 a hs, cycle0 a hs, bool_count]
    simp [add_comm]
  · norm_num [compilerSite]
    rw [degree2]
    simp only [tip1 a hs, bool_count]
    simp [add_comm]
  · norm_num [compilerSite]
    rw [degree3]
    simp only [cycle3 a hs, cycle2 a hs, bool_count]
    simp [add_comm]
  · norm_num [compilerSite]
    rw [degree4]
    simp only [tip2 a hs, bool_count]
    simp [add_comm]
  · norm_num [compilerSite]
    rw [degree5]
    simp only [cycle5 a hs, cycle4 a hs, bool_count]
    simp [add_comm]
  · norm_num [compilerSite]
    rw [degree6]
    simp only [tip3 a hs, bool_count]
    simp [add_comm]
  · norm_num [compilerSite]
    rw [degree7]
    simp only [cycle7 a hs, cycle6 a hs, bool_count]
    simp [add_comm]

#print axioms degree_compilerSite

end AKLT.W.H1C008
