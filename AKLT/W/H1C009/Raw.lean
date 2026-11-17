module
public import AKLT.Cert.H1.Production.Leaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C009
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

instance : LawfulBEq RawOption where
  rfl := by
    rintro ⟨s,m⟩
    change ((s == s) && (m == m)) = true
    simp
  eq_of_beq := by
    rintro ⟨s,m⟩ ⟨t,n⟩ h
    change ((s == t) && (m == n)) = true at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl,rfl⟩
    rfl

theorem ringOptions_explicit (axes corners : List RawOption) :
    ringOptions axes corners =
      [axes.getD 0 ⟨0,0⟩, corners.getD 0 ⟨0,0⟩,
       axes.getD 1 ⟨0,0⟩, corners.getD 1 ⟨0,0⟩,
       axes.getD 2 ⟨0,0⟩, corners.getD 2 ⟨0,0⟩,
       axes.getD 3 ⟨0,0⟩, corners.getD 3 ⟨0,0⟩] := by
  simp [ringOptions, List.range_succ]

theorem optionAt_ring (a : Input) (i : Nat) (hi : i < 8) :
    Input.optionAt a (ringSites.getD i (0,0)) =
      (ringOptions a.axes a.corners).getD i ⟨0,0⟩ := by
  interval_cases i <;> simp [Input.optionAt, ringSites, ringOptions_explicit]

def internalTemplateEdges : List (Plane × Plane) :=
  [((0,0),(1,0)), ((0,0),(0,1)), ((-1,0),(0,0)), ((0,-1),(0,0)),
   ((1,0),(1,1)), ((0,1),(1,1)), ((-1,1),(0,1)), ((-1,0),(-1,1)),
   ((-1,-1),(-1,0)), ((-1,-1),(0,-1)), ((0,-1),(1,-1)), ((1,-1),(1,0)),
   ((1,0),(2,0)), ((0,1),(0,2)), ((-2,0),(-1,0)), ((0,-2),(0,-1))]

theorem internalBonds_explicit :
    internalBonds templateSites = internalTemplateEdges.toFinset := by
  decide +kernel

theorem exists_lt_four (P : Nat → Prop) :
    (∃ d, d < 4 ∧ P d) ↔ P 0 ∨ P 1 ∨ P 2 ∨ P 3 := by
  constructor
  · rintro ⟨d,hd,h⟩
    interval_cases d <;> tauto
  · rintro (h | h | h | h)
    · exact ⟨0,by omega,h⟩
    · exact ⟨1,by omega,h⟩
    · exact ⟨2,by omega,h⟩
    · exact ⟨3,by omega,h⟩

theorem keptAt_input (a : Input) (x y : Plane) (hx : x ∈ templateSites)
    (hne : x ≠ (0,0)) :
    y ∈ (inputPattern a).keptAt x ↔
      (hasDirection (a.optionAt x).mask 0 = true ∧ x + (1,0) = y) ∨
      (hasDirection (a.optionAt x).mask 1 = true ∧ x + (0,1) = y) ∨
      (hasDirection (a.optionAt x).mask 2 = true ∧ x + (-1,0) = y) ∨
      (hasDirection (a.optionAt x).mask 3 = true ∧ x + (0,-1) = y) := by
  simp only [PatternData.keptAt, dite_eq_left hx, inputPattern, beq_iff_eq, ite_eq_right hne,
    Finset.mem_image, List.mem_toFinset, List.mem_map, List.mem_filter, List.mem_range]
  rw [show (∃ d, (∃ i, (i < 4 ∧ hasDirection (a.optionAt x).mask i = true) ∧
      compassAt i = d) ∧ x + d.step = y) ↔
      ∃ i, i < 4 ∧ (hasDirection (a.optionAt x).mask i = true ∧
        x + (compassAt i).step = y) by aesop]
  rw [exists_lt_four]
  simp [compassAt, Compass.step]

theorem axes_valid (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 4) :
    a.axes.getD i ⟨0,0⟩ ∈ axialOptions i := by
  have hh := ha
  simp only [inputCheck, Bool.and_eq_true, beq_iff_eq] at hh
  have hlen : a.axes.length = 4 := by tauto
  have hall : a.axes.zipIdx.all (fun (x,j) => (axialOptions j).contains x) = true := by tauto
  have hj : i < a.axes.length := by omega
  have h := (List.forall_mem_zipIdx'.mp (List.all_eq_true.mp hall)) i hj
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using h

theorem corners_valid (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 4) :
    a.corners.getD i ⟨0,0⟩ ∈ cornerOptions := by
  have hh := ha
  simp only [inputCheck, Bool.and_eq_true, beq_iff_eq] at hh
  have hlen : a.corners.length = 4 := by tauto
  have hall : a.corners.zipIdx.all
      (fun (x,j) => cornerOptions.contains x && cornerCompatible a.axes j x) = true := by tauto
  have hj : i < a.corners.length := by omega
  have h := (List.forall_mem_zipIdx'.mp (List.all_eq_true.mp hall)) i hj
  simp only [Bool.and_eq_true] at h
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using h.1

theorem ring_status_range (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    let s := ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status
    s = 0 ∨ s = 1 ∨ s = 2 := by
  have hax := axes_valid a ha (i/2) (by omega)
  have hco := corners_valid a ha (i/2) (by omega)
  have hsax : (a.axes.getD (i/2) ⟨0,0⟩).status = 0 ∨
      (a.axes.getD (i/2) ⟨0,0⟩).status = 1 ∨
      (a.axes.getD (i/2) ⟨0,0⟩).status = 2 := by
    unfold axialOptions at hax
    split at hax
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hax
      rcases hax with h | h | h | h <;> rw [h] <;> simp
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_map] at hax
      rcases hax with (h | h) | ⟨d,_,h⟩
      · rw [h]; simp
      · rw [h]; simp
      · rw [← h]; simp
  have hsco : (a.corners.getD (i/2) ⟨0,0⟩).status = 0 ∨
      (a.corners.getD (i/2) ⟨0,0⟩).status = 1 ∨
      (a.corners.getD (i/2) ⟨0,0⟩).status = 2 := by
    simp only [cornerOptions, List.mem_cons, List.not_mem_nil, or_false] at hco
    rcases hco with h | h | h | h | h | h | h | h <;> rw [h] <;> simp
  dsimp
  interval_cases i <;> simpa [ringOptions_explicit] using (by assumption)

theorem statusAt_center (a : Input) : (inputPattern a).statusAt (0,0) = .U := by
  simp [PatternData.statusAt, inputPattern, templateSites, square, latticeDist]

theorem statusAt_ring (a : Input) (i : Nat) (hi : i < 8) :
    (inputPattern a).statusAt (ringSites.getD i (0,0)) =
      (if ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status == 1 then .U
      else if ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status == 2 then .D else .X) := by
  have hopt := optionAt_ring a i hi
  have hx : ringSites.getD i (0,0) ∈ templateSites := by
    interval_cases i <;> simp [ringSites, templateSites, square, latticeDist]
  have hne : (ringSites.getD i (0,0) == (0,0)) = false := by
    interval_cases i <;> simp [ringSites]
  have htip : ([(2,0),(0,2),(-2,0),(0,-2)] : List Plane).contains
      (ringSites.getD i (0,0)) = false := by
    interval_cases i <;> simp [ringSites]
  simp only [PatternData.statusAt, dite_eq_left hx, inputPattern, hne, htip,
    Bool.or_self, Bool.false_eq_true, ite_false, hopt]

theorem statusAt_ring_ne (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 8) :
    (inputPattern a).statusAt (ringSites.getD i (0,0)) ≠ .X ↔
      ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status ≠ 0 := by
  rw [statusAt_ring a i hi]
  rcases ring_status_range a ha i hi with h | h | h <;>
    simp only [List.getD_eq_getElem?_getD] at h ⊢ <;> simp [h]

theorem statusAt_ring_diluted (a : Input) (i : Nat) (hi : i < 8) :
    (inputPattern a).statusAt (ringSites.getD i (0,0)) = .D ↔
      ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status = 2 := by
  rw [statusAt_ring a i hi]
  split_ifs <;> simp_all

theorem statusAt_tip (a : Input) (x : Plane) (hx : x ∈ templateTips) :
    (inputPattern a).statusAt x = .U := by
  simp only [templateTips, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp [PatternData.statusAt, inputPattern, templateSites, square, latticeDist]

theorem keptAt_center (a : Input) :
    (inputPattern a).keptAt (0,0) = {(1,0),(0,1),(-1,0)} := by
  simp [PatternData.keptAt, inputPattern, templateSites, square, latticeDist,
    Finset.image_insert, Compass.step]

end AKLT.W.H1C009
