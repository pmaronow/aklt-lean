import AKLT.Cert.H1.Production.Leaves

/-! Normalize irrelevant X/U flags and classify the actual two-direction D masks. -/

namespace AKLT.W.H1C025

open AKLT.Defs AKLT.Cert.H1.Production AKLT.Cert.H1

def dirPoint (x : Plane) (d : Fin 4) : Plane :=
  x + (compassAt d.val).step

def keptDirs (π : PatternData) (x : Plane) : Finset (Fin 4) :=
  Finset.univ.filter fun d => dirPoint x d ∈ π.keptAt x

def keptMask (π : PatternData) (x : Plane) : Nat :=
  (if (0 : Fin 4) ∈ keptDirs π x then 1 else 0) +
  (if (1 : Fin 4) ∈ keptDirs π x then 2 else 0) +
  (if (2 : Fin 4) ∈ keptDirs π x then 4 else 0) +
  (if (3 : Fin 4) ∈ keptDirs π x then 8 else 0)

def rawOptionAt (π : PatternData) (x : Plane) : RawOption :=
  let s := π.statusAt x
  ⟨statusDigit s, if s = .X then 0 else if s = .U then 15 else keptMask π x⟩

def axesOf (π : PatternData) : List RawOption :=
  [rawOptionAt π (1,0), rawOptionAt π (0,1),
   rawOptionAt π (-1,0), rawOptionAt π (0,-1)]

def cornersOf (π : PatternData) : List RawOption :=
  [rawOptionAt π (1,1), rawOptionAt π (-1,1),
   rawOptionAt π (-1,-1), rawOptionAt π (1,-1)]

def compassIndex : Compass → Fin 4
  | .east => 0
  | .north => 1
  | .west => 2
  | .south => 3

theorem keptMask_hasDirection (π : PatternData) (x : Plane) (d : Fin 4) :
    hasDirection (keptMask π x) d.val = decide (d ∈ keptDirs π x) := by
  fin_cases d
  all_goals
    by_cases h0 : (0 : Fin 4) ∈ keptDirs π x
    all_goals
      by_cases h1 : (1 : Fin 4) ∈ keptDirs π x
      all_goals
        by_cases h2 : (2 : Fin 4) ∈ keptDirs π x
        all_goals
          by_cases h3 : (3 : Fin 4) ∈ keptDirs π x
          all_goals norm_num [keptMask, hasDirection, h0, h1, h2, h3]

theorem keptDirs_card (π : PatternData) (x : Plane)
    (hx : x ∈ templateSites) : (keptDirs π x).card = (π.keptAt x).card := by
  classical
  apply Finset.card_bij (fun d _ => dirPoint x d)
  · intro d hd
    simpa [keptDirs] using hd
  · intro d₁ hd₁ d₂ hd₂ heq
    have hs : (compassAt d₁.val).step = (compassAt d₂.val).step := add_left_cancel heq
    apply Fin.ext
    fin_cases d₁ <;> fin_cases d₂ <;>
      simp [compassAt, Compass.step] at hs ⊢
  · intro y hy
    have himage : y ∈ (π.kept ⟨x, hx⟩).image (fun d => x + d.step) := by
      simpa [PatternData.keptAt, hx] using hy
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp himage
    refine ⟨compassIndex c, ?_, ?_⟩
    · cases c <;> simpa [keptDirs, dirPoint, compassAt, compassIndex,
        PatternData.keptAt, hx] using hy
    · cases c <;> simp [dirPoint, compassAt, compassIndex]

def outgoingIndex (c : Compass) : Nat :=
  if c = .east then 0 else if c = .north then 1 else 2

theorem outgoingIndex_lt (π : PatternData) (hπ : π.Covered) :
    outgoingIndex π.outgoing < 3 := by
  have h := hπ.1
  cases π.outgoing <;> simp [outgoingIndex] at h ⊢

instance : LawfulBEq RawOption where
  rfl := by rintro ⟨s,m⟩; change (s == s && m == m) = true; simp
  eq_of_beq := by
    rintro ⟨s,m⟩ ⟨t,n⟩ h
    change (s == t && m == n) = true at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl,rfl⟩
    rfl

theorem rawOption_status (π : PatternData) (x : Plane) :
    (rawOptionAt π x).status = statusDigit (π.statusAt x) := rfl

theorem rawOption_nonzero (π : PatternData) (x : Plane) :
    (rawOptionAt π x).status ≠ 0 ↔ π.statusAt x ≠ .X := by
  rw [rawOption_status]
  cases π.statusAt x <;> simp [statusDigit]

theorem card_four (s : Finset (Fin 4)) :
    s.card = (if (0 : Fin 4) ∈ s then 1 else 0) +
      (if (1 : Fin 4) ∈ s then 1 else 0) +
      (if (2 : Fin 4) ∈ s then 1 else 0) +
      (if (3 : Fin 4) ∈ s then 1 else 0) := by
  have he : s = Finset.univ.filter (fun d => d ∈ s) := by ext; simp
  conv_lhs => rw [he]
  simp only [Fin.card_filter_univ_succ']
  simp
  omega

theorem keptMask_two (π : PatternData) (x : Plane) (hx : x ∈ templateSites)
    (hc : (π.keptAt x).card = 2) :
    keptMask π x ∈ ([3,5,9,6,10,12] : List Nat) := by
  have hcard := card_four (keptDirs π x)
  rw [keptDirs_card π x hx, hc] at hcard
  by_cases h0 : (0 : Fin 4) ∈ keptDirs π x <;>
    by_cases h1 : (1 : Fin 4) ∈ keptDirs π x <;>
    by_cases h2 : (2 : Fin 4) ∈ keptDirs π x <;>
    by_cases h3 : (3 : Fin 4) ∈ keptDirs π x <;>
    norm_num [h0, h1, h2, h3] at hcard
  all_goals norm_num [keptMask, h0, h1, h2, h3]

theorem dirPoint_neighbour (x : Plane) (d : Fin 4) :
    dirPoint x d ∈ neighbours x := by
  exact Finset.mem_image.mpr ⟨compassAt d.val, Finset.mem_univ _, rfl⟩

theorem rawOption_direction (π : PatternData) (hπ : π.Covered) (x : Plane)
    (hx : x ∈ templateSites) (h0 : x ≠ (0,0)) (ht : x ∉ templateTips)
    (hs : π.statusAt x ≠ .X) (d : Fin 4) :
    hasDirection (rawOptionAt π x).mask d.val =
      decide (dirPoint x d ∈ π.keptAt x) := by
  cases he : π.statusAt x with
  | X => exact (hs he).elim
  | U =>
    have hk := hπ.2.2.2.2.2.2.2.1 x hx h0 ht he
    rw [hk]
    have hb : hasDirection 15 d.val = true := by
      fin_cases d <;> norm_num [hasDirection]
    simpa [rawOptionAt, he, hb] using (decide_eq_true (dirPoint_neighbour x d)).symm
  | D =>
    simpa [rawOptionAt, he, keptDirs] using keptMask_hasDirection π x d

theorem rawOption_corner (π : PatternData) (hπ : π.Covered) (x : Plane)
    (hx : x ∈ templateCorners) (hxt : x ∈ templateSites) :
    rawOptionAt π x ∈ cornerOptions := by
  rcases hπ.2.2.2.2.2.2.1 x hx with hu | hx | ⟨hd,hc⟩
  · simp [rawOptionAt, hu, statusDigit, cornerOptions]
  · simp [rawOptionAt, hx, statusDigit, cornerOptions]
  · have hm := keptMask_two π x hxt hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm | hm | hm | hm <;>
      simp [rawOptionAt, hd, statusDigit, cornerOptions, hm]

theorem axial_X (i : Fin 4) : (⟨0,0⟩ : RawOption) ∈ axialOptions i.val := by
  fin_cases i <;> norm_num [axialOptions, List.range_succ]

theorem axial_U (i : Fin 4) (hi : i.val < 3) :
    (⟨1,15⟩ : RawOption) ∈ axialOptions i.val := by
  fin_cases i <;> norm_num at hi
  all_goals norm_num [axialOptions, List.range_succ]

theorem axial_D (i : Fin 4) (m : Nat) (hm : m ∈ ([3,5,9,6,10,12] : List Nat))
    (hb : hasDirection m ((i.val+2)%4) = decide (i.val ≠ 3)) :
    (⟨2,m⟩ : RawOption) ∈ axialOptions i.val := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  fin_cases i <;> rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [hasDirection] at hb
  all_goals norm_num [axialOptions, List.range_succ]

theorem axis_mem (π : PatternData) (hπ : π.Covered) (i : Fin 4) :
    rawOptionAt π (compassAt i.val).step ∈ axialOptions i.val := by
  have hxt : (compassAt i.val).step ∈ templateSites := by
    fin_cases i <;> norm_num [compassAt, Compass.step, templateSites, square, latticeDist]
  have hpoint : dirPoint (compassAt i.val).step ⟨(i.val+2)%4, Nat.mod_lt _ (by omega)⟩ = (0,0) := by
    fin_cases i <;> norm_num [dirPoint, compassAt, Compass.step, Prod.mk_add_mk]
  have hallowed :
      (π.statusAt (compassAt i.val).step = .U ∧ i.val < 3) ∨
      π.statusAt (compassAt i.val).step = .X ∨
      (π.statusAt (compassAt i.val).step = .D ∧
        (π.keptAt (compassAt i.val).step).card = 2 ∧
        ((0,0) ∈ π.keptAt (compassAt i.val).step ↔ i.val ≠ 3)) := by
    have ha := hπ.2.2.2.2.1
    have hs := hπ.2.2.2.1
    fin_cases i
    all_goals simp only [compassAt, beq_self_eq_true, ↓reduceIte, Compass.step]
    · rcases ha .east (by simp) with hu | hx | ⟨hd,hc,hk⟩
      · exact Or.inl ⟨hu, by omega⟩
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr ⟨hd,hc,by simpa [Compass.step] using hk⟩)
    · rcases ha .north (by simp) with hu | hx | ⟨hd,hc,hk⟩
      · exact Or.inl ⟨hu, by omega⟩
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr ⟨hd,hc,by simpa [Compass.step] using hk⟩)
    · rcases ha .west (by simp) with hu | hx | ⟨hd,hc,hk⟩
      · exact Or.inl ⟨hu, by omega⟩
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr ⟨hd,hc,by simpa [Compass.step] using hk⟩)
    · rcases hs with hx | ⟨hd,hc,hk⟩
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr ⟨hd,hc,by simpa using hk⟩)
  rcases hallowed with ⟨hu,hi⟩ | hx | ⟨hd,hc,hk⟩
  · simpa [rawOptionAt, hu, statusDigit] using axial_U i hi
  · simpa [rawOptionAt, hx, statusDigit] using axial_X i
  · have hm := keptMask_two π _ hxt hc
    have hb := keptMask_hasDirection π (compassAt i.val).step
      ⟨(i.val+2)%4, Nat.mod_lt _ (by omega)⟩
    simp only [keptDirs, Finset.mem_filter, Finset.mem_univ, true_and, hpoint] at hb
    simp only [hk] at hb
    simpa [rawOptionAt, hd, statusDigit] using axial_D i _ hm hb

theorem axes_mem (π : PatternData) (hπ : π.Covered) : axesOf π ∈ axialConfigurations := by
  have he := axis_mem π hπ 0
  have hn := axis_mem π hπ 1
  have hw := axis_mem π hπ 2
  have hs := axis_mem π hπ 3
  apply List.mem_flatMap.mpr
  refine ⟨_, he, List.mem_flatMap.mpr ⟨_, hn, List.mem_flatMap.mpr ⟨_, hw, ?_⟩⟩⟩
  exact List.mem_map.mpr ⟨_, hs, by simp [axesOf, compassAt, Compass.step]⟩

#print axioms keptMask_hasDirection
#print axioms keptDirs_card
#print axioms outgoingIndex_lt
#print axioms rawOption_status
#print axioms rawOption_nonzero
#print axioms card_four
#print axioms keptMask_two
#print axioms dirPoint_neighbour
#print axioms rawOption_direction
#print axioms rawOption_corner
#print axioms axial_X
#print axioms axial_U
#print axioms axial_D
#print axioms axis_mem
#print axioms axes_mem

end AKLT.W.H1C025

