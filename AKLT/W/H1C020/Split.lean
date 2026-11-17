module
public import AKLT.W.H1C020.RingGeom

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-!
Exact factorization of the reduced integrand into the eight ring bonds, the
eight group factors and the (at most four) passage bonds.  Bonds are indexed
by the sixteen fixed template edges; group factors by the eight ring
positions.
-/

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

/-- The `j`-th fixed template edge. -/
def tE (j : Nat) : Plane × Plane := templateEdges.getD j ((0,0),(0,0))

lemma templateEdges_length : templateEdges.length = 16 := rfl

lemma templateEdges_mid_nodup :
    (templateEdges.map (fun e : Plane × Plane => e.1 + e.2)).Nodup := by
  simp only [templateEdges, List.map_cons, List.map_nil, Prod.mk_add_mk]
  norm_num

lemma tE_mid_inj (j j' : Nat) (hj : j < 16) (hj' : j' < 16)
    (h : (tE j).1 + (tE j).2 = (tE j').1 + (tE j').2) : j = j' := by
  have hnd := templateEdges_mid_nodup
  have hl : j < (templateEdges.map (fun e : Plane × Plane => e.1 + e.2)).length := by
    simpa [templateEdges_length] using hj
  have hl' : j' < (templateEdges.map (fun e : Plane × Plane => e.1 + e.2)).length := by
    simpa [templateEdges_length] using hj'
  have hj2 : j < templateEdges.length := by simpa [templateEdges_length] using hj
  have hj2' : j' < templateEdges.length := by simpa [templateEdges_length] using hj'
  unfold tE at h
  rw [List.getD_eq_getElem _ _ hj2, List.getD_eq_getElem _ _ hj2'] at h
  have := (hnd.getElem_inj_iff (i := j) (j := j') (hi := hl) (hj := hl')).mp
    (by simpa only [List.getElem_map] using h)
  exact this

lemma mem_templateEdges_index {e : Plane × Plane} (h : e ∈ templateEdges) :
    ∃ j < 16, tE j = e := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp h
  refine ⟨j, by simpa [templateEdges_length] using hj, ?_⟩
  unfold tE
  rw [List.getD_eq_getElem _ _ hj]

/-- A symmetric bond function multiplied over the actual bonds is the same
product over the sixteen fixed template edges, each present or not. -/
lemma bonds_prod {M : Type*} [CommMonoid M] (π : PatternData) (F : Plane × Plane → M)
    (hF : ∀ a b, F (a,b) = F (b,a)) :
    ∏ e ∈ π.bonds, F e = ∏ j ∈ Finset.range 16,
      (if presentBond π (tE j).1 (tE j).2 = true then F (tE j) else 1) := by
  classical
  symm
  apply Finset.prod_bij_ne_one
    (fun j _ _ => if tE j ∈ π.bonds then tE j else ((tE j).2, (tE j).1))
  · intro j _ hne
    have hp : presentBond π (tE j).1 (tE j).2 = true := by
      by_contra h
      exact hne (by simp [h])
    rcases (presentBond_iff π _ _).mp hp with h | h
    · simp only [Prod.mk.eta] at h
      simp [h]
    · by_cases h' : tE j ∈ π.bonds
      · simp [h']
      · simp [h', h]
  · intro j hj _ j' hj' _ heq
    apply tE_mid_inj j j' (Finset.mem_range.mp hj) (Finset.mem_range.mp hj')
    have key : ∀ i, (if tE i ∈ π.bonds then tE i else ((tE i).2, (tE i).1)).1 +
        (if tE i ∈ π.bonds then tE i else ((tE i).2, (tE i).1)).2 = (tE i).1 + (tE i).2 := by
      intro i
      split_ifs
      · rfl
      · exact add_comm _ _
    have := congrArg (fun e : Plane × Plane => e.1 + e.2) heq
    rw [key j, key j'] at this
    exact this
  · intro e he hne
    have hi := (Finset.mem_filter.mp he).1
    have hi' : (e.1, e.2) ∈ internalBonds templateSites := hi
    rcases AKLT.W.H1C031.internalBond_templateEdge hi' with hm | hm
    · obtain ⟨j, hj, hje⟩ := mem_templateEdges_index hm
      have hje' : tE j = e := hje
      refine ⟨j, Finset.mem_range.mpr hj, ?_, ?_⟩
      · have hp : presentBond π (tE j).1 (tE j).2 = true :=
          (presentBond_iff π _ _).mpr (Or.inl (by rw [hje']; exact he))
        rw [if_pos hp, hje']
        exact hne
      · simp [hje', he]
    · obtain ⟨j, hj, hje⟩ := mem_templateEdges_index hm
      have hnot : tE j ∉ π.bonds := by
        rw [hje]
        intro hb
        exact AKLT.W.H1C031.internalBonds_no_reverse hi' (Finset.mem_filter.mp hb).1
      refine ⟨j, Finset.mem_range.mpr hj, ?_, ?_⟩
      · have hp : presentBond π (tE j).1 (tE j).2 = true :=
          (presentBond_iff π _ _).mpr (Or.inr (by rw [hje]; exact he))
        rw [if_pos hp, hje, hF]
        exact hne
      · rw [if_neg hnot, hje]
  · intro j _ hne
    have hp : presentBond π (tE j).1 (tE j).2 = true := by
      by_contra h
      exact hne (by simp [h])
    rw [if_pos hp]
    split_ifs
    · rfl
    · exact hF _ _

lemma prod_range16 {M : Type*} [CommMonoid M] (G : Nat → M) :
    ∏ j ∈ Finset.range 16, G j = (∏ j ∈ Finset.range 4, G j) *
      (∏ i ∈ Finset.range 8, G (4+i)) * (∏ j ∈ Finset.range 4, G (12+j)) := by
  rw [show 16 = 12 + 4 from rfl, Finset.prod_range_add, show 12 = 4 + 8 from rfl,
    Finset.prod_range_add]

lemma tE_center (j : Nat) (hj : j < 4) : tE j = ((0,0), ptOf (2*j)) := by
  interval_cases j <;> rfl

lemma tE_ring (i : Nat) (hi : i < 8) : tE (4+i) = (ptOf i, ptOf ((i+1)%8)) := by
  interval_cases i <;> rfl

lemma tE_tip (j : Nat) (hj : j < 4) : tE (12+j) = (ptOf (2*j), groupPoint (2*j)) := by
  interval_cases j <;> rfl

/-! ### The factors -/

/-- A bond factor of the reduced integrand. -/
def bondFactorL (π : PatternData) (r : Representation) (next : Bool) (e : Plane × Plane) : LPoly :=
  if e.1 ∈ reducedSpinSites π r ∧ e.2 ∈ reducedSpinSites π r ∧
      ¬ (next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step}) then
    1 + formalDot (fun k => .inl (e.1, k)) (fun k => .inl (e.2, k)) else 1

/-- A group factor of the reduced integrand. -/
def groupFactor (π : PatternData) (r : Representation) (x : Plane) : LPoly :=
  if groupIsPair π r x then
    (1 + formalDot (fun k => .inl (x, k)) (fun k => .inr (groupLeader x, k))) *
    (1 + formalDot (fun k => .inl (x, k)) (fun k => .inr (groupSecond x, k)))
  else 1 + MvPolynomial.C (replacementRadius π x) *
    formalDot (fun k => .inl (leafNeighbour π x, k)) (fun k => .inr (groupLeader x, k))

lemma reducedIntegrand_eq (π : PatternData) (r : Representation) (next : Bool) :
    reducedIntegrand π r next = (∏ e ∈ π.bonds, bondFactorL π r next e) *
      ∏ x ∈ reductionGroups π, groupFactor π r x := rfl

/-- Ring bond between positions `i` and `i+1`. -/
def ringBond (π : PatternData) (r : Representation) (i : Nat) : LPoly :=
  if presentBond π (ptOf i) (ptOf ((i+1)%8)) = true ∧ ptOf i ∈ reducedSpinSites π r ∧
      ptOf ((i+1)%8) ∈ reducedSpinSites π r then
    1 + formalDot (fun k => .inl (ptOf i, k)) (fun k => .inl (ptOf ((i+1)%8), k)) else 1

/-- Group factor carried by ring position `i`. -/
def groupAt (π : PatternData) (r : Representation) (i : Nat) : LPoly :=
  if groupPoint i ∈ reductionGroups π then groupFactor π r (groupPoint i) else 1

/-- Passage bond to the axial ring position `2j`. -/
def centerBond (π : PatternData) (r : Representation) (next : Bool) (j : Nat) : LPoly :=
  if presentBond π (0,0) (ptOf (2*j)) = true ∧ ((0,0) : Plane) ∈ reducedSpinSites π r ∧
      ptOf (2*j) ∈ reducedSpinSites π r ∧ ¬ (next = true ∧ ptOf (2*j) = π.outgoing.step) then
    1 + formalDot (fun k => .inl ((0,0), k)) (fun k => .inl (ptOf (2*j), k)) else 1

def ringPart (π : PatternData) (r : Representation) : LPoly :=
  (∏ i ∈ Finset.range 8, ringBond π r i) * ∏ i ∈ Finset.range 8, groupAt π r i

def centerPart (π : PatternData) (r : Representation) (next : Bool) : LPoly :=
  ∏ j ∈ Finset.range 4, centerBond π r next j

lemma formalDot_comm {σ : Type*} (a b : Fin 3 → σ) : formalDot a b = formalDot b a := by
  unfold formalDot
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma bondFactorL_symm (π : PatternData) (r : Representation) (next : Bool) (a b : Plane) :
    bondFactorL π r next (a,b) = bondFactorL π r next (b,a) := by
  unfold bondFactorL
  simp only [Finset.pair_comm a b]
  by_cases h : a ∈ reducedSpinSites π r ∧ b ∈ reducedSpinSites π r ∧
      ¬ (next = true ∧ ({b, a} : Finset Plane) = {(0, 0), π.outgoing.step})
  · rw [if_pos h, if_pos ⟨h.2.1, h.1, h.2.2⟩, formalDot_comm]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.1, h'.1, h'.2.2⟩)]

lemma origin_pair_eq' (x o : Plane) (hx : x ≠ (0, 0)) :
    ({(0, 0), x} : Finset Plane) = {(0, 0), o} ↔ x = o := by
  constructor
  · intro h
    have : x ∈ ({(0, 0), o} : Finset Plane) := by rw [← h]; simp
    simpa [hx] using this
  · rintro rfl
    rfl

lemma pair_eq_origin_pair {a b o : Plane}
    (h : ({a, b} : Finset Plane) = {(0, 0), o}) : a = (0,0) ∨ b = (0,0) := by
  have : ((0,0) : Plane) ∈ ({a, b} : Finset Plane) := by rw [h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

lemma ring_factor (π : PatternData) (r : Representation) (next : Bool) (i : Nat) (hi : i < 8) :
    (if presentBond π (tE (4+i)).1 (tE (4+i)).2 = true then bondFactorL π r next (tE (4+i))
      else 1) = ringBond π r i := by
  rw [tE_ring i hi]
  unfold bondFactorL ringBond
  simp only
  have hn : ¬ (next = true ∧ ({ptOf i, ptOf ((i+1)%8)} : Finset Plane) =
      {(0, 0), π.outgoing.step}) := by
    rintro ⟨_, h⟩
    rcases pair_eq_origin_pair h with h | h
    · exact ptOf_ne_origin i hi h
    · exact ptOf_ne_origin _ (Nat.mod_lt _ (by decide)) h
  by_cases hp : presentBond π (ptOf i) (ptOf ((i+1)%8)) = true
  · by_cases hv : ptOf i ∈ reducedSpinSites π r ∧ ptOf ((i+1)%8) ∈ reducedSpinSites π r
    · rw [if_pos hp, if_pos ⟨hv.1, hv.2, hn⟩, if_pos ⟨hp, hv⟩]
    · rw [if_pos hp, if_neg (fun h => hv ⟨h.1, h.2.1⟩), if_neg (fun h => hv h.2)]
  · rw [if_neg hp, if_neg (fun h => hp h.1)]

lemma center_factor (π : PatternData) (r : Representation) (next : Bool) (j : Nat) (hj : j < 4) :
    (if presentBond π (tE j).1 (tE j).2 = true then bondFactorL π r next (tE j) else 1) =
      centerBond π r next j := by
  rw [tE_center j hj]
  unfold bondFactorL centerBond
  simp only
  have hne : ptOf (2*j) ≠ (0,0) := ptOf_ne_origin _ (by omega)
  have hiff : ({(0,0), ptOf (2*j)} : Finset Plane) = {(0, 0), π.outgoing.step} ↔
      ptOf (2*j) = π.outgoing.step := origin_pair_eq' _ _ hne
  simp only [hiff]
  by_cases hp : presentBond π (0,0) (ptOf (2*j)) = true
  · simp only [hp, true_and, ↓reduceIte]
  · simp only [hp, Bool.false_eq_true, false_and, ↓reduceIte]

lemma tip_factor (π : PatternData) (r : Representation) (next : Bool) (j : Nat) (hj : j < 4) :
    (if presentBond π (tE (12+j)).1 (tE (12+j)).2 = true then bondFactorL π r next (tE (12+j))
      else 1) = 1 := by
  rw [tE_tip j hj]
  have ht : groupPoint (2*j) ∉ reducedSpinSites π r :=
    tip_not_mem_V π r (even_groupPoint_tip _ (by omega) (by omega))
  unfold bondFactorL
  simp [ht]

lemma groups_image : templateCorners ∪ templateTips = (Finset.range 8).image groupPoint := by
  ext x
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · intro h
    simp only [templateCorners, templateTips, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
    · exact ⟨1, by norm_num, by simp [groupPoint, ringSites]⟩
    · exact ⟨3, by norm_num, by simp [groupPoint, ringSites]⟩
    · exact ⟨5, by norm_num, by simp [groupPoint, ringSites]⟩
    · exact ⟨7, by norm_num, by simp [groupPoint, ringSites]⟩
    · exact ⟨0, by norm_num, by simp [groupPoint, ringSites]⟩
    · exact ⟨2, by norm_num, by simp [groupPoint, ringSites]⟩
    · exact ⟨4, by norm_num, by simp [groupPoint, ringSites]⟩
    · exact ⟨6, by norm_num, by simp [groupPoint, ringSites]⟩
  · rintro ⟨i, hi, rfl⟩
    interval_cases i <;> simp [groupPoint, ringSites, templateCorners, templateTips]

lemma groupPoint_injOn : Set.InjOn groupPoint (Finset.range 8 : Set Nat) := by
  intro a ha b hb h
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  interval_cases a <;> interval_cases b <;> simp_all [groupPoint, ringSites]

lemma groups_prod (π : PatternData) (r : Representation) :
    ∏ x ∈ reductionGroups π, groupFactor π r x = ∏ i ∈ Finset.range 8, groupAt π r i := by
  classical
  have hfilter : reductionGroups π =
      (templateCorners ∪ templateTips).filter fun x => 0 < patternDegree π x := rfl
  rw [hfilter, Finset.prod_filter, groups_image, Finset.prod_image groupPoint_injOn]
  apply Finset.prod_congr rfl
  intro i hi
  unfold groupAt
  have hmem : groupPoint i ∈ templateCorners ∪ templateTips := by
    rw [groups_image]
    exact Finset.mem_image_of_mem _ hi
  have hiff : groupPoint i ∈ reductionGroups π ↔ 0 < patternDegree π (groupPoint i) := by
    rw [hfilter, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hmem, h⟩⟩
  by_cases h : 0 < patternDegree π (groupPoint i)
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]

/-- The reduced integrand is the ring part times the passage part. -/
theorem reducedIntegrand_split (π : PatternData) (r : Representation) (next : Bool) :
    reducedIntegrand π r next = ringPart π r * centerPart π r next := by
  rw [reducedIntegrand_eq, bonds_prod π _ (bondFactorL_symm π r next), prod_range16,
    groups_prod]
  have hc : (∏ j ∈ Finset.range 4, (if presentBond π (tE j).1 (tE j).2 = true then
      bondFactorL π r next (tE j) else 1)) = centerPart π r next :=
    Finset.prod_congr rfl (fun j hj => center_factor π r next j (Finset.mem_range.mp hj))
  have hr : (∏ i ∈ Finset.range 8, (if presentBond π (tE (4+i)).1 (tE (4+i)).2 = true then
      bondFactorL π r next (tE (4+i)) else 1)) = ∏ i ∈ Finset.range 8, ringBond π r i :=
    Finset.prod_congr rfl (fun i hi => ring_factor π r next i (Finset.mem_range.mp hi))
  have ht : (∏ j ∈ Finset.range 4, (if presentBond π (tE (12+j)).1 (tE (12+j)).2 = true then
      bondFactorL π r next (tE (12+j)) else 1)) = 1 :=
    Finset.prod_eq_one (fun j hj => tip_factor π r next j (Finset.mem_range.mp hj))
  rw [hc, hr, ht]
  unfold ringPart
  ring

end AKLT.W.H1C020
