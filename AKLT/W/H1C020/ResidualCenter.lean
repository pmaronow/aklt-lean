module
public import AKLT.W.H1C020.ResidualRing
public import AKLT.W.H1C020.CenterExp

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Proof of the second residual, `Residual_centerContraction`. -/

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

variable {π : PatternData} {r : Representation}

lemma south_absent (hπ : π.Covered) : presentBond π (ptOf 6) (0,0) = false := by
  cases h : presentBond π (ptOf 6) (0,0)
  · rfl
  · exfalso
    rcases (presentBond_iff π _ _).mp h with hb | hb
    · have := AKLT.W.H1M006.covered_incident_subset π hπ _ hb (Or.inr rfl)
      simp [AKLT.W.H1M006.passageEdges, ptOf, ringSites] at this
    · have := AKLT.W.H1M006.covered_incident_subset π hπ _ hb (Or.inl rfl)
      simp [AKLT.W.H1M006.passageEdges, ptOf, ringSites] at this

lemma odd_center_absent (i : Nat) (hi : i < 8) (hodd : i % 2 = 1) :
    presentBond π (ptOf i) (0,0) = false :=
  presentBond_eq_false π _ _ (odd_ringSite_not_center_adjacent i hi (by omega))

/-- Coefficient of an active passage bond. -/
def tc (π : PatternData) (next : Bool) (j : Nat) : ℚ :=
  if presentBond π (0,0) (ptOf (2*j)) = true ∧ ¬ (next = true ∧ ptOf (2*j) = π.outgoing.step)
  then 1 else 0

lemma centerBond_eq (hπ : π.Covered) (next : Bool) (j : Nat) (hj : j < 4) :
    centerBond π r next j = 1 + MvPolynomial.C (tc π next j) * cDot (ptOf (2*j)) := by
  unfold centerBond tc cDot
  by_cases hp : presentBond π (0,0) (ptOf (2*j)) = true
  · have hv : ptOf (2*j) ∈ reducedSpinSites π r :=
      axial_mem_V π r (2*j) (by omega) (by omega) (presentBond_active hp).2
    by_cases hn : next = true ∧ ptOf (2*j) = π.outgoing.step
    · rw [if_neg (fun h => h.2.2.2 hn), if_neg (fun h => h.2 hn)]
      simp
    · rw [if_pos ⟨hp, origin_mem_V π hπ r, hv, hn⟩, if_pos ⟨hp, hn⟩]
      simp
  · rw [if_neg (fun h => hp h.1), if_neg (fun h => hp h.1)]
    simp

lemma tc_three (hπ : π.Covered) (next : Bool) : tc π next 3 = 0 := by
  have h := south_absent hπ
  rw [presentBond_comm] at h
  unfold tc
  rw [if_neg]
  simp [h]

lemma centerPart_eq (hπ : π.Covered) (next : Bool) :
    centerPart π r next = (1 + MvPolynomial.C (tc π next 0) * cDot (ptOf 0)) *
      (1 + MvPolynomial.C (tc π next 1) * cDot (ptOf 2)) *
      (1 + MvPolynomial.C (tc π next 2) * cDot (ptOf 4)) := by
  unfold centerPart
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  rw [centerBond_eq hπ next 0 (by norm_num), centerBond_eq hπ next 1 (by norm_num),
    centerBond_eq hπ next 2 (by norm_num), centerBond_eq hπ next 3 (by norm_num), tc_three hπ]
  simp

lemma tv_mem (next : Bool) (j : Nat) (hj : j < 4) :
    tc π next j ≠ 0 → ptOf (2*j) ∈ ringV π r := by
  intro h
  unfold tc at h
  split at h
  · rename_i hc
    exact mem_ringV (axial_mem_V π r (2*j) (by omega) (by omega) (presentBond_active hc.1).2)
      (ptOf_ne_origin _ (by omega))
  · exact absurd rfl h

/-- The pair insertions of the checker, after integrating the passage spin. -/
def pairTerm (value : List Nat → VectorPolynomial) (a b : Nat) : VectorPolynomial :=
  ((List.range 3).map fun k => value (centerCodes 8 a b (k+1))).sum

lemma centerIns_eq (value : List Nat → VectorPolynomial) (out : Nat) (next : Bool)
    (p0 p1 p2 p3 p4 p5 p6 p7 : PackedSite) (h1 : p1.spec.center = false)
    (h3 : p3.spec.center = false) (h5 : p5.spec.center = false) (h6 : p6.spec.center = false)
    (h7 : p7.spec.center = false) :
    centerInsertions value 8 out next (centerPairs [p0,p1,p2,p3,p4,p5,p6,p7]) =
      (if p0.spec.center = true ∧ p2.spec.center = true ∧ ¬ (next = true ∧ (0 = out ∨ 2 = out))
        then pairTerm value 0 2 else 0) +
      (if p0.spec.center = true ∧ p4.spec.center = true ∧ ¬ (next = true ∧ (0 = out ∨ 4 = out))
        then pairTerm value 0 4 else 0) +
      (if p2.spec.center = true ∧ p4.spec.center = true ∧ ¬ (next = true ∧ (2 = out ∨ 4 = out))
        then pairTerm value 2 4 else 0) := by
  cases h0 : p0.spec.center <;> cases h2 : p2.spec.center <;> cases h4 : p4.spec.center <;>
    simp [centerPairs, centerInsertions, pairTerm, h0, h1, h2, h3, h4, h5, h6, h7,
      List.range_succ, add_assoc] <;>
    by_cases hn : next = true <;> simp [hn, add_assoc] <;> (try split_ifs) <;> simp_all [add_assoc]

lemma insertion_nil : insertion [] = 1 := by
  simp [insertion, ringCoordinate]

lemma insertion_cc (a b : Nat) (k : Nat) (hk : k < 3)
    (hab : (a = 0 ∧ b = 2) ∨ (a = 0 ∧ b = 4) ∨ (a = 2 ∧ b = 4)) :
    insertion (centerCodes 8 a b (k+1)) = sv (ptOf a) ⟨k, hk⟩ * sv (ptOf b) ⟨k, hk⟩ := by
  unfold insertion
  rw [prod_range8]
  unfold centerCodes
  rw [getD_range_map _ _ _ _ (by norm_num), getD_range_map _ _ _ _ (by norm_num),
    getD_range_map _ _ _ _ (by norm_num), getD_range_map _ _ _ _ (by norm_num),
    getD_range_map _ _ _ _ (by norm_num), getD_range_map _ _ _ _ (by norm_num),
    getD_range_map _ _ _ _ (by norm_num), getD_range_map _ _ _ _ (by norm_num)]
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    interval_cases k <;> simp [ringCoordinate, sv, ptOf]

lemma pairTerm_eq (st : Plane → Status) (hst : ∀ x ∈ ringV π r, st x = π.statusAt x)
    (a b : Nat) (hab : (a = 0 ∧ b = 2) ∨ (a = 0 ∧ b = 4) ∨ (a = 2 ∧ b = 4)) :
    pairTerm (ringPolynomial π r) a b = pairSum (ringV π r) st (ringPart π r) (ptOf a) (ptOf b) := by
  unfold pairTerm pairSum
  rw [Fin.sum_univ_three]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have h : ∀ (k : Nat) (hk : k < 3), ringPolynomial π r (centerCodes 8 a b (k+1)) =
      contractSpins (ringV π r) st (ringPart π r * sv (ptOf a) ⟨k, hk⟩ * sv (ptOf b) ⟨k, hk⟩) := by
    intro k hk
    unfold ringPolynomial insertedRingIntegrand
    rw [ringIntegrand_eq]
    change contractSpins (ringV π r) π.statusAt (ringPart π r * insertion _) = _
    rw [insertion_cc a b k hk hab, ← mul_assoc]
    exact contractSpins_congr_status _ (fun x hx m => by rw [hst x hx]) _
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), add_assoc]
  rfl

lemma coeff_match (A B : Prop) [Decidable A] [Decidable B] (n : Bool) (a b out : Nat)
    (S : VectorPolynomial) :
    MvPolynomial.C ((if A ∧ ¬ (n = true ∧ a = out) then (1:ℚ) else 0) *
      (if B ∧ ¬ (n = true ∧ b = out) then 1 else 0)) * S =
      if A ∧ B ∧ ¬ (n = true ∧ (a = out ∨ b = out)) then S else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hn : n = true <;>
    by_cases ha : a = out <;> by_cases hb : b = out <;> simp [hA, hB, hn, ha, hb]

/-- Second residual: integration of the passage spin. -/
theorem centerContraction_holds : Residual_centerContraction := by
  intro π hπ r ss hcg out hout next
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, rfl⟩ := list8 ss hcg.1
  have hflag : ∀ (i : Nat) (p : PackedSite), (p, i) ∈ [p0,p1,p2,p3,p4,p5,p6,p7].zipIdx →
      p.spec.center = presentBond π (ptOf i) (0,0) := fun i p hp => hcg.2 (p, i) hp
  have e0 := hflag 0 p0 (by simp [List.zipIdx])
  have e1 := hflag 1 p1 (by simp [List.zipIdx])
  have e2 := hflag 2 p2 (by simp [List.zipIdx])
  have e3 := hflag 3 p3 (by simp [List.zipIdx])
  have e4 := hflag 4 p4 (by simp [List.zipIdx])
  have e5 := hflag 5 p5 (by simp [List.zipIdx])
  have e6 := hflag 6 p6 (by simp [List.zipIdx])
  have e7 := hflag 7 p7 (by simp [List.zipIdx])
  have hout8 : out < 8 := by
    by_contra h
    have : ringSites.getD out (0,0) = (0,0) := by
      rw [List.getD_eq_default _ _ (by simp [ringSites]; omega)]
    rw [this] at hout
    cases hd : π.outgoing <;> rw [hd] at hout <;> simp [Compass.step] at hout
  have hstep : ∀ a < 8, (ptOf a = π.outgoing.step ↔ a = out) := by
    intro a ha
    constructor
    · intro h
      exact ptOf_injOn a out ha hout8 (h.trans hout.symm)
    · rintro rfl
      exact hout
  set st : Plane → Status := fun x => if next = true ∧ x = (0,0) then .D else π.statusAt x
    with hst_def
  have hst : ∀ x ∈ ringV π r, st x = π.statusAt x := by
    intro x hx
    have hx0 := (Finset.mem_erase.mp hx).1
    simp [hst_def, hx0]
  have key := center_expand (ringV π r) (Finset.notMem_erase _ _) st (ringPart π r)
    varsIn_ringPart (ptOf 0) (ptOf 2) (ptOf 4) (tc π next 0) (tc π next 1) (tc π next 2)
    (tv_mem next 0 (by norm_num)) (tv_mem next 1 (by norm_num)) (tv_mem next 2 (by norm_num))
  rw [Finset.insert_erase (origin_mem_V π hπ r)] at key
  unfold reducedPolynomial
  rw [reducedIntegrand_split, centerPart_eq hπ next]
  change contractSpins (reducedSpinSites π r) st _ = _
  rw [key]
  have hR0 : ringPolynomial π r [] = contractSpins (ringV π r) st (ringPart π r) := by
    unfold ringPolynomial insertedRingIntegrand
    rw [ringIntegrand_eq]
    change contractSpins (ringV π r) π.statusAt (ringPart π r * insertion []) = _
    rw [insertion_nil, mul_one]
    exact contractSpins_congr_status _ (fun x hx m => by rw [hst x hx]) _
  have hm2 : m2 (st (0,0)) = 1 / centerScale next := by
    simp only [hst_def, and_true]
    cases next <;> simp [m2, centerScale, hπ.2.1]
  have hlen : [p0,p1,p2,p3,p4,p5,p6,p7].length = 8 := rfl
  rw [hR0, hm2, hlen,
    centerIns_eq _ out next p0 p1 p2 p3 p4 p5 p6 p7
      (by rw [e1]; exact odd_center_absent 1 (by norm_num) (by norm_num))
      (by rw [e3]; exact odd_center_absent 3 (by norm_num) (by norm_num))
      (by rw [e5]; exact odd_center_absent 5 (by norm_num) (by norm_num))
      (by rw [e6]; exact south_absent hπ)
      (by rw [e7]; exact odd_center_absent 7 (by norm_num) (by norm_num)),
    pairTerm_eq st hst 0 2 (Or.inl ⟨rfl, rfl⟩), pairTerm_eq st hst 0 4 (Or.inr (Or.inl ⟨rfl, rfl⟩)),
    pairTerm_eq st hst 2 4 (Or.inr (Or.inr ⟨rfl, rfl⟩))]
  have ht0 : tc π next 0 = if p0.spec.center = true ∧ ¬ (next = true ∧ 0 = out) then 1 else 0 := by
    unfold tc
    rw [presentBond_comm, ← e0]
    simp only [show 2*0 = 0 from rfl, hstep 0 (by norm_num)]
  have ht1 : tc π next 1 = if p2.spec.center = true ∧ ¬ (next = true ∧ 2 = out) then 1 else 0 := by
    unfold tc
    rw [presentBond_comm, ← e2]
    simp only [show 2*1 = 2 from rfl, hstep 2 (by norm_num)]
  have ht2 : tc π next 2 = if p4.spec.center = true ∧ ¬ (next = true ∧ 4 = out) then 1 else 0 := by
    unfold tc
    rw [presentBond_comm, ← e4]
    simp only [show 2*2 = 4 from rfl, hstep 4 (by norm_num)]
  rw [ht0, ht1, ht2, coeff_match, coeff_match, coeff_match]

end AKLT.W.H1C020
