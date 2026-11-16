import AKLT.W.H1C020.BondId
import AKLT.W.H1C020.Reduction

/-!
Proof of `Residual_ringFubini`.  The uncontracted transfer is the ring part of
the reduced integrand times the inserted ring coordinates; contracting the
eight ring sites one at a time gives the checker's normalized transfer.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

variable {π : PatternData} {r : Representation}

/-- The inserted ring coordinates. -/
def insertion (codes : List Nat) : LPoly :=
  ((List.range 8).map fun i => ringCoordinate i (codes.getD i 0)).prod

/-- The ring spin sites actually retained. -/
abbrev ringV (π : PatternData) (r : Representation) : Finset Plane :=
  (reducedSpinSites π r).erase (0,0)

lemma varsIn_finsetProd {ι : Type*} {A : Finset Plane} (s : Finset ι) (f : ι → LPoly)
    (h : ∀ i ∈ s, VarsIn A (f i)) : VarsIn A (∏ i ∈ s, f i) := by
  classical
  intro w hw
  obtain ⟨i, hi, hw'⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_prod f hw)
  exact h i hi w hw'

lemma varsIn_finsetSum {ι : Type*} {A : Finset Plane} (s : Finset ι) (f : ι → LPoly)
    (h : ∀ i ∈ s, VarsIn A (f i)) : VarsIn A (∑ i ∈ s, f i) := by
  classical
  intro w hw
  obtain ⟨i, hi, hw'⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset s f hw)
  exact h i hi w hw'

lemma varsIn_formalDot_inl_inl {A : Finset Plane} {x y : Plane} (hx : x ∈ A) (hy : y ∈ A) :
    VarsIn A (formalDot (fun k => (.inl (x,k) : LocalVariable)) (fun k => .inl (y,k))) :=
  varsIn_finsetSum _ _ (fun k _ => (varsIn_X_inl hx k).mul (varsIn_X_inl hy k))

lemma varsIn_formalDot_inl_inr {A : Finset Plane} {x : Plane} (hx : x ∈ A) (j : Fin 20) :
    VarsIn A (formalDot (fun k => (.inl (x,k) : LocalVariable)) (fun k => .inr (j,k))) :=
  varsIn_finsetSum _ _ (fun k _ => (varsIn_X_inl hx k).mul (varsIn_X_inr A _))

lemma mem_ringV {x : Plane} (hx : x ∈ reducedSpinSites π r) (h0 : x ≠ (0,0)) : x ∈ ringV π r :=
  Finset.mem_erase.mpr ⟨h0, hx⟩

lemma varsIn_ringBond (i : Nat) (hi : i < 8) : VarsIn (ringV π r) (ringBond π r i) := by
  unfold ringBond
  split
  · rename_i h
    exact (varsIn_one _).add (varsIn_formalDot_inl_inl (mem_ringV h.2.1 (ptOf_ne_origin i hi))
      (mem_ringV h.2.2 (ptOf_ne_origin _ (Nat.mod_lt _ (by decide)))))
  · exact varsIn_one _

lemma leafNeighbour_ring (i : Nat) (hi : i < 8) (hg : groupPoint i ∈ reductionGroups π)
    (hp : groupIsPair π r (groupPoint i) = false) :
    ∃ j < 8, leafNeighbour π (groupPoint i) = ptOf j := by
  by_cases he : i % 2 = 0
  · exact ⟨i, hi, tip_leafNeighbour π i hi he hg⟩
  · have hodd : i % 2 = 1 := by omega
    have hs := (AKLT.W.H1M023.group_single π r hg hp).1
    rw [groupPoint_odd i hodd] at hs ⊢
    rcases leaf_corner π r i hi hodd hs with ⟨_, _, h⟩ | ⟨_, _, h⟩
    · exact ⟨i-1, by omega, h⟩
    · exact ⟨(i+1)%8, Nat.mod_lt _ (by decide), h⟩

lemma varsIn_groupAt (i : Nat) (hi : i < 8) : VarsIn (ringV π r) (groupAt π r i) := by
  unfold groupAt
  split
  · rename_i hg
    unfold groupFactor
    cases hp : groupIsPair π r (groupPoint i)
    · rw [if_neg (by decide)]
      obtain ⟨j, hj, hnb⟩ := leafNeighbour_ring i hi hg hp
      have hmem := AKLT.W.H1M023.group_single_neighbour_retained π r hg hp
      rw [hnb] at hmem ⊢
      exact (varsIn_one _).add ((varsIn_C _ _).mul
        (varsIn_formalDot_inl_inr (mem_ringV hmem (ptOf_ne_origin j hj)) _))
    · rw [if_pos rfl]
      have hmem := AKLT.W.H1M023.group_pair_retained π r hg hp
      have hx := mem_ringV hmem (groupPoint_ne_origin i hi)
      exact ((varsIn_one _).add (varsIn_formalDot_inl_inr hx _)).mul
        ((varsIn_one _).add (varsIn_formalDot_inl_inr hx _))
  · exact varsIn_one _

lemma varsIn_ringPart : VarsIn (ringV π r) (ringPart π r) := by
  unfold ringPart
  exact (varsIn_finsetProd _ _ (fun i hi => varsIn_ringBond i (Finset.mem_range.mp hi))).mul
    (varsIn_finsetProd _ _ (fun i hi => varsIn_groupAt i (Finset.mem_range.mp hi)))

/-- Facts about admissible insertion codes. -/
def CodesOK (π : PatternData) (codes : List Nat) : Prop :=
  ∀ i < 8, codes.getD i 0 ≤ 3 ∧ (codes.getD i 0 ≠ 0 → presentBond π (ptOf i) (0,0) = true)

lemma varsIn_insertion (codes : List Nat) (hc : CodesOK π codes) :
    VarsIn (ringV π r) (insertion codes) := by
  unfold insertion
  apply varsIn_listProd
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  have hi8 := List.mem_range.mp hi
  unfold ringCoordinate
  split
  · exact varsIn_one _
  · rename_i hne
    have hne' : codes.getD i 0 ≠ 0 := by simpa using hne
    have hb := (hc i hi8).2 hne'
    have hact := (presentBond_active hb).1
    have heven : i % 2 = 0 := by
      by_contra hodd
      have hno := presentBond_eq_false π (ringSites.getD i (0,0)) (0,0)
        (odd_ringSite_not_center_adjacent i hi8 hodd)
      exact absurd (hno ▸ hb : false = true) (by decide)
    exact varsIn_X_inl (mem_ringV (axial_mem_V π r i hi8 heven hact) (ptOf_ne_origin i hi8)) _

/-! ### Erasing the passage coordinates -/

lemma eraseCenterHom_origin (k : Fin 3) :
    eraseCenterHom (MvPolynomial.X (.inl ((0,0),k))) = 0 := by
  simp [eraseCenterHom]

lemma eraseCenterHom_fix (p : LPoly) (hp : VarsIn (ringV π r) p) : eraseCenterHom p = p := by
  have h := MvPolynomial.hom_congr_vars (f₁ := eraseCenterHom) (f₂ := RingHom.id _)
    (p₁ := p) (p₂ := p) (by ext a; simp [eraseCenterHom]) ?_ rfl
  · simpa using h
  · intro w hw _
    have hw' := hp w hw
    cases w with
    | inl w =>
        obtain ⟨x, k⟩ := w
        have hx : x ≠ (0,0) := (Finset.mem_erase.mp hw').1
        simp [eraseCenterHom, hx]
    | inr w => simp [eraseCenterHom]

lemma eraseCenterHom_centerPart (next : Bool) : eraseCenterHom (centerPart π r next) = 1 := by
  unfold centerPart
  rw [map_prod]
  apply Finset.prod_eq_one
  intro j _
  unfold centerBond
  split
  · rw [map_add, map_one]
    unfold formalDot
    rw [map_sum]
    simp [eraseCenterHom_origin]
  · exact map_one _

theorem ringIntegrand_eq : ringIntegrand π r = ringPart π r := by
  unfold ringIntegrand
  rw [reducedIntegrand_split, map_mul, eraseCenterHom_centerPart, mul_one,
    eraseCenterHom_fix _ varsIn_ringPart]

/-! ### The factorized transfer -/

lemma headD_eq_getD (l : List Nat) : l.headD 0 = l.getD 0 0 := by
  cases l <;> rfl

lemma tail_getD (l : List Nat) (i : Nat) : l.tail.getD i 0 = l.getD (i+1) 0 := by
  cases l <;> simp

lemma prod_range8 (f : Nat → LPoly) :
    ((List.range 8).map f).prod = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  ring

lemma finsetProd_range8 (f : Nat → LPoly) :
    ∏ i ∈ Finset.range 8, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]

def slotFactor (π : PatternData) (r : Representation) (i : Nat) : LPoly :=
  if i % 2 = 1 ∧ SingleReplacement π r (ptOf i) then 1 else groupAt π r i

lemma slotFactor_even (i : Nat) (he : i % 2 = 0) : slotFactor π r i = groupAt π r i := by
  unfold slotFactor
  rw [if_neg (fun h => by omega)]

lemma bond_identity' (i : Nat) (hi : i < 7) (s t : SiteSpec) (hs : SiteFlags π r i s)
    (ht : SiteFlags π r (i+1) t) :
    bondL Lf Rf i s t = ringBond π r i * leafBond π r i := by
  have h := bond_identity i (by omega) s t hs (by rwa [Nat.mod_eq_of_lt (by omega : i+1 < 8)])
  rwa [Nat.mod_eq_of_lt (by omega : i+1 < 8)] at h

lemma corner_identity' (a c : Nat) (hac : a + 1 = c) (hc : c < 8) (hodd : c % 2 = 1) :
    leafBond π r a * leafBond π r c * slotFactor π r c = groupAt π r c := by
  have h := corner_identity (π := π) (r := r) c hc hodd
  rw [show c - 1 = a by omega] at h
  exact h

lemma Mf_eq {i : Nat} {s : SiteSpec} (h : SiteFlags π r i s) (hi : i < 8) (v : Nat)
    (hv3 : v ≤ 3) (hvc : v ≠ 0 → s.center = true) :
    Mf i s v = ringCoordinate i v * slotFactor π r i := by
  unfold Mf
  rw [Cf_eq_ringCoordinate h hi v hv3 hvc, Gf_eq h hi]
  rfl

lemma list8 {α : Type*} (l : List α) (h : l.length = 8) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7, l = [a0, a1, a2, a3, a4, a5, a6, a7] := by
  match l, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7], _ => exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩

/-- The uncontracted transfer is the ring part times the inserted coordinates. -/
theorem closedL_eq {I : Finset (Fin 20)} {ss : List PackedSite} (hg : NetworkGeometry π r I ss)
    (codes : List Nat) (hc : CodesOK π codes) :
    closedL gLoc (eraseNetworkInversion ss) codes = ringPart π r * insertion codes := by
  have hfl : ∀ i (hi : i < ss.length), SiteFlags π r i (eraseInversion (ss[i]).spec) :=
    siteFlags_of_geometry hg
  have hcen : ∀ i (hi : i < ss.length), codes.getD i 0 ≤ 3 ∧
      (codes.getD i 0 ≠ 0 → (eraseInversion (ss[i]).spec).center = true) := by
    intro i hi
    have h8 : i < 8 := hg.1 ▸ hi
    refine ⟨(hc i h8).1, fun hne => ?_⟩
    rw [(hfl i hi).center]
    exact (hc i h8).2 hne
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, rfl⟩ := list8 ss hg.1
  have f0 : SiteFlags π r 0 (eraseInversion p0.spec) := hfl 0 (by simp)
  have f1 : SiteFlags π r 1 (eraseInversion p1.spec) := hfl 1 (by simp)
  have f2 : SiteFlags π r 2 (eraseInversion p2.spec) := hfl 2 (by simp)
  have f3 : SiteFlags π r 3 (eraseInversion p3.spec) := hfl 3 (by simp)
  have f4 : SiteFlags π r 4 (eraseInversion p4.spec) := hfl 4 (by simp)
  have f5 : SiteFlags π r 5 (eraseInversion p5.spec) := hfl 5 (by simp)
  have f6 : SiteFlags π r 6 (eraseInversion p6.spec) := hfl 6 (by simp)
  have f7 : SiteFlags π r 7 (eraseInversion p7.spec) := hfl 7 (by simp)
  have c0 : codes.getD 0 0 ≤ 3 ∧ (codes.getD 0 0 ≠ 0 → (eraseInversion p0.spec).center = true) :=
    hcen 0 (by simp)
  have c1 : codes.getD 1 0 ≤ 3 ∧ (codes.getD 1 0 ≠ 0 → (eraseInversion p1.spec).center = true) :=
    hcen 1 (by simp)
  have c2 : codes.getD 2 0 ≤ 3 ∧ (codes.getD 2 0 ≠ 0 → (eraseInversion p2.spec).center = true) :=
    hcen 2 (by simp)
  have c3 : codes.getD 3 0 ≤ 3 ∧ (codes.getD 3 0 ≠ 0 → (eraseInversion p3.spec).center = true) :=
    hcen 3 (by simp)
  have c4 : codes.getD 4 0 ≤ 3 ∧ (codes.getD 4 0 ≠ 0 → (eraseInversion p4.spec).center = true) :=
    hcen 4 (by simp)
  have c5 : codes.getD 5 0 ≤ 3 ∧ (codes.getD 5 0 ≠ 0 → (eraseInversion p5.spec).center = true) :=
    hcen 5 (by simp)
  have c6 : codes.getD 6 0 ≤ 3 ∧ (codes.getD 6 0 ≠ 0 → (eraseInversion p6.spec).center = true) :=
    hcen 6 (by simp)
  have c7 : codes.getD 7 0 ≤ 3 ∧ (codes.getD 7 0 ≠ 0 → (eraseInversion p7.spec).center = true) :=
    hcen 7 (by simp)
  simp only [eraseNetworkInversion, List.map_cons, List.map_nil]
  rw [closedL_factor Lf Rf Mf gLoc (fun _ _ _ _ _ => rfl)]
  simp only [bodyL, lastL, headD_eq_getD, tail_getD, Nat.reduceAdd, zero_add, List.tail_cons]
  rw [Mf_eq f0 (by norm_num) _ c0.1 c0.2, Mf_eq f1 (by norm_num) _ c1.1 c1.2,
    Mf_eq f2 (by norm_num) _ c2.1 c2.2, Mf_eq f3 (by norm_num) _ c3.1 c3.2,
    Mf_eq f4 (by norm_num) _ c4.1 c4.2, Mf_eq f5 (by norm_num) _ c5.1 c5.2,
    Mf_eq f6 (by norm_num) _ c6.1 c6.2, Mf_eq f7 (by norm_num) _ c7.1 c7.2,
    bond_identity' 0 (by norm_num) _ _ f0 f1, bond_identity' 1 (by norm_num) _ _ f1 f2,
    bond_identity' 2 (by norm_num) _ _ f2 f3, bond_identity' 3 (by norm_num) _ _ f3 f4,
    bond_identity' 4 (by norm_num) _ _ f4 f5, bond_identity' 5 (by norm_num) _ _ f5 f6,
    bond_identity' 6 (by norm_num) _ _ f6 f7]
  have hw := bond_identity 7 (by norm_num) _ _ f7 (by simpa using f0)
  simp only [Nat.reduceAdd, Nat.reduceMod] at hw
  rw [hw]
  have e1 := corner_identity' (π := π) (r := r) 0 1 rfl (by norm_num) (by norm_num)
  have e3 := corner_identity' (π := π) (r := r) 2 3 rfl (by norm_num) (by norm_num)
  have e5 := corner_identity' (π := π) (r := r) 4 5 rfl (by norm_num) (by norm_num)
  have e7 := corner_identity' (π := π) (r := r) 6 7 rfl (by norm_num) (by norm_num)
  rw [slotFactor_even 0 rfl, slotFactor_even 2 rfl, slotFactor_even 4 rfl, slotFactor_even 6 rfl]
  unfold ringPart insertion
  rw [finsetProd_range8, finsetProd_range8, prod_range8]
  calc _ = (ringCoordinate 0 (codes.getD 0 0) * ringCoordinate 1 (codes.getD 1 0) *
          ringCoordinate 2 (codes.getD 2 0) * ringCoordinate 3 (codes.getD 3 0) *
          ringCoordinate 4 (codes.getD 4 0) * ringCoordinate 5 (codes.getD 5 0) *
          ringCoordinate 6 (codes.getD 6 0) * ringCoordinate 7 (codes.getD 7 0)) *
        (ringBond π r 0 * ringBond π r 1 * ringBond π r 2 * ringBond π r 3 *
          ringBond π r 4 * ringBond π r 5 * ringBond π r 6 * ringBond π r 7) *
        (groupAt π r 0 * groupAt π r 2 * groupAt π r 4 * groupAt π r 6) *
        (leafBond π r 0 * leafBond π r 1 * slotFactor π r 1) *
        (leafBond π r 2 * leafBond π r 3 * slotFactor π r 3) *
        (leafBond π r 4 * leafBond π r 5 * slotFactor π r 5) *
        (leafBond π r 6 * leafBond π r 7 * slotFactor π r 7) := by ring
    _ = _ := by rw [e1, e3, e5, e7]; ring

end AKLT.W.H1C020
