module
public import AKLT.W.H1C020.Normalization

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

lemma bond_adjacent (π : PatternData) {e : Plane × Plane}
    (he : e ∈ π.bonds) : Adjacent e.1 e.2 := by
  classical
  have hb : e ∈ internalBonds templateSites := (Finset.mem_filter.mp he).1
  obtain ⟨p, hp, hImage⟩ := Finset.mem_biUnion.mp hb
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hImage
  have hqPos := (Finset.mem_inter.mp hq).1
  have hqCases : q = (p.1+1,p.2) ∨ q = (p.1,p.2+1) := by
    simpa only [positiveNeighbors, Finset.mem_insert, Finset.mem_singleton] using hqPos
  rcases hqCases with rfl | rfl <;> norm_num [Adjacent, latticeDist]

lemma adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  have hx : y.1-x.1 = -(x.1-y.1) := by ring
  have hy : y.2-x.2 = -(x.2-y.2) := by ring
  simpa only [Adjacent, latticeDist, hx, hy, Int.natAbs_neg] using h

lemma presentBond_eq_false (π : PatternData) (x y : Plane) (h : ¬ Adjacent x y) :
    presentBond π x y = false := by
  simp only [presentBond, decide_eq_false_iff_not, not_or]
  exact ⟨fun hb => h (bond_adjacent π hb), fun hb => h (adjacent_symm (bond_adjacent π hb))⟩

lemma groupSlots_le_two (π : PatternData) (r : Representation) (x : Plane) :
    groupSlots π r x ≤ 2 := by
  classical
  unfold groupSlots
  split_ifs <;> omega

lemma tip_not_corner {x : Plane} (hx : x ∈ templateTips) : x ∉ templateCorners := by
  simp only [templateTips, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> norm_num [templateCorners]

lemma groupSlots_tip_le_one (π : PatternData) (r : Representation) {x : Plane}
    (hx : x ∈ templateTips) : groupSlots π r x ≤ 1 := by
  classical
  have hc := tip_not_corner hx
  have hp : groupIsPair π r x = false := by simp [groupIsPair, hc]
  simp only [groupSlots, hp, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> omega

lemma even_groupPoint_tip (i : Nat) (hi : i < 8) (heven : i%2 = 0) :
    groupPoint i ∈ templateTips := by
  interval_cases i <;> norm_num [groupPoint, ringSites, templateTips] at *

lemma odd_ringSite_not_center_adjacent (i : Nat) (hi : i < 8) (hodd : i%2 ≠ 0) :
    ¬ Adjacent (ringSites.getD i (0,0)) (0,0) := by
  interval_cases i <;> norm_num [ringSites, Adjacent, latticeDist] at *

lemma bool_toNat_le_one (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

/-- The geometry's eight local tensors all have degree at most four, and a
replaced corner cannot simultaneously be a covering tip. -/
lemma network_localValidity (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (ss : List PackedSite) (hg : NetworkGeometry π r I ss) :
    ∀ s ∈ ss, LocalValidity s.spec := by
  classical
  intro s hs
  obtain ⟨i, hi, hsi⟩ := List.getElem_of_mem hs
  subst s
  have hizip : (ss[i],i) ∈ ss.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    exact List.getElem?_eq_getElem hi
  have hgsite := hg.2 (ss[i],i) hizip
  dsimp only at hgsite
  obtain ⟨hl, hr, hc, hslots, hdim, hdil, hleaf, htip, hinv, hstride, htable⟩ := hgsite
  have hi8 : i < 8 := hg.1 ▸ hi
  constructor
  · unfold siteDegree
    rw [hslots]
    have hleft := bool_toNat_le_one (ss[i]).spec.left
    have hright := bool_toNat_le_one (ss[i]).spec.right
    have hcenter := bool_toNat_le_one (ss[i]).spec.center
    by_cases heven : i%2 = 0
    · have hs := groupSlots_tip_le_one π r (even_groupPoint_tip i hi8 heven)
      omega
    · have hno := presentBond_eq_false π (ringSites.getD i (0,0)) (0,0)
        (odd_ringSite_not_center_adjacent i hi8 heven)
      rw [hc, hno]
      have hs := groupSlots_le_two π r (groupPoint i)
      simp only [Bool.toNat_false]
      omega
  · intro hleafTrue
    have hodd : i%2 = 1 := by
      have hp : i%2 = 1 ∧ SingleReplacement π r (ringSites.getD i (0,0)) := by
        simpa only [hleaf, decide_eq_true_eq] using hleafTrue
      exact hp.1
    rw [htip]
    apply decide_eq_false_iff_not.mpr
    rintro ⟨hzero, _⟩
    omega

end AKLT.W.H1C020
