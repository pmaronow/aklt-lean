import AKLT.W.H1C020.Split
import AKLT.W.H1C020.Reduction

/-!
Identification of the uncontracted local factors with the factors of the
reduced integrand: the centre-edge factor is the inserted ring coordinate,
the group-slot factor of a non-leaf site is its group factor, and each bond
sum is the ring bond, or the replaced leaf's factor on its single bond.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

/-- The flags of an inversion-erased local tensor at ring position `i`. -/
structure SiteFlags (π : PatternData) (r : Representation) (i : Nat) (s : SiteSpec) : Prop where
  left : s.left = presentBond π (ptOf ((i+7)%8)) (ptOf i)
  right : s.right = presentBond π (ptOf i) (ptOf ((i+1)%8))
  center : s.center = presentBond π (ptOf i) (0,0)
  nslots : s.nslots = groupSlots π r (groupPoint i)
  diluted : s.diluted = true ↔ π.statusAt (ptOf i) = .D
  leaf : s.leaf = true ↔ (i % 2 = 1 ∧ SingleReplacement π r (ptOf i))
  tip : s.tip = true ↔ (i % 2 = 0 ∧ groupPoint i ∈ reductionGroups π)
  inverted : s.inverted = false

lemma siteFlags_of_geometry {π : PatternData} {r : Representation} {I : Finset (Fin 20)}
    {ss : List PackedSite} (hg : NetworkGeometry π r I ss) (i : Nat) (hi : i < ss.length) :
    SiteFlags π r i (eraseInversion (ss[i]).spec) := by
  have hizip : (ss[i], i) ∈ ss.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
  have h := hg.2 (ss[i], i) hizip
  dsimp only at h
  obtain ⟨hl, hr, hc, hslots, _, hdil, hleaf, htip, _, _, _⟩ := h
  exact { left := hl, right := hr, center := hc, nslots := hslots
          diluted := by
            change (ss[i]).spec.diluted = true ↔ _
            rw [hdil]; simp only [decide_eq_true_eq]; exact Iff.rfl
          leaf := by
            change (ss[i]).spec.leaf = true ↔ _
            rw [hleaf]; simp only [decide_eq_true_eq]; exact Iff.rfl
          tip := by
            change (ss[i]).spec.tip = true ↔ _
            rw [htip]; simp only [decide_eq_true_eq]
          inverted := rfl }

variable {π : PatternData} {r : Representation}

lemma SiteFlags.leaf_false_of_even {i : Nat} {s : SiteSpec} (h : SiteFlags π r i s)
    (he : i % 2 = 0) : s.leaf = false := by
  cases hl : s.leaf
  · rfl
  · have := (h.leaf.mp hl).1
    omega

lemma SiteFlags.even_of_center {i : Nat} {s : SiteSpec} (h : SiteFlags π r i s) (hi : i < 8)
    (hc : s.center = true) : i % 2 = 0 := by
  by_contra hodd
  have hno := presentBond_eq_false π (ringSites.getD i (0,0)) (0,0)
    (odd_ringSite_not_center_adjacent i hi hodd)
  rw [h.center] at hc
  exact absurd (hno ▸ hc : false = true) (by decide)

/-! ### Small expansions -/

/-- Vector token coordinate. -/
def vX (j : Fin 20) (k : Fin 3) : LPoly := MvPolynomial.X (.inr (j,k))

lemma liftV_vv1 (t : Nat) : liftV (vectorVariable t 1) = vX (tokenIndex t) 0 := by
  simp only [liftV, vectorVariable, MvPolynomial.rename_X]; rfl

lemma liftV_vv2 (t : Nat) : liftV (vectorVariable t 2) = vX (tokenIndex t) 1 := by
  simp only [liftV, vectorVariable, MvPolynomial.rename_X]; rfl

lemma liftV_vv3 (t : Nat) : liftV (vectorVariable t 3) = vX (tokenIndex t) 2 := by
  simp only [liftV, vectorVariable, MvPolynomial.rename_X]; rfl

lemma beq10 : ((1:Nat) == 0) = false := rfl
lemma beq20 : ((2:Nat) == 0) = false := rfl
lemma beq30 : ((3:Nat) == 0) = false := rfl

lemma spinB_0 (x : Plane) : spinB x 0 = 1 := by simp [spinB]
lemma spinB_1 (x : Plane) : spinB x 1 = sv x 0 := by simp [spinB]
lemma spinB_2 (x : Plane) : spinB x 2 = sv x 1 := by simp [spinB]
lemma spinB_3 (x : Plane) : spinB x 3 = sv x 2 := by simp [spinB]

lemma sum_range4 (F : Nat → LPoly) : ((List.range 4).map F).sum = F 0 + F 1 + F 2 + F 3 := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

lemma formalDot_inl_inl (x y : Plane) :
    formalDot (fun k => (.inl (x,k) : LocalVariable)) (fun k => .inl (y,k)) =
      sv x 0 * sv y 0 + sv x 1 * sv y 1 + sv x 2 * sv y 2 := by
  simp [formalDot, Fin.sum_univ_three, sv]

lemma formalDot_inl_inr (x : Plane) (j : Fin 20) :
    formalDot (fun k => (.inl (x,k) : LocalVariable)) (fun k => .inr (j,k)) =
      sv x 0 * vX j 0 + sv x 1 * vX j 1 + sv x 2 * vX j 2 := by
  simp [formalDot, Fin.sum_univ_three, sv, vX]

lemma bond_spin_spin (x y : Plane) :
    ((List.range 4).map fun k => spinB x k * spinB y k).sum =
      1 + formalDot (fun k => (.inl (x,k) : LocalVariable)) (fun k => .inl (y,k)) := by
  rw [sum_range4, formalDot_inl_inl, spinB_0, spinB_0, spinB_1, spinB_1, spinB_2, spinB_2,
    spinB_3, spinB_3]
  ring

lemma leafVal_eq (j : Nat) (t : SiteSpec) (ht : t.inverted = false) (k : Nat) :
    leafVal j t k = if k = 0 then 1 else
      MvPolynomial.C (1 / (if t.diluted then 3 else 2)) * liftV (vectorVariable (ringLeader j) k) := by
  unfold leafVal leafScalar
  by_cases hk : k = 0
  · simp [hk]
  · simp [hk, ht]

lemma bond_spin_leaf (x : Plane) (j : Nat) (t : SiteSpec) (ht : t.inverted = false) :
    ((List.range 4).map fun k => spinB x k * leafVal j t k).sum =
      1 + MvPolynomial.C (1 / (if t.diluted then 3 else 2)) *
        formalDot (fun k => (.inl (x,k) : LocalVariable)) (fun k => .inr (tokenIndex (ringLeader j),k)) := by
  rw [sum_range4, formalDot_inl_inr]
  simp only [leafVal_eq j t ht, spinB_0, spinB_1, spinB_2, spinB_3, liftV_vv1, liftV_vv2,
    liftV_vv3, one_ne_zero, OfNat.ofNat_ne_zero, ↓reduceIte]
  ring

lemma bond_leaf_spin (y : Plane) (j : Nat) (t : SiteSpec) (ht : t.inverted = false) :
    ((List.range 4).map fun k => leafVal j t k * spinB y k).sum =
      1 + MvPolynomial.C (1 / (if t.diluted then 3 else 2)) *
        formalDot (fun k => (.inl (y,k) : LocalVariable)) (fun k => .inr (tokenIndex (ringLeader j),k)) := by
  rw [← bond_spin_leaf y j t ht]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k _
  ring

lemma bond_edge_edge : ((List.range 4).map fun k => edgeOne k * edgeOne k).sum = 1 := by
  rw [sum_range4]
  simp [edgeOne]

/-! ### Centre-edge factor -/

lemma Cf_eq_ringCoordinate {i : Nat} {s : SiteSpec} (h : SiteFlags π r i s) (hi : i < 8)
    (v : Nat) (hv3 : v ≤ 3) (hvc : v ≠ 0 → s.center = true) :
    Cf i s v = ringCoordinate i v := by
  unfold Cf
  cases hc : s.center
  · have hv : v = 0 := by
      by_contra hne
      have := hvc hne
      rw [hc] at this
      exact absurd this (by decide)
    subst hv
    simp [edgeOne, ringCoordinate]
  · have hl := h.leaf_false_of_even (h.even_of_center hi hc)
    simp only [hl, Bool.false_eq_true, ↓reduceIte, ↓reduceIte]
    interval_cases v <;> simp [spinB, ringCoordinate, sv, ptOf]

/-! ### Group-slot factor -/

lemma colorChoices_one : colorChoices 1 = [[0],[1],[2],[3]] := rfl

lemma colorChoices_two : colorChoices 2 =
    [[0,0],[0,1],[0,2],[0,3],[1,0],[1,1],[1,2],[1,3],
     [2,0],[2,1],[2,2],[2,3],[3,0],[3,1],[3,2],[3,3]] := rfl

lemma Gf_eq {i : Nat} {s : SiteSpec} (h : SiteFlags π r i s) (hi : i < 8) :
    Gf i s = if i % 2 = 1 ∧ SingleReplacement π r (ptOf i) then 1 else groupAt π r i := by
  by_cases hl : s.leaf = true
  · rw [if_pos (h.leaf.mp hl)]
    simp [Gf, hl]
  rw [if_neg (fun h' => hl (h.leaf.mpr h'))]
  have hl' : s.leaf = false := by simpa using hl
  unfold Gf groupAt
  rw [if_neg hl]
  have hinv := h.inverted
  by_cases he : i % 2 = 0
  · have htipx : groupPoint i ∈ templateTips := even_groupPoint_tip i hi he
    have hpair : groupIsPair π r (groupPoint i) = false := by
      simp [groupIsPair, tip_not_corner htipx]
    by_cases hg : groupPoint i ∈ reductionGroups π
    · have hn : s.nslots = 1 := by rw [h.nslots]; simp [groupSlots, hg, hpair]
      have ht : s.tip = true := h.tip.mpr ⟨he, hg⟩
      rw [if_pos hg, hn, colorChoices_one]
      unfold groupFactor
      rw [hpair, if_neg (by decide), tip_leafNeighbour π i hi he hg,
        ← ring_token_leader i hi, formalDot_inl_inr]
      have hrad : replacementRadius π (groupPoint i) = 3/5 := by
        simp [replacementRadius, htipx]
      rw [hrad]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tipScalar, signScalar,
        ht, hinv, spinM, vectorMonomial, List.headD_cons, spinB_0, spinB_1, spinB_2, spinB_3,
        Bool.false_and, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, beq10, beq20, beq30,
        map_one, map_mul, liftV_vv1, liftV_vv2, liftV_vv3, List.prod_cons, List.prod_nil]
      try simp only [MvPolynomial.C_mul, MvPolynomial.C_1]
      ring
    · have hn : s.nslots = 0 := by rw [h.nslots]; simp [groupSlots, hg]
      rw [if_neg hg, hn]
      simp [colorChoices, tipScalar, signScalar, spinM, vectorMonomial]
  · have hodd : i % 2 = 1 := by omega
    have hgp : groupPoint i = ptOf i := groupPoint_odd i hodd
    have hns : ¬ SingleReplacement π r (ptOf i) := fun hs => hl (h.leaf.mpr ⟨hodd, hs⟩)
    have hcorner : ptOf i ∈ templateCorners := (ptOf_corner_iff i hi).mpr hodd
    have htip : s.tip = false := by
      cases ht : s.tip
      · rfl
      · have := (h.tip.mp ht).1
        omega
    by_cases hg : groupPoint i ∈ reductionGroups π
    · have hpair : groupIsPair π r (groupPoint i) = true := by
        rw [hgp]
        simp [groupIsPair, hcorner, hns]
      have hn : s.nslots = 2 := by rw [h.nslots]; simp [groupSlots, hg, hpair]
      rw [if_pos hg, hn, colorChoices_two]
      unfold groupFactor
      rw [hpair, if_pos rfl, ← ring_token_leader i hi, ← ring_token_second i hi, hgp,
        formalDot_inl_inr, formalDot_inl_inr]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tipScalar, signScalar,
        htip, hinv, spinM, vectorMonomial, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        beq_self_eq_true, beq10, beq20, beq30, map_one, map_mul, liftV_vv1, liftV_vv2, liftV_vv3,
        spinB_0, spinB_1, spinB_2, spinB_3, List.prod_cons, List.prod_nil, mul_one,
        MvPolynomial.C_1, one_mul]
      ring
    · have hn : s.nslots = 0 := by rw [h.nslots]; simp [groupSlots, hg]
      rw [if_neg hg, hn]
      simp [colorChoices, tipScalar, signScalar, spinM, vectorMonomial]

end AKLT.W.H1C020
