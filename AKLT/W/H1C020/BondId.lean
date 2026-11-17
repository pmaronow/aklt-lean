module
public import AKLT.W.H1C020.Bonds

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-!
Each bond sum of the factorized transfer is the ring bond times, if the
corner of that bond is a replaced leaf whose single bond it is, that leaf's
group factor.  Around a corner the two bonds and its slot factor give its
group factor exactly once.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

variable {π : PatternData} {r : Representation}

/-- The corner position of the bond between `i` and `i+1`. -/
def cornerOf (i : Nat) : Nat := if i % 2 = 0 then i + 1 else i

/-- The replaced-leaf factor carried by the bond between `i` and `i+1`. -/
def leafBond (π : PatternData) (r : Representation) (i : Nat) : LPoly :=
  if SingleReplacement π r (ptOf (cornerOf i)) ∧
      presentBond π (ptOf i) (ptOf ((i+1)%8)) = true then groupAt π r (cornerOf i) else 1

lemma leaf_groupAt (c : Nat) (hc : c < 8) (hodd : c % 2 = 1)
    (hs : SingleReplacement π r (ptOf c)) (nb : Plane) (hnb : leafNeighbor π (ptOf c) = nb) :
    groupAt π r c = 1 + MvPolynomial.C (replacementRadius π (ptOf c)) *
      formalDot (fun k => (.inl (nb,k) : LocalVariable)) (fun k => .inr (tokenIndex (ringLeader c),k)) := by
  have hgp : groupPoint c = ptOf c := groupPoint_odd c hodd
  have hmem : groupPoint c ∈ reductionGroups π := by
    rw [hgp]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_union_left _ ((ptOf_corner_iff c hc).mpr hodd), ?_⟩
    rw [hs.1]
    decide
  have hpair : groupIsPair π r (ptOf c) = false := by
    simp [groupIsPair, hs]
  unfold groupAt groupFactor
  rw [if_pos hmem, hgp, hpair, if_neg (by decide), hnb, ring_token_leader c hc, hgp]

lemma radius_eq (x : Plane) (hx : x ∉ templateTips) (hact : x ∈ π.active) (t : SiteSpec)
    (ht : t.diluted = true ↔ π.statusAt x = .D) :
    replacementRadius π x = 1 / (if t.diluted then 3 else 2) := by
  have hne : π.statusAt x ≠ .X := (AKLT.W.H1M006.mem_active_iff π x).mp hact
  unfold replacementRadius
  rw [if_neg hx]
  cases hs : π.statusAt x with
  | U =>
      have : t.diluted = false := by
        cases hd : t.diluted
        · rfl
        · have := ht.mp hd; rw [hs] at this; exact absurd this (by decide)
      simp [this]
  | D =>
      have : t.diluted = true := ht.mpr hs
      simp [this]
  | X => exact absurd hs hne

theorem bond_identity (i : Nat) (hi : i < 8) (s t : SiteSpec) (hs : SiteFlags π r i s)
    (ht : SiteFlags π r ((i+1)%8) t) :
    ((List.range 4).map fun k => Rf i s k * Lf ((i+1)%8) t k).sum =
      ringBond π r i * leafBond π r i := by
  have hj : (i+1)%8 < 8 := Nat.mod_lt _ (by decide)
  have hPr : s.right = presentBond π (ptOf i) (ptOf ((i+1)%8)) := hs.right
  have hPl : t.left = presentBond π (ptOf i) (ptOf ((i+1)%8)) := by
    rw [ht.left, ptOf_left_index i hi]
  cases hP : presentBond π (ptOf i) (ptOf ((i+1)%8))
  · have hR : ∀ k, Rf i s k = edgeOne k := by
      intro k; unfold Rf; rw [hPr, hP]; rfl
    have hL : ∀ k, Lf ((i+1)%8) t k = edgeOne k := by
      intro k; unfold Lf; rw [hPl, hP]; rfl
    simp only [hR, hL, bond_edge_edge, ringBond, leafBond, hP, Bool.false_eq_true, false_and,
      and_false, ↓reduceIte, mul_one]
  · by_cases he : i % 2 = 0
    · have hjodd : (i+1)%8 % 2 = 1 := by omega
      have hj1 : (i+1)%8 = i+1 := by omega
      have hsleaf : s.leaf = false := hs.leaf_false_of_even he
      have hR : ∀ k, Rf i s k = spinB (ptOf i) k := by
        intro k; unfold Rf; rw [hPr, hP, hsleaf]; rfl
      have hcorner : cornerOf i = (i+1)%8 := by unfold cornerOf; rw [if_pos he, hj1]
      have hact := presentBond_active hP
      by_cases hsing : SingleReplacement π r (ptOf ((i+1)%8))
      · have htleaf : t.leaf = true := ht.leaf.mpr ⟨hjodd, hsing⟩
        have hL : ∀ k, Lf ((i+1)%8) t k = leafVal ((i+1)%8) t k := by
          intro k; unfold Lf; rw [hPl, hP, htleaf]; rfl
        have hnb : leafNeighbor π (ptOf ((i+1)%8)) = ptOf i := by
          rcases leaf_corner π r _ hj hjodd hsing with ⟨_, _, h⟩ | ⟨h, _, _⟩
          · rw [h]; congr 1; omega
          · rw [show (i+1)%8 - 1 = i by omega] at h
            rw [h] at hP
            exact absurd hP (by decide)
        simp only [hR, hL]
        rw [bond_spin_leaf _ _ t ht.inverted]
        have hrb : ringBond π r i = 1 := by
          unfold ringBond
          rw [if_neg (fun h => single_not_mem_V π r _ hj hjodd hsing h.2.2)]
        have hlb : leafBond π r i = groupAt π r ((i+1)%8) := by
          unfold leafBond
          rw [hcorner, if_pos ⟨hsing, hP⟩]
        rw [hrb, hlb, leaf_groupAt _ hj hjodd hsing _ hnb,
          radius_eq _ (ptOf_not_tip _ hj) hact.2 t ht.diluted, one_mul]
      · have htleaf : t.leaf = false := by
          cases h' : t.leaf
          · rfl
          · exact absurd (ht.leaf.mp h').2 hsing
        have hL : ∀ k, Lf ((i+1)%8) t k = spinB (ptOf ((i+1)%8)) k := by
          intro k; unfold Lf; rw [hPl, hP, htleaf]; rfl
        simp only [hR, hL]
        rw [bond_spin_spin]
        have hdeg := presentBond_degree hP
        have hrb : ringBond π r i =
            1 + formalDot (fun k => (.inl (ptOf i, k) : LocalVariable))
              (fun k => .inl (ptOf ((i+1)%8), k)) := by
          unfold ringBond
          rw [if_pos ⟨hP, axial_mem_V π r i hi he hact.1, corner_mem_V π r _ hdeg.2 hsing hj⟩]
        have hlb : leafBond π r i = 1 := by
          unfold leafBond
          rw [hcorner, if_neg (fun h => hsing h.1)]
        rw [hrb, hlb, mul_one]
    · have hodd : i % 2 = 1 := by omega
      have hjeven : (i+1)%8 % 2 = 0 := by omega
      have htleaf : t.leaf = false := ht.leaf_false_of_even hjeven
      have hL : ∀ k, Lf ((i+1)%8) t k = spinB (ptOf ((i+1)%8)) k := by
        intro k; unfold Lf; rw [hPl, hP, htleaf]; rfl
      have hcorner : cornerOf i = i := by unfold cornerOf; rw [if_neg he]
      have hact := presentBond_active hP
      by_cases hsing : SingleReplacement π r (ptOf i)
      · have hsleaf : s.leaf = true := hs.leaf.mpr ⟨hodd, hsing⟩
        obtain ⟨hleft, hnb⟩ : presentBond π (ptOf (i-1)) (ptOf i) = false ∧
            leafNeighbor π (ptOf i) = ptOf ((i+1)%8) := by
          rcases leaf_corner π r i hi hodd hsing with ⟨_, h, _⟩ | ⟨h1, _, h3⟩
          · rw [hP] at h; exact absurd h (by decide)
          · exact ⟨h1, h3⟩
        have hsl : s.left = false := by
          rw [hs.left, show (i+7)%8 = i-1 by omega]
          exact hleft
        have hR : ∀ k, Rf i s k = leafVal i s k := by
          intro k; unfold Rf; rw [hPr, hP, hsleaf, hsl]; rfl
        simp only [hR, hL]
        rw [bond_leaf_spin _ _ s hs.inverted]
        have hrb : ringBond π r i = 1 := by
          unfold ringBond
          rw [if_neg (fun h => single_not_mem_V π r i hi hodd hsing h.2.1)]
        have hlb : leafBond π r i = groupAt π r i := by
          unfold leafBond
          rw [hcorner, if_pos ⟨hsing, hP⟩]
        rw [hrb, hlb, leaf_groupAt i hi hodd hsing _ hnb,
          radius_eq _ (ptOf_not_tip i hi) hact.1 s hs.diluted, one_mul]
      · have hsleaf : s.leaf = false := by
          cases h' : s.leaf
          · rfl
          · exact absurd (hs.leaf.mp h').2 hsing
        have hR : ∀ k, Rf i s k = spinB (ptOf i) k := by
          intro k; unfold Rf; rw [hPr, hP, hsleaf]; rfl
        simp only [hR, hL]
        rw [bond_spin_spin]
        have hdeg := presentBond_degree hP
        have hrb : ringBond π r i =
            1 + formalDot (fun k => (.inl (ptOf i, k) : LocalVariable))
              (fun k => .inl (ptOf ((i+1)%8), k)) := by
          unfold ringBond
          rw [if_pos ⟨hP, corner_mem_V π r i hdeg.1 hsing hi,
            axial_mem_V π r _ hj hjeven hact.2⟩]
        have hlb : leafBond π r i = 1 := by
          unfold leafBond
          rw [hcorner, if_neg (fun h => hsing h.1)]
        rw [hrb, hlb, mul_one]

theorem corner_identity (c : Nat) (hc : c < 8) (hodd : c % 2 = 1) :
    leafBond π r (c-1) * leafBond π r c *
      (if c % 2 = 1 ∧ SingleReplacement π r (ptOf c) then 1 else groupAt π r c) = groupAt π r c := by
  have h1 : cornerOf (c-1) = c := by unfold cornerOf; rw [if_pos (by omega)]; omega
  have h2 : cornerOf c = c := by unfold cornerOf; rw [if_neg (by omega)]
  have h3 : (c-1+1)%8 = c := by omega
  unfold leafBond
  rw [h1, h2, h3]
  by_cases hs : SingleReplacement π r (ptOf c)
  · rw [if_pos (show c % 2 = 1 ∧ SingleReplacement π r (ptOf c) from ⟨hodd, hs⟩)]
    rcases leaf_corner π r c hc hodd hs with ⟨ha, hb, _⟩ | ⟨ha, hb, _⟩
    · rw [if_pos (show SingleReplacement π r (ptOf c) ∧
          presentBond π (ptOf (c-1)) (ptOf c) = true from ⟨hs, ha⟩),
        if_neg (show ¬ (SingleReplacement π r (ptOf c) ∧
          presentBond π (ptOf c) (ptOf ((c+1)%8)) = true) from fun h => by
            rw [hb] at h; exact absurd h.2 (by decide))]
      ring
    · rw [if_neg (show ¬ (SingleReplacement π r (ptOf c) ∧
          presentBond π (ptOf (c-1)) (ptOf c) = true) from fun h => by
            rw [ha] at h; exact absurd h.2 (by decide)),
        if_pos (show SingleReplacement π r (ptOf c) ∧
          presentBond π (ptOf c) (ptOf ((c+1)%8)) = true from ⟨hs, hb⟩)]
      ring
  · rw [if_neg (show ¬ (SingleReplacement π r (ptOf c) ∧
          presentBond π (ptOf (c-1)) (ptOf c) = true) from fun h => hs h.1),
      if_neg (show ¬ (SingleReplacement π r (ptOf c) ∧
          presentBond π (ptOf c) (ptOf ((c+1)%8)) = true) from fun h => hs h.1),
      if_neg (show ¬ (c % 2 = 1 ∧ SingleReplacement π r (ptOf c)) from fun h => hs h.2)]
    ring

end AKLT.W.H1C020
