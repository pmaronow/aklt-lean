module
public import AKLT.Cert.H1.Production.Leaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C016

open AKLT.Cert.H1 AKLT.Cert.H1.Production

private theorem siteSpec_beq_eq (s t : SiteSpec) : (s == t) = true ↔ s = t := by
  cases s
  cases t
  simp [BEq.beq, instBEqSiteSpec.beq]

private theorem gaussian_beq_eq (s t : Gaussian) : (s == t) = true ↔ s = t := by
  cases s
  cases t
  simp [BEq.beq, instBEqGaussian.beq]

private theorem table_beq_eq (s t : Table) : (s == t) = true ↔ s = t := by
  induction s generalizing t with
  | empty => cases t <;> simp [BEq.beq, instBEqTable.beq]
  | leaf z => cases t <;> simp [BEq.beq, instBEqTable.beq, ← gaussian_beq_eq]
  | node cut l r hl hr => cases t <;> simp [BEq.beq, instBEqTable.beq, ← hl, ← hr]

private theorem packedSite_ext (s t : PackedSite)
    (hs : s.spec = t.spec) (ht : s.table = t.table) : s = t := by
  cases s
  cases t
  cases hs
  cases ht
  rfl

theorem sector_bases_eq (base : List PackedSite) (ss : List SectorSite) (parity : Nat)
    (h : sectorNetworkCheck base parity ss = true) : ss.map SectorSite.base = base := by
  simp only [sectorNetworkCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.forall_mem_zipIdx, Nat.zero_add] at h
  apply List.ext_getElem (by simpa only [List.length_map] using h.1)
  intro i hi hb
  have hiz : i < (base.zip ss).length := by
    simp only [List.length_zip, h.1, min_self]
    exact hb
  have hp := h.2 i hiz
  simp only [List.getElem_zip] at hp
  simp only [List.getElem_map]
  exact packedSite_ext _ _ (siteSpec_beq_eq _ _ |>.mp hp.1.1.1)
    (table_beq_eq _ _ |>.mp hp.1.1.2)

theorem parameters_dimensions (base : List PackedSite) (out width lanes denominator p q : Nat)
    (h : parametersCheck base out width lanes denominator p q = true) :
    ∀ s ∈ base, 0 < s.spec.dim := by
  simp only [parametersCheck, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true, List.forall_mem_zipIdx, Nat.zero_add] at h
  intro s hs
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hs
  have hd := h.2 i hi
  rw [he] at hd
  exact hd.1.1.1.1

theorem geometry_spec (a : Input) (base : List PackedSite) (h : geometryCheck a base = true) :
    base.length = 8 ∧ ∀ i (hi : i < base.length), base[i].spec = inputSpec a i := by
  simpa only [geometryCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.forall_mem_zipIdx, Nat.zero_add, siteSpec_beq_eq] using h

private theorem list_eight {α : Type} (xs : List α) (h : xs.length = 8) :
    ∃ a b c d e f g k, xs = [a,b,c,d,e,f,g,k] := by
  rcases xs with _ | ⟨a,xs⟩
  · simp only [List.length_nil] at h; omega
  rcases xs with _ | ⟨b,xs⟩
  · simp only [List.length_cons, List.length_nil] at h; omega
  rcases xs with _ | ⟨c,xs⟩
  · simp only [List.length_cons, List.length_nil] at h; omega
  rcases xs with _ | ⟨d,xs⟩
  · simp only [List.length_cons, List.length_nil] at h; omega
  rcases xs with _ | ⟨e,xs⟩
  · simp only [List.length_cons, List.length_nil] at h; omega
  rcases xs with _ | ⟨f,xs⟩
  · simp only [List.length_cons, List.length_nil] at h; omega
  rcases xs with _ | ⟨g,xs⟩
  · simp only [List.length_cons, List.length_nil] at h; omega
  rcases xs with _ | ⟨k,xs⟩
  · simp only [List.length_cons, List.length_nil] at h; omega
  have hx : xs = [] := List.length_eq_zero_iff.mp (by
    simp only [List.length_cons] at h
    omega)
  subst xs
  exact ⟨a,b,c,d,e,f,g,k,rfl⟩

private theorem input_center_three (a : Input) : (inputSpec a 6).center = false := by
  simp [inputSpec, rawEdges, List.getD_eq_getElem?_getD]

theorem center_counts (a : Input) (base : List PackedSite) (out : Nat)
    (hi : inputCheck a = true) (hg : geometryCheck a base = true) (ho : out = 2*a.outgoing) :
    (centerPairs base).length ≤ 3 ∧
      ((centerPairs base).filter (fun (x,y) => x != out && y != out)).length ≤ 1 := by
  obtain ⟨hlen,hspec⟩ := geometry_spec a base hg
  obtain ⟨s0,s1,s2,s3,s4,s5,s6,s7,rfl⟩ := list_eight base hlen
  have hc0 := congrArg SiteSpec.center (hspec 0 (by simp))
  have hc1 := congrArg SiteSpec.center (hspec 1 (by simp))
  have hc2 := congrArg SiteSpec.center (hspec 2 (by simp))
  have hc3 := congrArg SiteSpec.center (hspec 3 (by simp))
  have hc4 := congrArg SiteSpec.center (hspec 4 (by simp))
  have hc5 := congrArg SiteSpec.center (hspec 5 (by simp))
  have hc6 := congrArg SiteSpec.center (hspec 6 (by simp))
  have hc7 := congrArg SiteSpec.center (hspec 7 (by simp))
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
  rw [input_center_three] at hc6
  simp only [inputSpec, Nat.reduceMod, Nat.reduceBEq, Nat.reduceDiv, Bool.false_and, Bool.true_and,
    beq_self_eq_true] at hc0 hc1 hc2 hc3 hc4 hc5 hc7
  simp only [inputCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hi
  have hout : a.outgoing < 3 := by tauto
  have hedge : (rawEdges a.axes a.corners).getD a.outgoing false = true :=
    by tauto
  have hor : a.outgoing = 0 ∨ a.outgoing = 1 ∨ a.outgoing = 2 := by omega
  rcases hor with h0 | h1 | h2
  · have ho0 : out = 0 := by omega
    have hc : s0.spec.center = true := hc0.trans (by simpa only [h0] using hedge)
    cases h2c : s2.spec.center <;> cases h4c : s4.spec.center <;>
      simp [centerPairs, List.range_succ, hc, hc1, hc3, hc5, hc6, hc7, h2c, h4c, ho0]
  · have ho2 : out = 2 := by omega
    have hc : s2.spec.center = true := hc2.trans (by simpa only [h1] using hedge)
    cases h0c : s0.spec.center <;> cases h4c : s4.spec.center <;>
      simp [centerPairs, List.range_succ, hc, hc1, hc3, hc5, hc6, hc7, h0c, h4c, ho2]
  · have ho4 : out = 4 := by omega
    have hc : s4.spec.center = true := hc4.trans (by simpa only [h2] using hedge)
    cases h0c : s0.spec.center <;> cases h2c : s2.spec.center <;>
      simp [centerPairs, List.range_succ, hc, hc1, hc3, hc5, hc6, hc7, h0c, h2c, ho4]

#print axioms sector_bases_eq
#print axioms parameters_dimensions
#print axioms geometry_spec
#print axioms center_counts

end AKLT.W.H1C016
