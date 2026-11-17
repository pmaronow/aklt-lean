module
public import AKLT.Cert.H1.Production.Leaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C031

open AKLT.Defs AKLT.Cert.H1

theorem mem_internalBonds_iff {G : Finset Plane} {a b : Plane} :
    (a, b) ∈ internalBonds G ↔ a ∈ G ∧ b ∈ G ∧
      (b = (a.1 + 1, a.2) ∨ b = (a.1, a.2 + 1)) := by
  simp [internalBonds, positiveNeighbors, and_assoc, and_left_comm, and_comm]

theorem internalBonds_no_reverse {G : Finset Plane} {a b : Plane}
    (h : (a, b) ∈ internalBonds G) : (b, a) ∉ internalBonds G := by
  intro hr
  have hp := (mem_internalBonds_iff.mp h).2.2
  have hq := (mem_internalBonds_iff.mp hr).2.2
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  simp only [Prod.mk.injEq] at hp hq
  omega

theorem mem_square_iff {x a : Plane} {u : Nat} :
    x ∈ square a u ↔
      (a.1 - (u : ℤ) ≤ x.1 ∧ x.1 ≤ a.1 + u) ∧
      (a.2 - (u : ℤ) ≤ x.2 ∧ x.2 ≤ a.2 + u) := by
  rw [square, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_Icc]

theorem mem_templateSites_iff {x : Plane} :
    x ∈ templateSites ↔
      ((-2 ≤ x.1 ∧ x.1 ≤ 2) ∧ (-2 ≤ x.2 ∧ x.2 ≤ 2)) ∧
      latticeDist x (0, 0) ≤ 2 := by
  rw [templateSites, Finset.mem_filter, mem_square_iff]
  norm_num

theorem templateSite_cases {x : Plane} (hx : x ∈ templateSites) :
    x = (0, 0) ∨ x ∈ ringSites ∨ x ∈ templateTips := by
  rcases x with ⟨a, b⟩
  have hx := mem_templateSites_iff.mp hx
  have ha₁ : -2 ≤ a := hx.1.1.1
  have ha₂ : a ≤ 2 := hx.1.1.2
  have hb₁ : -2 ≤ b := hx.1.2.1
  have hb₂ : b ≤ 2 := hx.1.2.2
  interval_cases a <;> interval_cases b <;>
    norm_num [latticeDist] at hx <;> norm_num [ringSites, templateTips]

theorem internalBond_templateEdge {a b : Plane}
    (h : (a, b) ∈ internalBonds templateSites) :
    (a, b) ∈ templateEdges ∨ (b, a) ∈ templateEdges := by
  rcases mem_internalBonds_iff.mp h with ⟨ha, hb, hp⟩
  rcases a with ⟨a₁, a₂⟩
  have ha := mem_templateSites_iff.mp ha
  have hb := mem_templateSites_iff.mp hb
  have ha₁ : -2 ≤ a₁ := ha.1.1.1
  have ha₂ : a₁ ≤ 2 := ha.1.1.2
  have ha₃ : -2 ≤ a₂ := ha.1.2.1
  have ha₄ : a₂ ≤ 2 := ha.1.2.2
  rcases hp with rfl | rfl <;>
    interval_cases a₁ <;> interval_cases a₂ <;>
    norm_num [latticeDist] at ha <;> norm_num [latticeDist] at hb <;>
    norm_num [templateEdges]

theorem reflectPoint_involution (f : Bool) (x : Plane) :
    reflectPoint f (reflectPoint f x) = x := by
  cases f <;> simp [reflectPoint]

theorem reflectPoint_false (x : Plane) : reflectPoint false x = x := by
  simp [reflectPoint]

theorem reflectPoint_true (x : Plane) : reflectPoint true x = (-x.1, x.2) := by
  simp [reflectPoint]

theorem reflectPoint_comm (f g : Bool) (x : Plane) :
    reflectPoint f (reflectPoint g x) = reflectPoint g (reflectPoint f x) := by
  cases f <;> cases g <;> simp [reflectPoint]

theorem reflect_ringSite (f : Bool) {x : Plane} (hx : x ∈ ringSites) :
    reflectPoint f x ∈ ringSites := by
  cases f
  · simpa only [reflectPoint_false] using hx
  · simp only [ringSites, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [reflectPoint, ringSites]

theorem reflect_tip (f : Bool) {x : Plane} (hx : x ∈ templateTips) :
    reflectPoint f x ∈ templateTips := by
  cases f
  · simpa only [reflectPoint_false] using hx
  · simp only [templateTips, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      norm_num [reflectPoint, templateTips]

theorem reflect_templateEdge (f : Bool) {a b : Plane}
    (h : (a, b) ∈ templateEdges ∨ (b, a) ∈ templateEdges) :
    (reflectPoint f a, reflectPoint f b) ∈ templateEdges ∨
      (reflectPoint f b, reflectPoint f a) ∈ templateEdges := by
  cases f
  · simpa only [reflectPoint_false] using h
  · simp only [templateEdges, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at h
    rcases h with h | h <;>
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num [reflectPoint, templateEdges]

theorem presentBond_symm (π : PatternData) (a b : Plane) :
    presentBond π a b = presentBond π b a := by
  simp only [presentBond, or_comm]

theorem presentBond_templateEdge {π : PatternData} {a b : Plane}
    (h : presentBond π a b = true) :
    (a, b) ∈ templateEdges ∨ (b, a) ∈ templateEdges := by
  have hm : (a, b) ∈ π.bonds ∨ (b, a) ∈ π.bonds := of_decide_eq_true h
  rcases hm with hm | hm
  · exact internalBond_templateEdge (Finset.mem_filter.mp hm).1
  · exact (internalBond_templateEdge (Finset.mem_filter.mp hm).1).symm

theorem bonds_eq_of_presentBond_eq {π ρ : PatternData}
    (h : ∀ a b, presentBond π a b = presentBond ρ a b) : π.bonds = ρ.bonds := by
  ext ⟨a, b⟩
  by_cases hi : (a, b) ∈ internalBonds templateSites
  · have hr := internalBonds_no_reverse hi
    have hnπ : (b, a) ∉ π.bonds := fun hm => hr (Finset.mem_filter.mp hm).1
    have hnρ : (b, a) ∉ ρ.bonds := fun hm => hr (Finset.mem_filter.mp hm).1
    have he := h a b
    simpa only [presentBond, hnπ, hnρ, or_false, decide_eq_decide] using he
  · have hnπ : (a, b) ∉ π.bonds := fun hm => hi (Finset.mem_filter.mp hm).1
    have hnρ : (a, b) ∉ ρ.bonds := fun hm => hi (Finset.mem_filter.mp hm).1
    simp only [hnπ, hnρ]

theorem positiveDegree_site_status {π : PatternData} {x : Plane}
    (hx : 0 < patternDegree π x) : x ∈ templateSites ∧ π.statusAt x ≠ .X := by
  obtain ⟨⟨a, b⟩, he⟩ := Finset.card_pos.mp hx
  rcases Finset.mem_filter.mp he with ⟨he, hi⟩
  have hd := Finset.mem_filter.mp he
  have ht := mem_internalBonds_iff.mp hd.1
  rcases hi with rfl | rfl
  · exact ⟨ht.1, hd.2.1⟩
  · exact ⟨ht.2.1, hd.2.2.1⟩

end AKLT.W.H1C031

#print axioms AKLT.W.H1C031.mem_internalBonds_iff
#print axioms AKLT.W.H1C031.internalBonds_no_reverse
#print axioms AKLT.W.H1C031.mem_square_iff
#print axioms AKLT.W.H1C031.mem_templateSites_iff
#print axioms AKLT.W.H1C031.templateSite_cases
#print axioms AKLT.W.H1C031.internalBond_templateEdge
#print axioms AKLT.W.H1C031.reflectPoint_involution
#print axioms AKLT.W.H1C031.reflectPoint_false
#print axioms AKLT.W.H1C031.reflectPoint_true
#print axioms AKLT.W.H1C031.reflectPoint_comm
#print axioms AKLT.W.H1C031.reflect_ringSite
#print axioms AKLT.W.H1C031.reflect_tip
#print axioms AKLT.W.H1C031.reflect_templateEdge
#print axioms AKLT.W.H1C031.presentBond_symm
#print axioms AKLT.W.H1C031.presentBond_templateEdge
#print axioms AKLT.W.H1C031.bonds_eq_of_presentBond_eq
#print axioms AKLT.W.H1C031.positiveDegree_site_status
