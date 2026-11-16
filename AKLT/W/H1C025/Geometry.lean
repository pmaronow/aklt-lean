import AKLT.Cert.H1.Production.Leaves

namespace AKLT.W.H1C025
open AKLT.Defs AKLT.Cert.H1

theorem mem_internal (S : Finset Plane) (a b : Plane) :
    (a,b) ∈ internalBonds S ↔
      a ∈ S ∧ b ∈ S ∧ b ∈ positiveNeighbours a := by
  simp [internalBonds, Finset.mem_biUnion, Finset.mem_image, Prod.ext_iff,
    and_comm, and_left_comm, and_assoc]

theorem internal_template {a b : Plane} (he : (a,b) ∈ internalBonds templateSites) :
    (a,b) ∈ templateEdges ∨ (b,a) ∈ templateEdges := by
  obtain ⟨ha,hb,hp⟩ := (mem_internal _ _ _).mp he
  rcases a with ⟨ax,ay⟩
  have hbounds : (-2 ≤ ax ∧ ax ≤ 2) ∧ (-2 ≤ ay ∧ ay ≤ 2) := by
    have h := (Finset.mem_filter.mp ha).1
    simpa [square] using h
  rcases hbounds with ⟨⟨haxl,haxu⟩,⟨hayl,hayu⟩⟩
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  all_goals
    interval_cases ax <;> interval_cases ay <;>
      norm_num [templateSites, square, latticeDist] at ha
  all_goals norm_num [templateSites, square, latticeDist] at hb
  all_goals norm_num [templateEdges]

theorem template_internal (a b : Plane) (he : (a,b) ∈ templateEdges) :
    (a,b) ∈ internalBonds templateSites ∨ (b,a) ∈ internalBonds templateSites := by
  simp only [templateEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he |
    he | he | he | he | he | he | he | he
  all_goals
    cases he
    norm_num [mem_internal, templateSites, square, latticeDist, positiveNeighbours]

def bondCondition (π : PatternData) (a b : Plane) : Prop :=
  π.statusAt a ≠ .X ∧ π.statusAt b ≠ .X ∧
    (a ∈ templateTips ∨ b ∈ π.keptAt a) ∧
    (b ∈ templateTips ∨ a ∈ π.keptAt b)

instance (π : PatternData) (a b : Plane) : Decidable (bondCondition π a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem presentBond_iff (π : PatternData) (a b : Plane)
    (he : (a,b) ∈ templateEdges) :
    presentBond π a b = true ↔ bondCondition π a b := by
  have hi := template_internal a b he
  simp only [presentBond, decide_eq_true_eq, PatternData.bonds, Finset.mem_filter,
    bondCondition]
  tauto

theorem presentBond_symm (π : PatternData) (a b : Plane) :
    presentBond π a b = presentBond π b a := by simp [presentBond, or_comm]

theorem presentBond_mem (π : PatternData) (a b : Plane) :
    presentBond π a b = true ↔ (a,b) ∈ π.bonds ∨ (b,a) ∈ π.bonds := by
  simp only [presentBond, decide_eq_true_eq]

theorem degree_zero (π : PatternData) (x : Plane) :
    patternDegree π x = 0 ↔ ∀ e ∈ templateEdges,
      (e.1 = x ∨ e.2 = x) → presentBond π e.1 e.2 = false := by
  rw [patternDegree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h ⟨a,b⟩ _ hx
    cases hb : presentBond π a b with
    | false => rfl
    | true =>
      rcases (presentBond_mem π a b).mp hb with hab | hba
      · exact (h hab hx).elim
      · exact (h hba (Or.symm hx)).elim
  · intro h e he hx
    have hi := (Finset.mem_filter.mp he).1
    rcases internal_template hi with hab | hba
    · have hf := h e hab hx
      have ht := (presentBond_mem π e.1 e.2).mpr (Or.inl he)
      rw [hf] at ht
      contradiction
    · have hf := h (e.2,e.1) hba (Or.symm hx)
      have ht := (presentBond_mem π e.2 e.1).mpr (Or.inr he)
      rw [hf] at ht
      contradiction

def semanticEdges (π : PatternData) : List Bool :=
  templateEdges.map (fun (a,b) => presentBond π a b)

def edgeLive (edges : List Bool) (i : Nat) : Bool :=
  edges.getD (4+i) false || edges.getD (4+(i+7)%8) false ||
    (i%2 == 0 && (edges.getD (i/2) false || edges.getD (12+i/2) false))

theorem ring_degree_zero (π : PatternData) (i : Fin 8) :
    patternDegree π (ringSites.getD i.val (0,0)) = 0 ↔
      edgeLive (semanticEdges π) i.val = false := by
  rw [degree_zero]
  simp only [templateEdges, List.forall_mem_cons]
  fin_cases i <;>
    simp [templateEdges, ringSites, semanticEdges, edgeLive, Bool.or_eq_false_iff,
      and_comm, and_left_comm, and_assoc]

#print axioms mem_internal
#print axioms internal_template
#print axioms template_internal
#print axioms presentBond_iff
#print axioms presentBond_symm
#print axioms presentBond_mem
#print axioms degree_zero
#print axioms ring_degree_zero

end AKLT.W.H1C025
