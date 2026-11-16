import AKLT.Blueprint.H3.NodesAutomaton

noncomputable section

open AKLT.Defs

namespace AKLT.W.H3M002

theorem main : AKLT.Blueprint.H3.ProjectionRealizationStatement := by
  classical
  intro m q hm π hπ
  let r : Fin q → DirectionWord m := fun a => Classical.choose (hπ.1 a)
  let Q : MemoryQuotient m q :=
    { project := π
      representative := r
      allowed := fun a d => decide (WindowAdmissible (r a) d)
      kind := fun a d => windowKind (r a) d
      successor := fun a d => π (windowSuccessor (r a) d)
      arrival := fun a => windowArrival (r a) }
  refine ⟨Q, ?_, ?_⟩
  · change (∀ a, RawWindow (r a) ∧ π (r a) = a) ∧
      ∀ w : DirectionWord m, RawWindow w → ∀ d : Compass,
        (Q.allowed (Q.project w) d = true ↔ WindowAdmissible w d) ∧
        (WindowAdmissible w d →
          Q.kind (Q.project w) d = windowKind w d ∧
          Q.successor (Q.project w) d = Q.project (windowSuccessor w d) ∧
          (windowKind w d ≠ .revisit → Q.arrival (Q.project w) = windowArrival w))
    constructor
    · intro a
      exact Classical.choose_spec (hπ.1 a)
    · intro w hw d
      let v := r (π w)
      have hv : RawWindow v := (Classical.choose_spec (hπ.1 (π w))).1
      have hclass : π w = π v := (Classical.choose_spec (hπ.1 (π w))).2.symm
      have hfibre := hπ.2 w v hw hv hclass
      constructor
      · change (decide (WindowAdmissible (r (π w)) d) = true ↔
          WindowAdmissible w d)
        rw [decide_eq_true_eq]
        exact (hfibre.1 d).1.symm
      · intro hadm
        refine ⟨?_, ?_, ?_⟩
        · change windowKind (r (π w)) d = windowKind w d
          exact (hfibre.1 d).2.1.symm
        · change π (windowSuccessor (r (π w)) d) =
            π (windowSuccessor w d)
          exact ((hfibre.1 d).2.2 hadm).symm
        · intro hnonrevisit
          change windowArrival (r (π w)) = windowArrival w
          exact (hfibre.2 ⟨d, hadm, hnonrevisit⟩).symm
  · intro w hw
    rfl

end AKLT.W.H3M002

end

#print axioms AKLT.W.H3M002.main
