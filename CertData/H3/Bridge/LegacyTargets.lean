import CertData.H3.Bridge.Interface

namespace CertData.H3.Bridge
open AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Defs

/-- Centre zero is already one of the terminal clauses in both predicates. -/
def PassesEquivalenceLeaf : Prop := ∀ (Q : MemoryQuotient 10 3741) (C : StationaryData 3741)
    (X : PairType) (d₀ : Compass), C.Passes Q X d₀ ↔ C.PassesV2 Q X d₀

/-- Forget only the extra supplied-data assertions in the strengthened target. -/
theorem legacy_automaton_from_v2 (h : AKLT.Blueprint.Top.Automaton10StatementV2) :
    AKLT.Blueprint.Top.Automaton10Statement :=
  ⟨h.1,Automaton10Data.supplied,h.2.2.2.2.1,h.2.2.2.2.2⟩

/-- Assembly retaining exactly the same certificate family and rational bounds. -/
theorem legacy_stationary_from_v2 (heq : PassesEquivalenceLeaf)
    (h : AKLT.Blueprint.Top.StationaryCheckStatementV2) : AKLT.Blueprint.Top.StationaryCheckStatement := by
  rcases h with ⟨hs,hq,C,hC⟩
  refine ⟨hs,Automaton10Data.supplied,hq,C,?_⟩
  intro k hk
  exact ⟨(heq Automaton10Data.supplied (C k) k.1 k.2).mpr (hC k hk).1,(hC k hk).2⟩

#print axioms legacy_automaton_from_v2
#print axioms legacy_stationary_from_v2
end CertData.H3.Bridge
