module
public import CertData.H3.Close.Leaves
public import CertData.H3.Bridge.All

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

set_option maxRecDepth 100000

/-! Unconditional H3 certificate statements, composed from retained finite
checks, the hand-written bridge, and the merged mathematical leaf proofs. -/

namespace CertData.H3.Close

/-- The supplied ten-step automaton satisfies the exact Top V2 contract. -/
theorem automaton10 : AKLT.Blueprint.Top.Automaton10StatementV2 :=
  CertData.H3.Bridge.automatonV2_from_leaves
    CertData.H3.Graph.packed automatonLeaves
    CertData.H3.Check.SuppliedTables.checked
    CertData.H3.Check.BlockLookup.checked
    CertData.H3.GraphAssembly.raw_receipt
    CertData.H3.GraphAssembly.representative_receipt
    CertData.H3.GraphAssembly.field_receipt
    CertData.H3.Check.EdgeCounts.checked

/-- All five stationary certificates satisfy the exact Top V2 contract. -/
theorem stationaryCheck : AKLT.Blueprint.Top.StationaryCheckStatementV2 :=
  CertData.H3.Bridge.All.stationary_from_leaves
    ⟨automatonLeaves, productionCaseLeaves⟩

example : AKLT.Blueprint.Top.Automaton10StatementV2 := automaton10
example : AKLT.Blueprint.Top.StationaryCheckStatementV2 := stationaryCheck

#print automaton10
#print stationaryCheck
#print axioms automaton10
#print axioms stationaryCheck

end CertData.H3.Close

