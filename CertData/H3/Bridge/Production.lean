module
public import CertData.H3.Bridge.GraphLayout

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true
set_option maxRecDepth 100000

namespace CertData.H3.Bridge
open AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Defs AKLT.Gen.Packed

/-! These eight closed obligations were generalized in phase 3 to remove all
imports of generated literals/checks. No mathematical proof is supplied. -/
def SpanDataLeaf : Prop := ∀ P : PackedGraph, SpanRepresents P.toGraph
def ClassDataLeaf : Prop := ∀ P : PackedGraph, P.Transcribed → P.blockCheck=true →
  ∀ c : Fin (4^10), P.toGraph.classAt c.val=Automaton10Data.rawClassAt c.val
def DecodeDataLeaf : Prop := ∀ c : Nat, decodeWord 10 c=Automaton10Data.decodeWord 10 c
def QuotientDataLeaf : Prop := ∀ P : PackedGraph, P.Transcribed → P.blockCheck=true →
  P.toGraph.quotient=Automaton10Data.supplied
def UnmaskedDataLeaf : Prop := ∀ P : PackedGraph, P.Transcribed →
  (∀ a : Fin 3741, P.toGraph.representative a.val=Automaton10Data.representativeCode a) ∧
  ∀ (a : Fin 3741) (d : Compass),
    P.toGraph.dest a.val (directionCode d)=Automaton10Data.destinationCode a d ∧
    P.toGraph.kind a.val (directionCode d)=Automaton10Data.kindCode a d
def FieldJoinLeaf : Prop := ∀ G : Graph, FieldReceipt G → fieldBatch G 0 3741=true
def RawShardJoinLeaf : Prop := ∀ G : Graph, RawReceipt G →
  (rawBatch G 0 4096).ok=true ∧ (rawBatch G 0 4096).count=60092
def RepresentativeJoinLeaf : Prop := ∀ G : Graph,
  RepresentativeReceipt G → representativeBatch G 0 3741=true

def AutomatonBridgeLeaves : Prop := SpanDataLeaf ∧ ClassDataLeaf ∧ DecodeDataLeaf ∧ QuotientDataLeaf ∧
  RawShardJoinLeaf ∧ RepresentativeJoinLeaf ∧ RawTrieCoverageLeaf ∧ RawTrieProjectionLeaf ∧
  RawTrieCountLeaf ∧ EdgeCountLeaf ∧ UnmaskedDataLeaf ∧ FieldJoinLeaf ∧
  RawTrieBoundsLeaf ∧ RepresentativeBoundsLeaf ∧ FieldCheckSoundLeaf

/-- Blueprint assembly, parameterized by literal storage and checked receipts. -/
theorem graph_correct_from_leaves (P : PackedGraph) (h : AutomatonBridgeLeaves)
    (hr : RawReceipt P.toGraph) (hp : RepresentativeReceipt P.toGraph) : P.toGraph.quotient.Correct := by
  rcases h with ⟨hspan,_,_,_,hraw,hrep,_,hprojection,_,_,_,_,_,_,_⟩
  exact hprojection P.toGraph (hspan P) (hraw P.toGraph hr).1 (hrep P.toGraph hp)

/-- The designated V2 target, with no generated-module imports in its proof. -/
theorem automatonV2_from_leaves (P : PackedGraph) (h : AutomatonBridgeLeaves)
    (ht : P.Transcribed) (hb : P.blockCheck=true)
    (hr : RawReceipt P.toGraph) (hp : RepresentativeReceipt P.toGraph)
    (hf : FieldReceipt P.toGraph) (he : edgeCounts P.toGraph=(2516,5032,1872)) :
    AKLT.Blueprint.Top.Automaton10StatementV2 := by
  have hcorrect := graph_correct_from_leaves P h hr hp
  rcases h with ⟨hspan,hclass,hdecode,hquot,hraw,hrep,hcoverage,_,hcount,hedge,hdata,hfields,hbounds,hrepbounds,hfieldsound⟩
  have hQ := hquot P ht hb
  have hraw' := hraw P.toGraph hr
  have hc := (hcount P.toGraph).symm.trans hraw'.2
  have hcover := hcoverage P.toGraph (hspan P) hraw'.1
  have he' := hedge P.toGraph he
  have hd := hdata P ht
  refine ⟨hc,?_,?_,?_,?_,?_,?_,?_⟩
  · intro c
    rw [←hclass P ht hb c,←hdecode c.val]
    exact ⟨hbounds P.toGraph (hspan P) hraw'.1 c,hcover c⟩
  · intro a
    rw [←hd.1 a]
    exact hrepbounds P.toGraph (hrep P.toGraph hp) a
  · intro a d
    rw [←(hd.2 a d).1,←(hd.2 a d).2]
    exact hfieldsound P.toGraph (hfields P.toGraph hf) a d
  · exact Eq.mp (congrArg (fun Q : MemoryQuotient 10 3741 => Q.Correct) hQ) hcorrect
  · exact Eq.mp (congrArg (fun Q : MemoryQuotient 10 3741 => quotientEdgeCount Q .straight=2516) hQ) he'.1
  · exact Eq.mp (congrArg (fun Q : MemoryQuotient 10 3741 => quotientEdgeCount Q .turn=5032) hQ) he'.2.1
  · exact Eq.mp (congrArg (fun Q : MemoryQuotient 10 3741 => quotientEdgeCount Q .revisit=1872) hQ) he'.2.2

/-- Full family assembly after the numeric automaton target and five cases. -/
theorem stationaryV2_from_cases (hsquare : (square (0,0) certificateRadius).card=19881)
    (ha : AKLT.Blueprint.Top.Automaton10StatementV2)
    (hbn : CaseV2 .B .north) (hbw : CaseV2 .B .west) (hcn : CaseV2 .C .north)
    (hcw : CaseV2 .C .west) (hcs : CaseV2 .C .south) : AKLT.Blueprint.Top.StationaryCheckStatementV2 :=
  stationaryV2_of_cases hsquare ha.2.2.2.2.1 hbn hbw hcn hcw hcs

#print axioms graph_correct_from_leaves
#print axioms automatonV2_from_leaves
#print axioms stationaryV2_from_cases
end CertData.H3.Bridge
