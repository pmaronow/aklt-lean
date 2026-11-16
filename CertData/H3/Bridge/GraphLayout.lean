import CertData.H3.Bridge.Interface

namespace CertData.H3.Bridge
open AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Defs AKLT.Gen.Packed

/-- The untrusted literal storage. The interface contains no concrete data. -/
structure PackedGraph where
  denseClass : Nat
  blocks : PlaneTree
  representatives : Nat
  destinations : Nat
  kinds : Nat

def PackedGraph.classAt (P : PackedGraph) (code : Nat) : Nat :=
  if code<1048576 then lane (P.blocks.get (code/4096)) 12 (code%4096) else 3741
def PackedGraph.classSpan (P : PackedGraph) (start count : Nat) : Nat :=
  Nat.land (P.blocks.get (start/4096) >>> (12*(start%4096))) (2^(12*count)-1)
def PackedGraph.toGraph (P : PackedGraph) : Graph :=
  ⟨P.classAt,P.classSpan,(fun a => lane P.representatives 20 a),
    (fun a d => lane P.destinations 12 (4*a+d)),(fun a d => lane P.kinds 2 (4*a+d))⟩
def PackedGraph.blockCheck (P : PackedGraph) : Bool :=
  (List.range 256).all (fun i => P.blocks.get i == lane P.denseClass 49152 i)
def PackedGraph.Transcribed (P : PackedGraph) : Prop :=
  P.denseClass=Automaton10Data.rawClass ∧ P.representatives=Automaton10Data.representatives ∧
  P.destinations=Automaton10Data.destinations ∧ P.kinds=Automaton10Data.edgeKinds

/-- Receipts refer to structurally sharded checks, without importing any check module. -/
def RawReceipt (G : Graph) : Prop := ∃ expected : Fin 64 → RawStats,
  (∀ i : Fin 64, rawBatch G (i.val*64) 64=expected i) ∧
  (∀ i : Fin 64, (expected i).ok=true) ∧
  ((List.finRange 64).map fun i => (expected i).count).sum=60092
def RepresentativeReceipt (G : Graph) : Prop := ∀ i : Fin 59,
  representativeBatch G (i.val*64) (min 64 (3741-i.val*64))=true
def FieldReceipt (G : Graph) : Prop := ∀ i : Fin 59,
  fieldBatch G (i.val*64) (min 64 (3741-i.val*64))=true

end CertData.H3.Bridge
