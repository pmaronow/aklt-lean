module
public import CertData.H3.Bridge.Production

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C051

open CertData.H3.Bridge AKLT.Cert.H3.Production AKLT.Defs AKLT.Gen.Packed

private theorem packedLane_eq_dataLane (packed width index : Nat) :
    AKLT.Gen.Packed.lane packed width index =
      AKLT.Defs.Automaton10Data.lane packed width index := by
  simp [AKLT.Gen.Packed.lane, AKLT.Defs.Automaton10Data.lane,
    Nat.shiftRight_eq_div_pow]

private theorem directionCode_eq_data (d : Compass) :
    AKLT.Cert.H3.directionCode d = AKLT.Defs.Automaton10Data.directionCode d := by
  cases d <;> rfl

theorem main : CertData.H3.Bridge.UnmaskedDataLeaf := by
  intro P hP
  rcases hP with ⟨_, hrepresentatives, hdestinations, hkinds⟩
  constructor
  · intro a
    change AKLT.Gen.Packed.lane P.representatives 20 a.val =
      AKLT.Defs.Automaton10Data.lane Automaton10Data.representatives 20 a.val
    rw [hrepresentatives]
    exact packedLane_eq_dataLane _ _ _
  · intro a d
    constructor
    · dsimp [PackedGraph.toGraph, AKLT.Defs.Automaton10Data.destinationCode]
      rw [hdestinations, directionCode_eq_data]
      rw [show 4 * a.val = a.val * 4 by omega]
      exact packedLane_eq_dataLane _ _ _
    · dsimp [PackedGraph.toGraph, AKLT.Defs.Automaton10Data.kindCode]
      rw [hkinds, directionCode_eq_data]
      rw [show 4 * a.val = a.val * 4 by omega]
      exact packedLane_eq_dataLane _ _ _

end AKLT.W.H3C051

#print axioms AKLT.W.H3C051.main
