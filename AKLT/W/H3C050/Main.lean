import CertData.H3.Bridge.Production

namespace AKLT.W.H3C050

open AKLT.Cert.H3.Production AKLT.Defs AKLT.Gen.Packed
open CertData.H3.Bridge

private theorem lane_nested (P i j : Nat) (hj : j < 4096) :
    lane (lane P 49152 i) 12 j = lane P 12 (i * 4096 + j) := by
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [AKLT.Gen.Packed.testBit_lane]
  by_cases hb : b < 12
  · have hbig : 12 * j + b < 49152 := by omega
    have heq : 49152 * i + (12 * j + b) = 12 * (i * 4096 + j) + b := by omega
    simp [hb, hbig, heq]
  · simp [hb]

private theorem encodeWord_succ {n : Nat} (w : AKLT.Defs.DirectionWord (n+1)) :
    AKLT.Cert.H3.encodeWord w =
      AKLT.Cert.H3.directionCode (w 0) * 4^n +
        AKLT.Cert.H3.encodeWord (fun i => w i.succ) := by
  simp only [AKLT.Cert.H3.encodeWord, List.finRange_succ, List.map_cons, List.sum_cons]
  rw [List.map_map]
  simp only [Fin.val_zero, Nat.add_sub_cancel_right]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hii : i.val < n := i.isLt
  simp only [Function.comp_apply, Fin.val_succ]
  have hexp : n - (i.val + 1) = n - 1 - i.val := by omega
  rw [hexp]

private theorem encodeWord_lt {n : Nat} (w : AKLT.Defs.DirectionWord n) :
    AKLT.Cert.H3.encodeWord w < 4^n := by
  induction n with
  | zero => simp [AKLT.Cert.H3.encodeWord]
  | succ n ih =>
    rw [encodeWord_succ]
    have hd : AKLT.Cert.H3.directionCode (w 0) < 4 := by
      cases w 0 <;> decide
    have hr := ih (fun i => w i.succ)
    rw [pow_succ]
    nlinarith [show 0 < 4^n by positivity]

private theorem directionCode_eq_data (d : AKLT.Defs.Compass) :
    AKLT.Cert.H3.directionCode d = AKLT.Defs.Automaton10Data.directionCode d := by
  cases d <;> rfl

private theorem direction_eq_data (c : Nat) :
    AKLT.Cert.H3.direction c = AKLT.Defs.Automaton10Data.direction c := by
  cases c <;> rfl

private theorem lane_eq_data (p b i : Nat) :
    AKLT.Gen.Packed.lane p b i = AKLT.Defs.Automaton10Data.lane p b i := by
  simp [AKLT.Gen.Packed.lane, AKLT.Defs.Automaton10Data.lane,
    Nat.shiftRight_eq_div_pow]

private theorem edgeIndex_eq (a : Nat) (d : AKLT.Defs.Compass) :
    4*a + AKLT.Cert.H3.directionCode d =
      a*4 + AKLT.Defs.Automaton10Data.directionCode d := by
  rw [directionCode_eq_data]
  ring

private theorem decodeWord_eq_data {n code : Nat} :
    AKLT.Cert.H3.decodeWord n code = AKLT.Defs.Automaton10Data.decodeWord n code := by
  funext i
  simp only [AKLT.Cert.H3.decodeWord, AKLT.Defs.Automaton10Data.decodeWord]
  exact direction_eq_data _

private theorem encodeWord_eq_data {n : Nat} (w : AKLT.Defs.DirectionWord n) :
    AKLT.Cert.H3.encodeWord w = AKLT.Defs.Automaton10Data.encodeWord w := by
  have hcode : AKLT.Cert.H3.directionCode = AKLT.Defs.Automaton10Data.directionCode := by
    funext d
    cases d <;> rfl
  simp [AKLT.Cert.H3.encodeWord, AKLT.Defs.Automaton10Data.encodeWord, hcode]

private theorem classAt_eq_rawClassAt (P : PackedGraph)
    (ht : P.Transcribed) (hb : P.blockCheck = true) (c : Nat) (hc : c < 4^10) :
    P.toGraph.classAt c = AKLT.Defs.Automaton10Data.rawClassAt c := by
  rcases ht with ⟨hdense, _, _, _⟩
  have hblocks : ∀ i < 256, P.blocks.get i = lane P.denseClass 49152 i := by
    intro i hi
    have himem : i ∈ List.range 256 := List.mem_range.mpr hi
    have h := (List.all_eq_true.mp hb) i himem
    simpa [PackedGraph.blockCheck] using h
  have hlim : c < 1048576 := by simpa using hc
  have hi : c / 4096 < 256 := by omega
  change P.classAt c = AKLT.Defs.Automaton10Data.rawClassAt c
  dsimp [PackedGraph.classAt]
  simp [hlim]
  rw [hblocks (c / 4096) hi, hdense]
  rw [lane_nested AKLT.Defs.Automaton10Data.rawClass (c / 4096) (c % 4096) (by omega)]
  have hcode : c / 4096 * 4096 + c % 4096 = c := by omega
  rw [hcode]
  simp [AKLT.Gen.Packed.lane, AKLT.Defs.Automaton10Data.lane,
    AKLT.Defs.Automaton10Data.rawClassAt, Nat.shiftRight_eq_div_pow]

private theorem quotient_ext {m q : Nat} (Q R : MemoryQuotient m q)
    (hp : Q.project = R.project) (hr : Q.representative = R.representative)
    (ha : Q.allowed = R.allowed) (hk : Q.kind = R.kind)
    (hs : Q.successor = R.successor) (hv : Q.arrival = R.arrival) : Q = R := by
  cases Q
  cases R
  simp_all

theorem main : CertData.H3.Bridge.QuotientDataLeaf := by
  intro P ht hb
  rcases ht with ⟨hdense, hrep, hdest, hkind⟩
  apply quotient_ext
  · funext w
    apply Fin.ext
    simp only [AKLT.Cert.H3.Production.Graph.quotient,
      AKLT.Defs.Automaton10Data.supplied, AKLT.Cert.H3.Production.finState]
    have hclass := classAt_eq_rawClassAt P ⟨hdense, hrep, hdest, hkind⟩ hb
      (AKLT.Cert.H3.encodeWord w) (by simpa using encodeWord_lt w)
    rw [hclass, encodeWord_eq_data]
  · funext a
    change AKLT.Cert.H3.decodeWord 10 (AKLT.Gen.Packed.lane P.representatives 20 a.val) =
      AKLT.Defs.Automaton10Data.decodeWord 10
        (AKLT.Defs.Automaton10Data.lane AKLT.Defs.Automaton10Data.representatives 20 a.val)
    rw [decodeWord_eq_data, hrep, lane_eq_data]
  · funext a d
    change (AKLT.Gen.Packed.lane P.destinations 12
        (4*a.val + AKLT.Cert.H3.directionCode d) != 0) =
      (AKLT.Defs.Automaton10Data.lane AKLT.Defs.Automaton10Data.destinations 12
        (a.val*4 + AKLT.Defs.Automaton10Data.directionCode d) != 0)
    rw [hdest, edgeIndex_eq, lane_eq_data]
  · funext a d
    change AKLT.Cert.H3.stepKind (AKLT.Gen.Packed.lane P.kinds 2
        (4*a.val + AKLT.Cert.H3.directionCode d)) =
      (match AKLT.Defs.Automaton10Data.kindCode a d with
       | 0 => AKLT.Defs.StepKind.straight
       | 1 => AKLT.Defs.StepKind.turn
       | _ => AKLT.Defs.StepKind.revisit)
    rw [hkind, edgeIndex_eq, lane_eq_data]
    rfl
  · funext a d
    apply Fin.ext
    change ((AKLT.Gen.Packed.lane P.destinations 12
        (4*a.val + AKLT.Cert.H3.directionCode d) - 1) % 3741) % 3741 =
      (AKLT.Defs.Automaton10Data.destinationCode a d - 1) % 3741
    rw [hdest, edgeIndex_eq, lane_eq_data]
    simp [AKLT.Defs.Automaton10Data.destinationCode]
  · funext a
    change AKLT.Cert.H3.direction
        (AKLT.Gen.Packed.lane P.representatives 20 a.val % 4) =
      AKLT.Defs.Automaton10Data.direction
        (AKLT.Defs.Automaton10Data.lane AKLT.Defs.Automaton10Data.representatives 20 a.val % 4)
    rw [hrep, lane_eq_data]
    exact direction_eq_data _

#print axioms main

end AKLT.W.H3C050
