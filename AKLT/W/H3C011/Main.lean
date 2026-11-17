module
public import AKLT.W.H3C011.Traversal
public import AKLT.W.H3C002.Main
public import AKLT.W.H3C005.Main
public import AKLT.W.H3C009.Main
public import AKLT.W.H3C010.Main
public import AKLT.W.H3C013.Main
public import CertData.H3.Kernel.Soundness

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C011

open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production CertData.H3.Bridge

private theorem representativeBatch_check (G : Graph) (start count i : Nat)
    (hi : i < count) (h : representativeBatch G start count = true) :
    representativeCheck G (start + i) = true := by
  exact List.all_eq_true.mp h i (List.mem_range.mpr hi)

/-- The representative check supplies both a raw representative and its own
class index, once successful replay is known to represent a raw word. -/
theorem representatives_of_replaySound (hsound : RawReplaySoundLeaf)
    (G : Graph) (hbatch : representativeBatch G 0 3741 = true) :
    ∀ a : Fin 3741, RawWindow (G.quotient.representative a) ∧
      G.quotient.project (G.quotient.representative a) = a := by
  intro a
  have hcheck : representativeCheck G a.val = true := by
    simpa only [Nat.zero_add] using representativeBatch_check G 0 3741 a.val a.isLt hbatch
  have hbound := AKLT.W.H3C013.main G hbatch a
  have hrest := (Bool.and_eq_true_iff.mp hcheck).2
  cases hr : replayRaw 10 (G.representative a.val) rawInitial with
  | none => simp [hr] at hrest
  | some s =>
      have hself : G.classAt s.code = a.val := by simpa only [hr, beq_iff_eq] using hrest
      rcases hsound 10 (G.representative a.val) (by decide) hbound s hr with
        ⟨hraw, hdepth, hpos, hincoming, hcode, hdeparted, hused⟩
      have hencode : encodeWord (decodeWord 10 (G.representative a.val)) < 1048576 := by
        simpa only [show (4 : Nat) ^ 10 = 1048576 from rfl] using
          (AKLT.W.H3C002.main 10 (decodeWord 10 (G.representative a.val))).1
      rw [Nat.mod_eq_of_lt hencode] at hcode
      refine ⟨hraw, ?_⟩
      change finState (G.classAt (encodeWord (decodeWord 10 (G.representative a.val)))) = a
      rw [← hcode, hself]
      apply Fin.ext
      exact Nat.mod_eq_of_lt a.isLt

/-- Coverage chooses a code with a genuine class. The symbolic traversal lemma
then supplies its checked row, to which the two soundness leaves apply. -/
theorem rows_of_leaves (hrow : RawRowSoundLeaf) (hcoverage : RawTrieCoverageLeaf)
    (hsound : RawReplaySoundLeaf) (G : Graph) (hspan : SpanRepresents G)
    (hbatch : (rawBatch G 0 4096).ok = true) :
    ∀ w : DirectionWord 10, RawWindow w → CorrectAt G.quotient w := by
  intro w hw
  have hencode := AKLT.W.H3C002.main 10 w
  let c : Fin (4 ^ 10) := ⟨encodeWord w, hencode.1⟩
  have hc : c.val < 1048576 := by
    simpa only [show (4 : Nat) ^ 10 = 1048576 from rfl] using c.isLt
  have hclass : G.classAt c.val < 3741 :=
    (hcoverage G hspan hbatch c).mpr (by simpa only [c, hencode.2] using hw)
  obtain ⟨s, hreplay, hcheck⟩ := rawBatch_row G hspan hbatch c.val hc hclass
  have hs := hsound 10 c.val (by decide) c.isLt s hreplay
  have hr := hrow G c.val hc s hs.1 hs.2 hcheck
  simpa only [c, hencode.2] using hr

/-- Successful trie and representative checks certify the raw-to-quotient map. -/
theorem main : CertData.H3.Bridge.RawTrieProjectionLeaf := by
  intro G hspan hbatch hrepresentatives
  exact quotient_assembly 10 3741 G.quotient
    (representatives_of_replaySound AKLT.W.H3C005.main G hrepresentatives)
    (rows_of_leaves AKLT.W.H3C009.main AKLT.W.H3C010.main AKLT.W.H3C005.main
      G hspan hbatch)

#print axioms representatives_of_replaySound
#print axioms rows_of_leaves
#print axioms main

end AKLT.W.H3C011
