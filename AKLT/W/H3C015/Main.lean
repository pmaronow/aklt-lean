module
public import AKLT.W.H3C015.Counting
public import AKLT.W.H3C001.Main
public import AKLT.W.H3C002.Main
public import AKLT.W.H3C005.Main
public import AKLT.W.H3C006.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

open scoped BigOperators

namespace AKLT.W.H3C015

open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production

private def rawCodes10 : Finset (Fin (4 ^ 10)) :=
  Finset.univ.filter fun c => RawWindow (decodeWord 10 c.val)

private def rawCodeEquiv : MemoryWindow 10 ≃ (↑rawCodes10 : Type _) where
  toFun w :=
    ⟨⟨encodeWord w.val, (AKLT.W.H3C002.main 10 w.val).1⟩, by
      simp only [rawCodes10, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(AKLT.W.H3C002.main 10 w.val).2]
      exact w.property⟩
  invFun c :=
    ⟨decodeWord 10 c.val.val, (Finset.mem_filter.mp c.property).2⟩
  left_inv w := Subtype.ext (AKLT.W.H3C002.main 10 w.val).2
  right_inv c := Subtype.ext (Fin.ext (AKLT.W.H3C001.main 10 c.val.val c.val.isLt))

private theorem memoryWindow_card_eq_rawCodes :
    Fintype.card (MemoryWindow 10) = rawCodes10.card := by
  calc
    Fintype.card (MemoryWindow 10) = Fintype.card (↑rawCodes10 : Type _) :=
      Fintype.card_congr rawCodeEquiv
    _ = rawCodes10.card := Fintype.card_coe rawCodes10

private theorem replayRaw_isSome_iff_raw (c : Nat) (hc : c < 4 ^ 10) :
    (replayRaw 10 c rawInitial).isSome = true ↔ RawWindow (decodeWord 10 c) := by
  constructor
  · intro h
    cases hr : replayRaw 10 c rawInitial with
    | none => simp [hr] at h
    | some s => exact (AKLT.W.H3C005.main 10 c (by decide) hc s hr).1
  · exact AKLT.W.H3C006.main 10 c (by decide) hc

/-- The production trie counts exactly the mathematical memory-ten windows. -/
theorem main : CertData.H3.Bridge.RawTrieCountLeaf := by
  intro G
  rw [rawBatch_count_replays, memoryWindow_card_eq_rawCodes]
  rw [rawCodes10, Finset.card_filter, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro c _
  simp only [replayRaw_isSome_iff_raw c.val c.isLt]

#print axioms main

end AKLT.W.H3C015
