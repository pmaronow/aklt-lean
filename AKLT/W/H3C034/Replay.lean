module
public import AKLT.W.H3C034.Semantics

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production CertData.H3.Bridge
open AKLT.Cert.H2

namespace AKLT.W.H3C034

set_option maxHeartbeats 2000000

theorem direction_inj (a b : Fin 4) (h : direction a.val = direction b.val) : a=b := by
  fin_cases a <;> fin_cases b <;> simp_all [direction]

theorem prefixReplay_complete_of_sound (hSound : PrefixReplaySoundLeaf) : PrefixReplayCompleteLeaf := by
  intro E hv X d₀ n c hn hn12 hc hw
  induction n generalizing c with
  | zero => omega
  | succ m ih =>
    by_cases hm : m=0
    · subst m
      have hc4 : c<4 := by simpa using hc
      let d : Fin 4 := ⟨c, hc4⟩
      have hd : d=d₀ := by
        apply direction_inj
        obtain ⟨i, hi, hdir⟩ := hw.2.1
        fin_cases i
        simpa [decodeWord, Nat.mod_eq_of_lt hc4, d] using hdir
      have hvertex : wordVertex kernelStart (decodeWord 1 c) 1 = advance prefixInitial.pos c := by
        rw [advance_eq _ d]
        simp [wordVertex, decodeWord, Nat.mod_eq_of_lt hc4, prefixInitial, kernelStart, d]
      have hgood : goodStep d₀.val prefixInitial c = true := by
        have hcen : advance prefixInitial.pos c ≠ (0,0) := by
          rw [← hvertex]
          exact (hw.2.2 1 le_rfl).1
        have hdeq : c=d₀.val := congrArg Fin.val hd
        have hcen' : advance (-1,0) d₀.val ≠ (0,0) := by
          simpa only [prefixInitial, hdeq] using hcen
        simp [goodStep, prefixInitial, Walk.legal, hdeq, hcen']
      have ht : (transition E initial c).walk.pos ≠ target X := by
        rw [transition_walk]
        change advance prefixInitial.pos c ≠ target X
        rw [← hvertex, target_eq]
        exact (hw.2.2 1 le_rfl).2
      have hr : runNode E X d₀.val 1 c initial = some (transition E initial c) := by
        have hinit : prefixInitial.pos ≠ target X := by cases X <;> decide
        simp [runNode, nextNode, initial, Nat.mod_eq_of_lt hc4, hgood, hinit]
      rw [replayPrefix_eq_runNode, hr]
      simp [ht]
    · have hm1 : 1 ≤ m := by omega
      have hcm : c/4 < 4^m := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0<4)).2
        simpa [pow_succ] using hc
      have hp : SurvivingPrefix X (direction d₀.val) (decodeWord m (c/4)) := by
        rw [decodeWord_last] at hw
        refine ⟨?_, (first_snoc_iff _ _ _ hm1).1 hw.2.1, ?_⟩
        · simpa using trail_initWord kernelStart kernelIncoming _ hw.1
        · intro j hj
          rw [← snoc_vertex kernelStart (decodeWord m (c/4)) (direction (c%4)) j hj]
          exact hw.2.2 j (by omega)
      have hcp := ih (c/4) hm1 (by omega) hcm hp
      cases hr : replayPrefix E X d₀.val m (c/4) initial with
      | none => simp [hr] at hcp
      | some t =>
        have hrep := (hSound E hv X d₀ m (c/4) hm1 (by omega) hcm t hr).1
        obtain ⟨hrun, ht⟩ := replay_runNode hr
        let d : Fin 4 := ⟨c%4, Nat.mod_lt _ (by decide)⟩
        have hgood : goodStep d₀.val t.walk (c%4) = true := by
          apply (goodStep_iff _ t hrep.1 hm1 hp.1 d₀.val d).2
          rw [← decodeWord_last]
          exact ⟨hw.1, (hw.2.2 (m+1) le_rfl).1⟩
        have hvtx : (transition E t (c%4)).walk.pos = wordVertex kernelStart (decodeWord (m+1) c) (m+1) := by
          rw [transition_walk]
          change advance t.walk.pos d.val = _
          rw [hrep.1.2.1, advance_eq, decodeWord_last,
            vertex_succ _ _ m (by omega), snoc_vertex _ _ _ m le_rfl,
            show (⟨m, by omega⟩ : Fin (m+1))=Fin.last m by rfl, snoc_last]
        have hs : (transition E t (c%4)).walk.pos ≠ target X := by
          rw [hvtx, target_eq]
          exact (hw.2.2 (m+1) le_rfl).2
        have hrfull : runNode E X d₀.val (m+1) c initial = some (transition E t (c%4)) := by
          rw [runNode_last, hrun]
          simp only [Option.bind_some, nextNode, ite_eq_right ht, ite_eq_left hgood]
        rw [replayPrefix_eq_runNode, hrfull]
        simp [hs]

end AKLT.W.H3C034

#print axioms AKLT.W.H3C034.prefixReplay_complete_of_sound
