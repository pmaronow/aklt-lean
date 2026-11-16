import AKLT.W.H3C034.Words

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production CertData.H3.Bridge
open AKLT.Cert.H2

namespace AKLT.W.H3C034

set_option maxHeartbeats 3000000

theorem target_eq (X : PairType) : target X = kernelTarget X := by cases X <;> rfl

theorem runNode_replay {E : Exact} {X : PairType} {d₀ n c : Nat} {s : PrefixState}
    (hrun : runNode E X d₀ n c initial = some s) (hs : s.walk.pos ≠ target X) :
    replayPrefix E X d₀ n c initial = some s := by
  rw [replayPrefix_eq_runNode, hrun]
  simp [hs]

theorem replay_runNode {E : Exact} {X : PairType} {d₀ n c : Nat} {s : PrefixState}
    (hrun : replayPrefix E X d₀ n c initial = some s) :
    runNode E X d₀ n c initial = some s ∧ s.walk.pos ≠ target X := by
  rw [replayPrefix_eq_runNode] at hrun
  cases h : runNode E X d₀ n c initial with
  | none => simp [h] at hrun
  | some t =>
    simp only [h, Option.bind_some] at hrun
    by_cases ht : t.walk.pos = target X
    · simp [ht] at hrun
    · simp only [ite_eq_right ht, Option.some.injEq] at hrun
      subst s
      exact ⟨rfl, ht⟩

theorem node_surviving (hSound : PrefixReplaySoundLeaf) (E : Exact) (hv : ExactValid E)
    (X : PairType) (d₀ : Fin 4) (n c : Nat) (hn : 1 ≤ n) (hn12 : n ≤ 12)
    (hc : c < 4^n) (s : PrefixState) (hrun : runNode E X d₀.val n c initial = some s)
    (hs : s.walk.pos ≠ target X) :
    PrefixRepresents E (decodeWord n c) s ∧ SurvivingPrefix X (direction d₀.val) (decodeWord n c) :=
  hSound E hv X d₀ n c hn hn12 hc s (runNode_replay hrun hs)

theorem node_closed (hSound : PrefixReplaySoundLeaf) (hStep : PrefixStepLeaf)
    (E : Exact) (hv : ExactValid E) (X : PairType) (d₀ : Fin 4)
    (n c : Nat) (hn : 2 ≤ n) (hn12 : n ≤ 12) (hc : c < 4^n)
    (s : PrefixState) (hrun : runNode E X d₀.val n c initial = some s)
    (hs : s.walk.pos = target X) :
    PrefixRepresents E (decodeWord n c) s ∧
      ClosedTrail X (decodeWord n c) ∧ FirstDirection (decodeWord n c) (direction d₀.val) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [runNode_last] at hrun
  cases hp : runNode E X d₀.val m (c/4) initial with
  | none => simp [hp] at hrun
  | some t =>
    simp only [hp, Option.bind_some, nextNode] at hrun
    have ht : t.walk.pos ≠ target X := by
      intro ht
      simp [ht] at hrun
    have hg : goodStep d₀.val t.walk (c%4) = true := by
      by_contra hg
      simp [ht, hg] at hrun
    have heq : transition E t (c%4) = s := by simpa [ht, hg] using hrun
    subst s
    ·
      have hcm : c/4 < 4^m := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0<4)).2
        simpa [pow_succ] using hc
      obtain ⟨hrep, hsurv⟩ := node_surviving hSound E hv X d₀ m (c/4)
        (by omega) (by omega) hcm t hp ht
      let d : Fin 4 := ⟨c%4, Nat.mod_lt _ (by decide)⟩
      have hgood := (goodStep_iff _ t hrep.1 (by omega) hsurv.1 d₀.val d).1 hg
      have hstep := hStep E hv m (decodeWord m (c/4)) t hrep d
        (by simpa only [append_one_eq_snoc] using hgood.1)
      rw [append_one_eq_snoc, ← decodeWord_last] at hstep
      refine ⟨hstep, ?_, ?_⟩
      · rw [decodeWord_last]
        refine ⟨hgood.1, ?_, ?_, ?_⟩
        · rw [← decodeWord_last, ← hstep.1.2.1, ← target_eq]
          exact hs
        · intro j hj
          by_cases hjm : j ≤ m
          · rw [snoc_vertex _ _ _ j hjm]
            exact (hsurv.2.2 j hjm).1
          · have hjlast : j=m+1 := by omega
            subst j
            exact hgood.2
        · intro j hj
          rw [snoc_vertex _ _ _ j (by omega)]
          exact (hsurv.2.2 j (by omega)).2
      · rw [decodeWord_last, first_snoc_iff _ _ _ (by omega)]
        exact hsurv.2.1

theorem closed_parent {X : PairType} {d₀ : Compass} {m c : Nat} (hm : 1 ≤ m)
    (hw : ClosedTrail X (decodeWord (m+1) c))
    (hd : FirstDirection (decodeWord (m+1) c) d₀) :
    SurvivingPrefix X d₀ (decodeWord m (c/4)) := by
  rw [decodeWord_last] at hw hd
  refine ⟨?_, (first_snoc_iff _ _ _ hm).1 hd, ?_⟩
  · simpa using trail_initWord kernelStart kernelIncoming _ hw.1
  · intro j hj
    have he := snoc_vertex kernelStart (decodeWord m (c/4)) (direction (c%4)) j hj
    exact ⟨by rw [← he]; exact hw.2.2.1 j (by omega),
      by rw [← he]; exact hw.2.2.2 j (by omega)⟩

theorem node_closed_complete (hSound : PrefixReplaySoundLeaf) (hComplete : PrefixReplayCompleteLeaf)
    (E : Exact) (hv : ExactValid E) (X : PairType) (d₀ : Fin 4)
    (n c : Nat) (hn : 2 ≤ n) (hn12 : n ≤ 12) (hc : c < 4^n)
    (hw : ClosedTrail X (decodeWord n c))
    (hd : FirstDirection (decodeWord n c) (direction d₀.val)) :
    ∃ s, runNode E X d₀.val n c initial = some s ∧ s.walk.pos = target X := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hcm : c/4 < 4^m := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0<4)).2
    simpa [pow_succ] using hc
  have hp := closed_parent (by omega : 1 ≤ m) hw hd
  have hcpl := hComplete E hv X d₀ m (c/4) (by omega) (by omega) hcm hp
  cases hr : replayPrefix E X d₀.val m (c/4) initial with
  | none => simp [hr] at hcpl
  | some t =>
    have hrep := (hSound E hv X d₀ m (c/4) (by omega) (by omega) hcm t hr).1
    obtain ⟨hrun, ht⟩ := replay_runNode hr
    let d : Fin 4 := ⟨c%4, Nat.mod_lt _ (by decide)⟩
    have hgood : goodStep d₀.val t.walk d.val = true := by
      apply (goodStep_iff _ t hrep.1 (by omega) hp.1 d₀.val d).2
      rw [← decodeWord_last]
      exact ⟨hw.1, hw.2.2.1 (m+1) le_rfl⟩
    refine ⟨transition E t d.val, ?_, ?_⟩
    · rw [runNode_last, hrun]
      dsimp only [d] at hgood ⊢
      simp only [Option.bind_some, nextNode, ite_eq_right ht, ite_eq_left hgood]
    · rw [transition_walk]
      change advance t.walk.pos d.val = target X
      rw [hrep.1.2.1, advance_eq]
      have he := vertex_succ kernelStart (snoc (decodeWord m (c/4)) (direction d.val)) m (by omega)
      rw [snoc_vertex _ _ _ m le_rfl, show (⟨m, by omega⟩ : Fin (m+1))=Fin.last m by rfl,
        snoc_last, ← decodeWord_last] at he
      rw [← he, target_eq]
      exact hw.2.1

theorem node_hit_value (hSound : PrefixReplaySoundLeaf) (hComplete : PrefixReplayCompleteLeaf)
    (hStep : PrefixStepLeaf) (hShort : ShortValueLeaf)
    (E : Exact) (hv : ExactValid E) (X : PairType) (d₀ : Fin 4)
    (n c : Nat) (hn : 2 ≤ n) (hn12 : n ≤ 12) (hc : c < 4^n) :
    optionValue (hitValue E X) (runNode E X d₀.val n c initial) =
      if ClosedTrail X (decodeWord n c) ∧ FirstDirection (decodeWord n c) (direction d₀.val)
      then closedContribution (decodeWord n c) else 0 := by
  classical
  cases hr : runNode E X d₀.val n c initial with
  | none =>
    have hnot : ¬(ClosedTrail X (decodeWord n c) ∧
        FirstDirection (decodeWord n c) (direction d₀.val)) := by
      rintro ⟨hw, hd⟩
      obtain ⟨s, hs, _⟩ := node_closed_complete hSound hComplete E hv X d₀ n c hn hn12 hc hw hd
      rw [hr] at hs
      contradiction
    simp [optionValue, hnot]
  | some s =>
    by_cases hs : s.walk.pos = target X
    · obtain ⟨hrep, hw, hd⟩ := node_closed hSound hStep E hv X d₀ n c hn hn12 hc s hr hs
      simpa [optionValue, hitValue, hs, hw, hd] using hShort E hv n hn12 (decodeWord n c) s hrep
    · obtain ⟨_, hsurv⟩ := node_surviving hSound E hv X d₀ n c (by omega) hn12 hc s hr hs
      have hnot : ¬ClosedTrail X (decodeWord n c) := by
        intro hw
        exact (hsurv.2.2 n le_rfl).2 hw.2.1
      simp [optionValue, hitValue, hs, hnot]

theorem leaf_value (G : Graph) (T lookup : Tables) (E : Exact) (hbinding : EndpointBinding T lookup)
    (w : DirectionWord 12) (s : PrefixState) (hrep : PrefixRepresents E w s)
    (hok : (leafValue G lookup s).ok = true) :
    resultValue E (leafValue G lookup s) =
      ∑ φ : Phase, prefixPhases w φ *
        T.data.potential φ (G.quotient.project (lastWindowWord 10 w)) (wordVertex kernelStart w 12) := by
  have hc : G.classAt s.walk.code < 3741 := by
    have hh : G.classAt s.walk.code < 3741 ∧ endpointInside s.walk.pos = true := by
      simpa only [leafValue, Bool.and_eq_true, decide_eq_true_eq] using hok
    exact hh.1
  have hpos := hrep.1.2.1
  have hcode := hrep.1.2.2.2.1
  have hinside := AKLT.W.H3C019.main w
  let a : Fin 3741 := ⟨G.classAt s.walk.code, hc⟩
  have hproj : G.quotient.project (lastWindowWord 10 w) = a := by
    apply Fin.ext
    change G.classAt (encodeWord (lastWindowWord 10 w)) % 3741 = G.classAt s.walk.code
    rw [lastWindowCode 12 (by decide) w, ← hcode, Nat.mod_eq_of_lt hc]
  have hb (p : Fin 4) : endpointValue lookup p.val a.val s.walk.pos =
      T.data.extended (phase p.val) a (wordVertex kernelStart w 12) := by
    rw [hpos]
    exact hbinding p a _ hinside
  rw [hproj]
  have hu : (Finset.univ : Finset Phase) = {.A,.B,.C,.D} := rfl
  simp only [hu, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq,
    or_self, not_false_eq_true, Finset.sum_singleton, hrep.2.1, StationaryData.potential,
    phaseNumerator, certificateValueScale]
  simp only [resultValue, leafValue, Nat.cast_zero, zero_div, zero_add, Nat.cast_add, Nat.cast_mul]
  change _ = _
  rw [hb ⟨0, by decide⟩, hb ⟨1, by decide⟩, hb ⟨2, by decide⟩, hb ⟨3, by decide⟩]
  simp only [phase]
  dsimp only [a]
  push_cast
  ring

end AKLT.W.H3C034
