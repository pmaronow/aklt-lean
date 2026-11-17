module
public import AKLT.W.H3C034.Replay

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production CertData.H3.Bridge
open AKLT.Cert.H2

namespace AKLT.W.H3C034

set_option maxHeartbeats 2000000

/-- First-hit geometry, retaining either a surviving or a terminal final state. -/
def TraceValid (X : PairType) (d₀ : Compass) {n : Nat} (w : DirectionWord n) : Prop :=
  IsTrail kernelStart kernelIncoming w ∧ (n=0 ∨ FirstDirection w d₀) ∧
    (∀ j ≤ n, wordVertex kernelStart w j ≠ kernelCenter) ∧
    ∀ j < n, wordVertex kernelStart w j ≠ kernelTarget X

theorem initial_rep (E : Exact) (c : Nat) : PrefixRepresents E (decodeWord 0 c) initial := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [WalkRepresents, initial, prefixInitial, wordVertex, encodeWord, kernelStart]
  · intro φ
    cases φ <;> norm_num [prefixPhases, phaseInitial, phaseNumerator, initial]
  · simp [trailBaseWeight, initial]
  · simp [initial, firstVisitList]
  · simp [initial]

theorem initial_trace (X : PairType) (d₀ : Compass) (c : Nat) :
    TraceValid X d₀ (decodeWord 0 c) := by
  refine ⟨?_, Or.inl rfl, ?_, ?_⟩
  · constructor
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  · intro j hj
    have he : j=0 := by omega
    subst j
    simp [wordVertex, kernelStart, kernelCenter]
  · intro j hj; omega

theorem trace_snoc {E : Exact} {X : PairType} {d₀ : Fin 4} {n : Nat}
    {w : DirectionWord n} {s : PrefixState} (hrep : PrefixRepresents E w s)
    (hw : TraceValid X (direction d₀.val) w) (hs : s.walk.pos ≠ target X)
    (d : Fin 4) (hg : goodStep d₀.val s.walk d.val = true) :
    TraceValid X (direction d₀.val) (snoc w (direction d.val)) := by
  have hg' : ((s.walk.depth ≠ 0 ∨ d.val=d₀.val) ∧ s.walk.legal d.val=true) ∧
      advance s.walk.pos d.val ≠ kernelCenter := by
    simpa only [goodStep, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq,
      kernelCenter] using hg
  have hv : wordVertex kernelStart (snoc w (direction d.val)) (n+1) =
      advance s.walk.pos d.val := by
    rw [vertex_succ _ _ n (by omega), snoc_vertex _ _ _ n le_rfl,
      show (⟨n, by omega⟩ : Fin (n+1))=Fin.last n by rfl,
      snoc_last, advance_eq, hrep.1.2.1]
  have ht : IsTrail kernelStart kernelIncoming (snoc w (direction d.val)) := by
    by_cases hn : n=0
    · subst n
      have hd : direction d.val ≠ kernelIncoming.reverse := by
        intro hd
        apply hg'.2
        rw [advance_eq, hrep.1.2.1, vertex_zero, hd]
        rfl
      constructor
      · intro i j _; exact Fin.ext (by omega)
      · intro i _
        have he : i=Fin.last 0 := Fin.ext (by omega)
        simpa only [he, snoc_last] using hd
    · exact (goodStep_iff w s hrep.1 (by omega) hw.1 d₀.val d).1 hg |>.1
  refine ⟨ht, ?_, ?_, ?_⟩
  · right
    by_cases hn : n=0
    · subst n
      have hdeq : d.val=d₀.val := by
        have hd0 := hrep.1.1
        rcases hg'.1.1 with hnz | he
        · exact False.elim (hnz hd0)
        · exact he
      exact ⟨Fin.last 0, rfl, by rw [snoc_last, hdeq]⟩
    · exact (first_snoc_iff w _ _ (by omega)).2 (hw.2.1.resolve_left hn)
  · intro j hj
    by_cases hjn : j ≤ n
    · rw [snoc_vertex _ _ _ j hjn]
      exact hw.2.2.1 j hjn
    · have he : j=n+1 := by omega
      subst j
      rw [hv]
      exact hg'.2
  · intro j hj
    rw [snoc_vertex _ _ _ j (by omega)]
    by_cases hjn : j<n
    · exact hw.2.2.2 j hjn
    · have he : j=n := by omega
      subst j
      rw [← hrep.1.2.1, ← target_eq]
      exact hs

theorem runNode_sound_of_step (hStep : PrefixStepLeaf) (E : Exact) (hv : ExactValid E)
    (X : PairType) (d₀ : Fin 4) (n c : Nat) (s : PrefixState)
    (hrun : runNode E X d₀.val n c initial = some s) :
    PrefixRepresents E (decodeWord n c) s ∧ TraceValid X (direction d₀.val) (decodeWord n c) := by
  induction n generalizing c s with
  | zero =>
    simp only [runNode, Option.some.injEq] at hrun
    subst s
    exact ⟨initial_rep E c, initial_trace X (direction d₀.val) c⟩
  | succ n ih =>
    rw [runNode_last] at hrun
    cases hp : runNode E X d₀.val n (c/4) initial with
    | none => simp [hp] at hrun
    | some t =>
      simp only [hp, Option.bind_some, nextNode] at hrun
      have ht : t.walk.pos ≠ target X := by
        intro ht; simp [ht] at hrun
      have hg : goodStep d₀.val t.walk (c%4) = true := by
        by_contra hg; simp [ht, hg] at hrun
      have heq : transition E t (c%4) = s := by simpa [ht, hg] using hrun
      subst s
      obtain ⟨hrep, hw⟩ := ih (c/4) t hp
      let d : Fin 4 := ⟨c%4, Nat.mod_lt _ (by decide)⟩
      have htrace := trace_snoc hrep hw ht d hg
      have hstep := hStep E hv n (decodeWord n (c/4)) t hrep d
        (by simpa only [append_one_eq_snoc] using htrace.1)
      rw [append_one_eq_snoc, ← decodeWord_last] at hstep
      exact ⟨hstep, by simpa only [d, Fin.val_mk, ← decodeWord_last] using htrace⟩

theorem prefixReplay_sound_of_step (hStep : PrefixStepLeaf) : PrefixReplaySoundLeaf := by
  intro E hv X d₀ n c hn _ _ s hr
  obtain ⟨hrun, hs⟩ := replay_runNode hr
  obtain ⟨hrep, hw⟩ := runNode_sound_of_step hStep E hv X d₀ n c s hrun
  refine ⟨hrep, hw.1, hw.2.1.resolve_left (by omega), ?_⟩
  intro j hj
  refine ⟨hw.2.2.1 j hj, ?_⟩
  by_cases hjn : j<n
  · exact hw.2.2.2 j hjn
  · have he : j=n := by omega
    subst j
    rw [← hrep.1.2.1, ← target_eq]
    exact hs

end AKLT.W.H3C034

#print axioms AKLT.W.H3C034.prefixReplay_sound_of_step
