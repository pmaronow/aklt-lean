module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.W.H3C029

open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production CertData.H3.Bridge

private theorem advance_eq (x : Plane) (d : Fin 4) :
    advance x d.val = x + (direction d.val).step := by
  have hd := d.isLt
  rcases d with ⟨d, hd⟩
  interval_cases d <;> rfl

private theorem wordVertex_succ {n : Nat} (u : Plane) (w : DirectionWord n)
    (i : Fin n) :
    wordVertex u w (i.val + 1) = wordVertex u w i.val + (w i).step := by
  unfold wordVertex
  have hterms : ∀ j : Fin n,
      (if j.val < i.val + 1 then (w j).step else 0) =
        (if j.val < i.val then (w j).step else 0) +
          (if j = i then (w i).step else 0) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp
    · have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
      by_cases hlt : j.val < i.val
      · simp [hlt, show j.val < i.val + 1 by omega, hji]
      · simp [hlt, show ¬j.val < i.val + 1 by omega, hji]
  simp_rw [hterms, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  abel

private theorem wordVertex_append_prefix {n : Nat} (u : Plane) (w : DirectionWord n)
    (d : Compass) (j : Nat) (hj : j ≤ n) :
    wordVertex u (appendWords w (fun _ : Fin 1 => d)) j = wordVertex u w j := by
  induction j with
  | zero => simp [wordVertex]
  | succ j ih =>
    rw [wordVertex_succ u _ ⟨j, by omega⟩,
      wordVertex_succ u w ⟨j, by omega⟩, ih (by omega)]
    simp [appendWords, show j < n by omega]

private theorem wordVertex_append_last {n : Nat} (u : Plane) (w : DirectionWord n)
    (d : Compass) :
    wordVertex u (appendWords w (fun _ : Fin 1 => d)) (n + 1) =
      wordVertex u w n + d.step := by
  have h := wordVertex_succ u (appendWords w (fun _ : Fin 1 => d)) ⟨n, by omega⟩
  rw [wordVertex_append_prefix u w d n le_rfl] at h
  simpa [appendWords] using h

private theorem decodeWord_append (n c : Nat) :
    decodeWord (n + 1) c =
      appendWords (decodeWord n (c / 4)) (fun _ : Fin 1 => direction (c % 4)) := by
  funext i
  by_cases hi : i.val < n
  · simp only [appendWords, dite_eq_left hi, decodeWord]
    have he : n + 1 - 1 - i.val = (n - 1 - i.val) + 1 := by omega
    rw [he, pow_succ', ← Nat.div_div_eq_div_mul]
  · have he : n + 1 - 1 - i.val = 0 := by omega
    simp only [decodeWord, he, pow_zero, Nat.div_one]
    simp [appendWords, hi]

private theorem bond_comm (x y : Plane) : bond x y = bond y x := by
  unfold bond
  split_ifs with hxy hyx
  · have h : x = y := by apply Prod.ext <;> omega
    subst y
    rfl
  · rfl
  · rfl
  · exfalso
    omega

private theorem bond_eq_of_pair_eq {x y z t : Plane}
    (h : ({x, y} : Finset Plane) = {z, t}) : bond x y = bond z t := by
  have hx : x = z ∨ x = t := by
    have hx : x ∈ ({z, t} : Finset Plane) := h ▸ (by simp)
    simpa using hx
  have hy : y = z ∨ y = t := by
    have hy : y ∈ ({z, t} : Finset Plane) := h ▸ (by simp)
    simpa using hy
  have hz : z = x ∨ z = y := by
    have hz : z ∈ ({x, y} : Finset Plane) := h.symm ▸ (by simp)
    simpa using hz
  have ht : t = x ∨ t = y := by
    have ht : t ∈ ({x, y} : Finset Plane) := h.symm ▸ (by simp)
    simpa using ht
  have hp : (x = z ∧ y = t) ∨ (x = t ∧ y = z) := by grind
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact bond_comm _ _

private theorem wordBond_append_old {n : Nat} (w : DirectionWord n)
    (d : Compass) (i : Fin n) :
    wordBond kernelStart (appendWords w (fun _ : Fin 1 => d)) i.castSucc =
      wordBond kernelStart w i := by
  unfold wordBond
  simp only [Fin.val_castSucc]
  rw [wordVertex_append_prefix kernelStart w d i.val (by omega),
    wordVertex_append_prefix kernelStart w d (i.val + 1) (by omega)]

private theorem wordBond_append_last {n : Nat} (w : DirectionWord n)
    (d : Compass) :
    wordBond kernelStart (appendWords w (fun _ : Fin 1 => d)) (Fin.last n) =
      {wordVertex kernelStart w n, wordVertex kernelStart w n + d.step} := by
  simp only [wordBond, Fin.val_last, wordVertex_append_last,
    wordVertex_append_prefix kernelStart w d n le_rfl]

/-- The executable bond and center tests imply the mathematical trail condition. -/
theorem trail_append_of_goodStep {n : Nat} (w : DirectionWord n) (s : Walk)
    (hrep : WalkRepresents kernelStart 2 w s) (htrail : IsTrail kernelStart kernelIncoming w)
    (d₀ : Nat) (d : Fin 4) (hgood : goodStep d₀ s d.val = true) :
    IsTrail kernelStart kernelIncoming (appendWords w (fun _ : Fin 1 => direction d.val)) := by
  have hg := hgood
  simp only [goodStep, Bool.and_eq_true] at hg
  have hlegal : bond s.pos (advance s.pos d.val) ∉ s.used := by
    simpa [Walk.legal] using hg.1.2
  have hcenter : advance s.pos d.val ≠ kernelCenter := by
    simpa [kernelCenter] using hg.2
  have hpos := hrep.2.1
  have hused := hrep.2.2.2.2.2
  have hnew (i : Fin n) :
      wordBond kernelStart (appendWords w (fun _ : Fin 1 => direction d.val)) (Fin.last n) ≠
        wordBond kernelStart (appendWords w (fun _ : Fin 1 => direction d.val)) i.castSucc := by
    intro heq
    rw [wordBond_append_last, wordBond_append_old] at heq
    have hb := bond_eq_of_pair_eq heq
    apply hlegal
    rw [hpos, advance_eq, hused]
    apply List.mem_map.mpr
    exact ⟨i, by simp, hb.symm⟩
  constructor
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro _
        rfl
      · intro hij
        exact (hnew j hij).elim
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro hij
        exact (hnew i hij.symm).elim
      · intro hij
        rw [wordBond_append_old, wordBond_append_old] at hij
        exact congrArg Fin.castSucc (htrail.1 hij)
  · intro i hi0
    by_cases hi : i.val < n
    · simpa [appendWords, hi] using htrail.2 ⟨i.val, hi⟩ hi0
    · have hn : n = 0 := by omega
      have hstart : s.pos = kernelStart := by simpa [hn, wordVertex] using hpos
      intro hrev
      have hd : direction d.val = kernelIncoming.reverse := by
        simpa [appendWords, hi] using hrev
      apply hcenter
      rw [hstart, advance_eq, hd]
      rfl

/-- Replaying a word can be split immediately before its last direction.
The intermediate and final target tests both remain in the equation. -/
theorem replayPrefix_snoc (E : Exact) (X : PairType) (d₀ n c : Nat) (s : PrefixState) :
    replayPrefix E X d₀ (n + 1) c s =
      (replayPrefix E X d₀ n (c / 4) s).bind (fun t =>
        if goodStep d₀ t.walk (c % 4) then
          replayPrefix E X d₀ 0 c (transition E t (c % 4)) else none) := by
  induction n generalizing s with
  | zero =>
    simp only [replayPrefix, pow_zero, Nat.div_one]
    split <;> simp_all
  | succ n ih =>
    have hd : c / 4 ^ (n + 1) % 4 = c / 4 / 4 ^ n % 4 := by
      rw [Nat.div_div_eq_div_mul, pow_succ']
    simp only [replayPrefix, hd]
    split
    · rfl
    · split
      · exact ih _
      · rfl

@[simp] theorem transition_walk (E : Exact) (s : PrefixState) (d : Nat) :
    (transition E s d).walk = s.walk.step d := by
  unfold transition
  dsimp only
  split
  · rfl
  · split <;> rfl

/-- The empty replay state represents the empty mathematical word. -/
theorem initial_represents (E : Exact) (c : Nat) :
    PrefixRepresents E (decodeWord 0 c) initial := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [WalkRepresents, initial, prefixInitial, wordVertex, encodeWord, kernelStart]
  · intro φ
    cases φ <;> simp [prefixPhases, initial, phaseNumerator, phaseInitial]
  · simp [trailBaseWeight, initial]
  · simp [initial, firstVisitList]
  · simp [initial]

/-- The full replay induction uses only the single-step representation leaf.
The path invariant allows an empty prefix and hence states its first direction
conditionally; all vertices, including the final one, avoid the target. -/
theorem replay_sound_of_prefixStep (hstep : PrefixStepLeaf)
    (E : Exact) (hE : ExactValid E) (X : PairType) (d₀ : Fin 4) (n c : Nat)
    (hc : c < 4 ^ n) (s : PrefixState)
    (hs : replayPrefix E X d₀.val n c initial = some s) :
    PrefixRepresents E (decodeWord n c) s ∧
    IsTrail kernelStart kernelIncoming (decodeWord n c) ∧
    (0 < n → FirstDirection (decodeWord n c) (direction d₀.val)) ∧
    ∀ j ≤ n, wordVertex kernelStart (decodeWord n c) j ≠ kernelCenter ∧
      wordVertex kernelStart (decodeWord n c) j ≠ kernelTarget X := by
  induction n generalizing c s with
  | zero =>
    have hstart : initial.walk.pos ≠ target X := by cases X <;> decide
    have hstate : s = initial := by simpa [replayPrefix, hstart] using hs.symm
    subst s
    refine ⟨initial_represents E c, ?_, ?_, ?_⟩
    · constructor
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
    · omega
    · intro j hj
      have hj0 : j = 0 := by omega
      subst j
      cases X <;> simp [wordVertex, kernelStart, kernelCenter, kernelTarget]
  | succ n ih =>
    rw [replayPrefix_snoc] at hs
    obtain ⟨t, ht, hlast⟩ := Option.bind_eq_some_iff.mp hs
    split at hlast
    next hgood =>
      simp only [replayPrefix] at hlast
      split at hlast
      next htarget => cases hlast
      next htarget =>
        have hstate : transition E t (c % 4) = s := Option.some.inj hlast
        subst s
        have hparent : c / 4 < 4 ^ n := by
          apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mpr
          simpa [pow_succ] using hc
        obtain ⟨hrep, htrail, hfirst, havoid⟩ := ih (c / 4) hparent t ht
        let d : Fin 4 := ⟨c % 4, Nat.mod_lt _ (by decide)⟩
        have htrail' := trail_append_of_goodStep (decodeWord n (c / 4)) t.walk
          hrep.1 htrail d₀.val d hgood
        rw [decodeWord_append]
        refine ⟨hstep E hE n _ t hrep d htrail', htrail', ?_, ?_⟩
        · intro _
          by_cases hn : n = 0
          · subst n
            have hdepth : t.walk.depth = 0 := hrep.1.1
            have hg := hgood
            simp only [goodStep, Bool.and_eq_true] at hg
            have hd : c % 4 = d₀.val := by simpa [hdepth] using hg.1.1
            exact ⟨⟨0, by omega⟩, rfl, by simp [appendWords, hd]⟩
          · obtain ⟨i, hi0, hi⟩ := hfirst (by omega)
            refine ⟨i.castSucc, hi0, ?_⟩
            simpa [appendWords, i.isLt] using hi
        · intro j hj
          by_cases hjn : j ≤ n
          · rw [wordVertex_append_prefix kernelStart _ _ j hjn]
            exact havoid j hjn
          · have hjlast : j = n + 1 := by omega
            subst j
            have hendpoint :
                wordVertex kernelStart
                  (appendWords (decodeWord n (c / 4)) (fun _ : Fin 1 => direction (c % 4)))
                  (n + 1) = advance t.walk.pos d.val := by
              rw [wordVertex_append_last, advance_eq, hrep.1.2.1]
            rw [hendpoint]
            constructor
            · have hg := hgood
              simp only [goodStep, Bool.and_eq_true] at hg
              simpa [kernelCenter] using hg.2
            · cases X <;> simpa [transition_walk, Walk.step, d, target, kernelTarget] using htarget
    next hgood => cases hlast

#print axioms trail_append_of_goodStep
#print axioms replayPrefix_snoc
#print axioms transition_walk
#print axioms initial_represents
#print axioms replay_sound_of_prefixStep

end AKLT.W.H3C029
