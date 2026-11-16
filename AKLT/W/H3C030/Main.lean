import CertData.H3.Bridge.Interface

namespace AKLT.W.H3C030

open AKLT.Cert.H3.Production
open AKLT.Cert.H3
open CertData.H3.Bridge
open AKLT.Defs

def suffixWord {total : Nat} (w : DirectionWord total) (k m : Nat)
    (hlen : k + m = total) : DirectionWord m :=
  fun i => w ⟨k + i.val, by omega⟩

def usedBonds {n : Nat} (w : DirectionWord n) (k : Nat) : List Bond :=
  (List.range k).reverse.map fun j =>
    bond (wordVertex kernelStart w j) (wordVertex kernelStart w (j + 1))

def WalkPrefix {n : Nat} (w : DirectionWord n) (k : Nat) (s : PrefixState) : Prop :=
  s.walk.depth = k ∧ s.walk.pos = wordVertex kernelStart w k ∧
    s.walk.used = usedBonds w k

/-- The local checks made by the deterministic prefix parser. -/
def ReplayTrace (E : Exact) (X : PairType) (d₀ : Nat) : Nat → Nat → PrefixState → Prop
  | 0, _, s => s.walk.pos ≠ target X
  | n + 1, c, s =>
      s.walk.pos ≠ target X ∧
      goodStep d₀ s.walk (c / 4 ^ n % 4) = true ∧
      ReplayTrace E X d₀ n c (transition E s (c / 4 ^ n % 4))

theorem wordVertex_succ {n : Nat} (w : DirectionWord n) {k : Nat} (hk : k < n) :
    wordVertex kernelStart w (k + 1) =
      wordVertex kernelStart w k + (w ⟨k, hk⟩).step := by
  unfold wordVertex
  have hterm (i : Fin n) :
      (if i.val < k + 1 then (w i).step else 0) =
        (if i.val < k then (w i).step else 0) +
          (if i.val = k then (w i).step else 0) := by
    by_cases hi : i.val < k
    · have hneq : i.val ≠ k := by omega
      simp [hi, hneq, Nat.lt_succ_of_lt hi]
    · by_cases heq : i.val = k
      · have hival : i = ⟨k, hk⟩ := Fin.ext heq
        subst i
        simp
      · have hge : k + 1 ≤ i.val := by omega
        simp [hi, heq, Nat.not_lt_of_ge hge]
  rw [show (∑ i : Fin n, (if i.val < k + 1 then (w i).step else 0) : Plane) =
      ∑ i : Fin n, ((if i.val < k then (w i).step else 0) +
        (if i.val = k then (w i).step else 0)) by
        apply Finset.sum_congr rfl
        intro i _
        exact hterm i]
  rw [Finset.sum_add_distrib]
  have hsingle :
      (∑ i : Fin n, if i.val = k then (w i).step else 0 : Plane) =
        (w ⟨k, hk⟩).step := by
    calc
      (∑ i : Fin n, if i.val = k then (w i).step else 0 : Plane) =
          ∑ i : Fin n, if i = ⟨k, hk⟩ then (w ⟨k, hk⟩).step else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases heq : i.val = k
            · have hi : i = ⟨k, hk⟩ := Fin.ext heq
              subst i
              simp
            · have hi : i ≠ ⟨k, hk⟩ := by
                intro h
                exact heq (congrArg Fin.val h)
              simp [heq, hi]
      _ = (w ⟨k, hk⟩).step := by simp
  rw [hsingle]
  simp [add_assoc]

theorem usedBonds_succ {n : Nat} (w : DirectionWord n) (k : Nat) :
    usedBonds w (k + 1) =
      bond (wordVertex kernelStart w k) (wordVertex kernelStart w (k + 1)) :: usedBonds w k := by
  simp [usedBonds, List.range_succ, List.reverse_append]

theorem transition_walk (E : Exact) (s : PrefixState) (d : Nat) :
    (transition E s d).walk = s.walk.step d := by
  simp only [transition]
  split_ifs <;> rfl

theorem walkPrefix_transition {n : Nat} (w : DirectionWord n) (k : Nat) (hk : k < n)
    (E : Exact) (s : PrefixState) (hs : WalkPrefix w k s) :
    WalkPrefix w (k + 1) (transition E s (directionCode (w ⟨k, hk⟩))) := by
  rcases hs with ⟨hdepth, hpos, hused⟩
  have hwalk := transition_walk E s (directionCode (w ⟨k, hk⟩))
  refine ⟨?_, ?_, ?_⟩
  · rw [hwalk, Walk.step]
    simp [hdepth]
  · rw [hwalk, Walk.step, hpos]
    have hadvance : advance (wordVertex kernelStart w k)
        (directionCode (w ⟨k, hk⟩)) =
          wordVertex kernelStart w k + (w ⟨k, hk⟩).step := by
      cases w ⟨k, hk⟩ <;> rfl
    rw [hadvance, wordVertex_succ w hk]
  · rw [hwalk]
    simp only [Walk.step]
    rw [usedBonds_succ]
    rw [hpos, hused]
    have hadvance : advance (wordVertex kernelStart w k)
        (directionCode (w ⟨k, hk⟩)) =
          wordVertex kernelStart w k + (w ⟨k, hk⟩).step := by
      cases w ⟨k, hk⟩ <;> rfl
    rw [hadvance, wordVertex_succ w hk]

theorem walkPrefix_initial {n : Nat} (w : DirectionWord n) : WalkPrefix w 0 initial := by
  simp [WalkPrefix, initial, prefixInitial, usedBonds, wordVertex, kernelStart]

theorem bond_finset_eq {a b c d : Point} (h : bond a b = bond c d) :
    ({a, b} : Finset Point) = {c, d} := by
  unfold bond at h
  split_ifs at h <;> cases h <;> ext x <;> simp <;> tauto

theorem freshBond {n : Nat} (w : DirectionWord n) {k : Nat} (hk : k < n)
    (htrail : IsTrail kernelStart kernelIncoming w) :
    bond (wordVertex kernelStart w k) (wordVertex kernelStart w (k + 1)) ∉ usedBonds w k := by
  intro hmem
  unfold usedBonds at hmem
  rcases List.mem_map.mp hmem with ⟨j, hj, he⟩
  have hjrange : j ∈ List.range k := by simpa using hj
  have hjk : j < k := List.mem_range.mp hjrange
  have hidx :
      (⟨j, by omega⟩ : Fin n) = (⟨k, hk⟩ : Fin n) := by
    apply htrail.1
    apply bond_finset_eq
    simpa using he
  have hval : j = k := by simpa using congrArg Fin.val hidx
  omega

theorem walkLegal {n : Nat} (w : DirectionWord n) {k : Nat} (hk : k < n)
    (s : PrefixState) (hp : WalkPrefix w k s)
    (htrail : IsTrail kernelStart kernelIncoming w) :
    (s.walk.legal (directionCode (w ⟨k, hk⟩))) = true := by
  rcases hp with ⟨_, hpos, hused⟩
  have hadvance : advance (wordVertex kernelStart w k)
      (directionCode (w ⟨k, hk⟩)) =
        wordVertex kernelStart w k + (w ⟨k, hk⟩).step := by
    cases w ⟨k, hk⟩ <;> rfl
  have hfresh := freshBond w hk htrail
  have hcontains : (usedBonds w k).contains
      (bond (wordVertex kernelStart w k) (wordVertex kernelStart w (k + 1))) = false := by
    simpa using hfresh
  rw [Walk.legal, hpos, hadvance, ← wordVertex_succ w hk, hused]
  simpa using hcontains

theorem directionCode_direction {c : Nat} (hc : c < 4) :
    directionCode (direction c) = c := by
  interval_cases c <;> rfl

theorem replayTrace_from_prefix (E : Exact) (X : PairType) (d₀ : Nat) :
    d₀ < 4 →
    ∀ (total k m : Nat) (w : DirectionWord total) (hlen : k + m = total)
      (c : Nat) (s : PrefixState),
      decodeWord m c = suffixWord w k m hlen →
      WalkPrefix w k s →
      IsTrail kernelStart kernelIncoming w → FirstDirection w (direction d₀) →
      (∀ j ≤ total, wordVertex kernelStart w j ≠ kernelCentre ∧
        wordVertex kernelStart w j ≠ target X) →
      ReplayTrace E X d₀ m c s := by
  intro hd₀ total k m
  induction m generalizing total k with
  | zero =>
      intro w hlen c s hdecode hwalk htrail hfirst havoid
      have hk : k = total := by omega
      have hpos := hwalk.2.1
      have ht := (havoid k (by omega)).2
      simpa [ReplayTrace, hpos] using ht
  | succ m ih =>
      intro w hlen c s hdecode hwalk htrail hfirst havoid
      have hk : k < total := by omega
      let i : Fin total := ⟨k, hk⟩
      let q := c / 4 ^ m % 4
      have hhead : direction q = w i := by
        have hh := congrFun hdecode (⟨0, by omega⟩ : Fin (m + 1))
        simpa [q, decodeWord, suffixWord, i] using hh
      have hq : q = directionCode (w i) := by
        have h := congrArg directionCode hhead
        rw [directionCode_direction (Nat.mod_lt _ (by omega))] at h
        exact h
      have hdepth := hwalk.1
      have hpos := hwalk.2.1
      have hused := hwalk.2.2
      have hnotTarget : s.walk.pos ≠ target X := by
        have ht := (havoid k (by omega)).2
        simpa [hpos] using ht
      have hstepGeom := wordVertex_succ w hk
      have hadvance : advance (wordVertex kernelStart w k) (directionCode (w i)) =
          wordVertex kernelStart w k + (w i).step := by
        cases w i <;> rfl
      have hnotCentre : advance s.walk.pos q ≠ kernelCentre := by
        have hc := (havoid (k + 1) (by omega)).1
        rw [hpos, hq, hadvance, ← hstepGeom]
        exact hc
      have hlegal := walkLegal w hk s ⟨hdepth, hpos, hused⟩ htrail
      have hfirstTest : (s.walk.depth != 0 || q == d₀) = true := by
        by_cases hk0 : k = 0
        ·
          rcases hfirst with ⟨j, hj, hjdir⟩
          have hj0 : j = ⟨0, by omega⟩ := Fin.ext (by simpa using hj)
          have hi0 : i = ⟨0, by omega⟩ := by
            apply Fin.ext
            simp [i, hk0]
          have hji : j = i := hj0.trans hi0.symm
          have hfirstDir : w i = direction d₀ := by simpa [hji] using hjdir
          have hfirstCode : directionCode (w i) = d₀ := by
            rw [hfirstDir]
            exact directionCode_direction hd₀
          have hq0 : q = d₀ := by rw [hq, hfirstCode]
          simp [hdepth, hk0, hq0]
        · simp [hdepth, hk0]
      have hlegalQ : s.walk.legal q = true := by simpa [hq] using hlegal
      have hnotCentreBool : (advance s.walk.pos q != kernelCentre) = true := by
        simp [hnotCentre]
      have hgood : goodStep d₀ s.walk q = true := by
        change ((s.walk.depth != 0 || q == d₀) && s.walk.legal q &&
          (advance s.walk.pos q != (0, 0))) = true
        rw [hfirstTest, hlegalQ]
        simpa [kernelCentre] using hnotCentreBool
      have hwalk' : WalkPrefix w (k + 1) (transition E s q) := by
        simpa [q, hq] using walkPrefix_transition w k hk E s ⟨hdepth, hpos, hused⟩
      have hlen' : (k + 1) + m = total := by omega
      have hdecode' : decodeWord m c = suffixWord w (k + 1) m hlen' := by
        funext j
        have hj := congrFun hdecode j.succ
        have hexp : m - (j.val + 1) = m - 1 - j.val := by omega
        simpa [decodeWord, suffixWord, hexp, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj
      have hrest := ih total (k + 1) w hlen' c (transition E s q)
        hdecode' hwalk' htrail hfirst havoid
      change s.walk.pos ≠ target X ∧ goodStep d₀ s.walk q = true ∧
        ReplayTrace E X d₀ m c (transition E s q)
      exact ⟨hnotTarget, hgood, hrest⟩

theorem replayPrefix_of_trace (E : Exact) (X : PairType) (d₀ n c : Nat)
    (s : PrefixState) (h : ReplayTrace E X d₀ n c s) :
    (replayPrefix E X d₀ n c s).isSome = true := by
  induction n generalizing c s with
  | zero =>
      simp [ReplayTrace, replayPrefix] at h ⊢
      exact h
  | succ n ih =>
      rcases h with ⟨hpos, hstep, hrest⟩
      simpa [ReplayTrace, replayPrefix, hpos, hstep] using
        ih c (transition E s (c / 4 ^ n % 4)) hrest

theorem main : PrefixReplayCompleteLeaf := by
  intro E hE X d₀ n c hn hn12 hc hs
  rcases hs with ⟨htrail, hfirst, havoid⟩
  have hdecode : decodeWord n c = suffixWord (decodeWord n c) 0 n (by omega) := by
    funext i
    simp [suffixWord]
  have htrace := replayTrace_from_prefix E X d₀.val d₀.isLt n 0 n
    (decodeWord n c) (by omega) c initial hdecode (walkPrefix_initial _) htrail hfirst havoid
  exact replayPrefix_of_trace E X d₀.val n c initial htrace

#print axioms replayPrefix_of_trace
#print axioms main

end AKLT.W.H3C030
