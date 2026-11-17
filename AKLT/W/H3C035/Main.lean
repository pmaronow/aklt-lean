module
public import CertData.H3.Bridge.Interface
public import AKLT.Cert.H2.Words
public import AKLT.W.H3C031.Main
public import AKLT.W.H3C033.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production CertData.H3.Bridge
open AKLT.Cert.H2

namespace AKLT.W.H3C035

attribute [local instance] Classical.propDecidable

private theorem bond_comm (x y : Plane) : bond x y = bond y x := by
  unfold bond
  split_ifs with hxy hyx hyx
  · have h : x = y := Prod.ext (by omega) (by omega)
    subst y
    rfl
  · rfl
  · rfl
  · omega

private theorem bond_eq_iff (x y a b : Plane) :
    bond x y = bond a b ↔ ({x, y} : Finset Plane) = {a, b} := by
  constructor
  · intro h
    have edge (p q : Plane) :
        ({p, q} : Finset Plane) = {(bond p q).1, (bond p q).2} := by
      unfold bond
      split_ifs <;> simp [Finset.pair_comm]
    rw [edge x y, h, ← edge a b]
  · intro h
    have hset : ({x, y} : Set Plane) = {a, b} := by
      simpa using congrArg (fun s : Finset Plane => (s : Set Plane)) h
    rcases Set.pair_eq_pair_iff.mp hset with h | h
    · rcases h with ⟨rfl, rfl⟩
      rfl
    · rcases h with ⟨rfl, rfl⟩
      exact bond_comm _ _

private theorem advance_direction (p : Plane) (d : Compass) :
    advance p (directionCode d) = p + d.step := by
  cases d <;> rfl

private theorem direction_code (d : Compass) : direction (directionCode d) = d := by
  cases d <;> rfl

private theorem code_lt_four (d : Compass) : directionCode d < 4 := by
  cases d <;> decide

private theorem snoc_append {n : Nat} (w : DirectionWord n) (d : Compass) :
    snoc w d = appendWords w (fun _ : Fin 1 => d) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [appendWords]
  · simp [snoc, appendWords, j.isLt]

/-- A node reached before any earlier target hit; the last vertex may be a hit. -/
private def Reached {n : Nat} (X : PairType) (d₀ : Compass) (w : DirectionWord n) : Prop :=
  IsTrail kernelStart kernelIncoming w ∧
  (∀ j ≤ n, wordVertex kernelStart w j ≠ kernelCentre) ∧
  (∀ j < n, wordVertex kernelStart w j ≠ kernelTarget X) ∧
  (n = 0 ∨ FirstDirection w d₀)

private theorem legal_iff_fresh {n : Nat} (w : DirectionWord n) (s : Walk)
    (hs : WalkRepresents kernelStart 2 w s) (d : Compass) :
    s.legal (directionCode d) = true ↔
      ∀ i, wordBond kernelStart w i ≠
        {wordVertex kernelStart w n, wordVertex kernelStart w n + d.step} := by
  rcases hs with ⟨_, hpos, _, _, _, hused⟩
  simp [Walk.legal, hused, hpos, advance_direction, bond_eq_iff, wordBond]

private theorem trail_snoc_of_fresh {n : Nat} (w : DirectionWord n) (d : Compass)
    (hw : IsTrail kernelStart kernelIncoming w)
    (hf : ∀ i, wordBond kernelStart w i ≠
      {wordVertex kernelStart w n, wordVertex kernelStart w n + d.step})
    (hc : wordVertex kernelStart w n + d.step ≠ kernelCentre) :
    IsTrail kernelStart kernelIncoming (snoc w d) := by
  constructor
  · intro i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> intro he
    · rfl
    · exact False.elim (hf _ (by simpa only [snoc_last_bond, snoc_bond] using he.symm))
    · exact False.elim (hf _ (by simpa only [snoc_last_bond, snoc_bond] using he))
    · exact congrArg Fin.castSucc (hw.1 (by simpa only [snoc_bond] using he))
  · intro i hi
    induction i using Fin.lastCases with
    | last =>
      have hn : n = 0 := hi
      subst n
      rw [snoc_last]
      intro hd
      subst d
      exact hc (by simp [kernelStart, kernelCentre, kernelIncoming, Compass.reverse,
        Compass.step])
    | cast i =>
      simpa [snoc] using hw.2 i hi

private theorem reached_snoc {n : Nat} (X : PairType) (d₀ : Compass)
    (w : DirectionWord n) (s : Walk) (hs : WalkRepresents kernelStart 2 w s)
    (d : Compass) :
    Reached X d₀ (snoc w d) ↔
      Reached X d₀ w ∧ wordVertex kernelStart w n ≠ kernelTarget X ∧
        goodStep (directionCode d₀) s (directionCode d) = true := by
  have hvertex : wordVertex kernelStart (snoc w d) (n + 1) =
      wordVertex kernelStart w n + d.step := by
    rw [vertex_succ _ _ n (by omega), snoc_vertex _ _ _ n le_rfl]
    rw [show (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n from Fin.ext rfl, snoc_last]
  have hfirst : FirstDirection (snoc w d) d₀ ↔
      (if n = 0 then d = d₀ else FirstDirection w d₀) := by
    by_cases hn : n = 0
    · subst n
      simp only [↓reduceIte]
      constructor
      · rintro ⟨i, hi, hd⟩
        have he : i = Fin.last 0 := Fin.ext hi
        simpa only [he, snoc_last] using hd
      · intro hd
        exact ⟨Fin.last 0, rfl, (snoc_last w d).trans hd⟩
    · simp only [hn, ↓reduceIte]
      constructor
      · rintro ⟨i, hi, hd⟩
        have hlt : i.val < n := by omega
        exact ⟨⟨i.val, hlt⟩, hi, (snoc_apply_lt w d _ hlt).symm.trans hd⟩
      · rintro ⟨i, hi, hd⟩
        exact ⟨i.castSucc, hi, by simpa [snoc] using hd⟩
  have hgood : goodStep (directionCode d₀) s (directionCode d) = true ↔
      (n ≠ 0 ∨ d = d₀) ∧
      (∀ i, wordBond kernelStart w i ≠
        {wordVertex kernelStart w n, wordVertex kernelStart w n + d.step}) ∧
      wordVertex kernelStart w n + d.step ≠ kernelCentre := by
    have hcode : directionCode d = directionCode d₀ ↔ d = d₀ := by
      constructor
      · intro h
        simpa only [direction_code] using congrArg direction h
      · rintro rfl
        rfl
    simp only [goodStep, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne,
      beq_iff_eq, hs.1, hs.2.1, advance_direction, hcode, kernelCentre,
      and_assoc, legal_iff_fresh w s hs d]
  rw [hgood]
  constructor
  · rintro ⟨ht, hc, hv, hdir⟩
    have hp : IsTrail kernelStart kernelIncoming w := by
      simpa using trail_initWord kernelStart kernelIncoming (snoc w d) ht
    have hdir' := hfirst.mp (hdir.resolve_left (by omega))
    refine ⟨⟨hp, ?_, ?_, ?_⟩, ?_, ?_, snoc_fresh _ _ _ _ ht, ?_⟩
    · intro j hj
      simpa only [snoc_vertex _ _ _ j hj] using hc j (by omega)
    · intro j hj
      simpa only [snoc_vertex kernelStart w d j (by omega)] using hv j (by omega)
    · by_cases hn : n = 0
      · exact Or.inl hn
      · exact Or.inr (by simpa [hn] using hdir')
    · simpa only [snoc_vertex _ _ _ n le_rfl] using hv n (by omega)
    · by_cases hn : n = 0
      · exact Or.inr (by simpa [hn] using hdir')
      · exact Or.inl hn
    · simpa only [hvertex] using hc (n + 1) le_rfl
  · rintro ⟨⟨ht, hc, hv, hdir⟩, hend, hfirst', hf, hc'⟩
    refine ⟨trail_snoc_of_fresh w d ht hf hc', ?_, ?_, Or.inr (hfirst.mpr ?_)⟩
    · intro j hj
      by_cases hjn : j ≤ n
      · rw [snoc_vertex _ _ _ j hjn]
        exact hc j hjn
      · have hj' : j = n + 1 := by omega
        simpa only [hj', hvertex] using hc'
    · intro j hj
      rw [snoc_vertex _ _ _ j (by omega)]
      by_cases hjn : j < n
      · exact hv j hjn
      · simpa only [show j = n by omega] using hend
    · by_cases hn : n = 0
      · simpa [hn] using hfirst'.resolve_left (by simp [hn])
      · simpa [hn] using hdir.resolve_left hn

private theorem reached_terminal {n : Nat} (X : PairType) (d₀ : Compass) (w : DirectionWord n) :
    (Reached X d₀ w ∧ wordVertex kernelStart w n = kernelTarget X) ↔
      (ClosedTrail X w ∧ FirstDirection w d₀) := by
  constructor
  · rintro ⟨⟨ht, hc, hv, hdir⟩, hend⟩
    refine ⟨⟨ht, hend, hc, hv⟩, hdir.resolve_left ?_⟩
    intro hn
    subst n
    cases X <;> simp [kernelStart, kernelTarget] at hend
  · rintro ⟨⟨ht, hend, hc, hv⟩, hdir⟩
    exact ⟨⟨ht, hc, hv, Or.inr hdir⟩, hend⟩


private def wordState (E : Exact) : (n : Nat) → DirectionWord n → PrefixState
  | 0, _ => initial
  | n + 1, w => transition E (wordState E n (initWord w)) (directionCode (w (Fin.last n)))

@[simp] private theorem wordState_snoc (E : Exact) {n : Nat} (w : DirectionWord n) (d : Compass) :
    wordState E (n + 1) (snoc w d) = transition E (wordState E n w) (directionCode d) := by
  simp only [wordState, initWord_snoc, snoc_last]

private theorem initial_represents (E : Exact) (w : DirectionWord 0) :
    PrefixRepresents E w initial := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [WalkRepresents, initial, prefixInitial, wordVertex, encodeWord, kernelStart]
  · intro φ
    cases φ <;> simp [prefixPhases, phaseInitial, phaseNumerator, initial]
  · simp [trailBaseWeight, initial]
  · simp [initial, firstVisitList]
  · simp [initial]

private theorem wordState_represents (hstep : PrefixStepLeaf) (E : Exact) (hE : ExactValid E)
    {n : Nat} (w : DirectionWord n) (hw : IsTrail kernelStart kernelIncoming w) :
    PrefixRepresents E w (wordState E n w) := by
  induction n with
  | zero => exact initial_represents E w
  | succ n ih =>
    have hp := trail_initWord kernelStart kernelIncoming w hw
    have hr := ih (initWord w) hp
    have htrail : IsTrail kernelStart kernelIncoming
        (appendWords (initWord w) (fun _ : Fin 1 => w (Fin.last n))) := by
      rw [← snoc_append, snoc_initWord]
      exact hw
    have hh := hstep E hE n (initWord w) (wordState E n (initWord w)) hr
      ⟨directionCode (w (Fin.last n)), code_lt_four _⟩ (by simpa only [direction_code] using htrail)
    simpa only [direction_code, ← snoc_append, snoc_initWord, wordState] using hh

private theorem value_zero (E : Exact) : resultValue E zeroResult = 0 := by
  simp [resultValue, zeroResult]

private theorem value_add (E : Exact) (r s : PrefixResult) :
    resultValue E (r.add s) = resultValue E r + resultValue E s := by
  simp [resultValue, PrefixResult.add, Nat.cast_add, add_div]
  ring

private theorem value_fold (E : Exact) (rs : List PrefixResult) (r : PrefixResult) :
    resultValue E (rs.foldl PrefixResult.add r) = resultValue E r +
      (rs.map (resultValue E)).sum := by
  induction rs generalizing r with
  | nil => simp
  | cons s rs ih => simp [ih, value_add, add_assoc]

private theorem dirs_sum (f : Nat → ℚ) :
    (dirs.map f).sum = ∑ d : Compass, f (directionCode d) := by
  simp [dirs, show (Finset.univ : Finset Compass) =
    {.east, .north, .west, .south} from rfl, directionCode]

private theorem value_nodes (E : Exact) (r : PrefixResult) (nodes : Nat) :
    resultValue E {r with nodes := nodes} = resultValue E r := rfl

private theorem value_dfs_step (E : Exact) (X : PairType) (d₀ : Compass)
    (fuel : Nat) (s : PrefixState) :
    resultValue E (earlyDFS E X (directionCode d₀) (fuel + 1) s) =
      resultValue E (earlyDFS E X (directionCode d₀) 0 s) +
        (if s.walk.pos = target X then 0 else
          ∑ d : Compass, if goodStep (directionCode d₀) s.walk (directionCode d) then
            resultValue E (earlyDFS E X (directionCode d₀) fuel
              (transition E s (directionCode d))) else 0) := by
  simp only [earlyDFS]
  split_ifs with ht
  · simp
  · rw [value_nodes, value_fold, value_zero, zero_add, List.map_map, dirs_sum]
    simp only [value_nodes, value_zero, zero_add]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs with hg <;> simp [hg, value_zero]

/-- The total remaining DFS value at a fixed true-word layer. -/
private def frontierValue (E : Exact) (X : PairType) (d₀ : Compass) (n fuel : Nat) : ℚ :=
  ∑ w : DirectionWord n, if Reached X d₀ w then
    resultValue E (earlyDFS E X (directionCode d₀) fuel (wordState E n w)) else 0

/-- The contribution from exactly one first-hit length. -/
private def hitValue (X : PairType) (d₀ : Compass) (n : Nat) : ℚ :=
  ∑ w : DirectionWord n,
    if ClosedTrail X w ∧ FirstDirection w d₀ then closedContribution w else 0

private theorem frontier_zero (hstep : PrefixStepLeaf) (hshort : ShortValueLeaf)
    (E : Exact) (hE : ExactValid E) (X : PairType) (d₀ : Compass)
    (n : Nat) (hn : n ≤ 12) : frontierValue E X d₀ n 0 = hitValue X d₀ n := by
  classical
  apply Finset.sum_congr rfl
  intro w _
  by_cases hr : Reached X d₀ w
  · have hrep := wordState_represents hstep E hE w hr.1
    have hp := hrep.1.2.1
    have ht : target X = kernelTarget X := by cases X <;> rfl
    simp only [hr, ↓reduceIte, earlyDFS, hp, ht]
    by_cases hend : wordVertex kernelStart w n = kernelTarget X
    · have hc := (reached_terminal X d₀ w).mp ⟨hr, hend⟩
      simp only [hend, ↓reduceIte, hc, resultValue, Nat.cast_zero, zero_div, add_zero]
      exact hshort E hE n hn w _ hrep
    · have hc : ¬ (ClosedTrail X w ∧ FirstDirection w d₀) := by
        intro hc
        exact hend hc.1.2.1
      simp [hend, hc, resultValue, zeroResult]
  · have hc : ¬ (ClosedTrail X w ∧ FirstDirection w d₀) := by
      intro hc
      exact hr ((reached_terminal X d₀ w).mpr hc).1
    simp [hr, hc]

private theorem frontier_step (hstep : PrefixStepLeaf) (hshort : ShortValueLeaf)
    (E : Exact) (hE : ExactValid E) (X : PairType) (d₀ : Compass)
    (n fuel : Nat) (hn : n ≤ 12) :
    frontierValue E X d₀ n (fuel + 1) = hitValue X d₀ n +
      frontierValue E X d₀ (n + 1) fuel := by
  classical
  rw [← frontier_zero hstep hshort E hE X d₀ n hn]
  unfold frontierValue
  rw [sum_snoc, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hr : Reached X d₀ w
  · have hrep := wordState_represents hstep E hE w hr.1
    have ht : target X = kernelTarget X := by cases X <;> rfl
    simp_rw [reached_snoc X d₀ w (wordState E n w).walk hrep.1]
    simp only [hr, true_and, ↓reduceIte, wordState_snoc]
    rw [value_dfs_step]
    rw [hrep.1.2.1, ht]
    congr 1
    by_cases hend : wordVertex kernelStart w n = kernelTarget X
    · simp [hend]
    · simp [hend]
  · have hnot (d : Compass) : ¬ Reached X d₀ (snoc w d) := by
      intro hd
      obtain ⟨ht, hc, hv, hf⟩ := hd
      apply hr
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa using trail_initWord kernelStart kernelIncoming (snoc w d) ht
      · intro j hj
        simpa only [snoc_vertex kernelStart w d j hj] using hc j (by omega)
      · intro j hj
        simpa only [snoc_vertex kernelStart w d j (by omega)] using hv j (by omega)
      · by_cases hn : n = 0
        · exact Or.inl hn
        · obtain ⟨i, hi, hdi⟩ := hf.resolve_left (by omega)
          have hlt : i.val < n := by omega
          exact Or.inr ⟨⟨i.val, hlt⟩, hi,
            (snoc_apply_lt w d i.val hlt).symm.trans hdi⟩
    simp [hr, hnot]

private theorem frontier_sum (hstep : PrefixStepLeaf) (hshort : ShortValueLeaf)
    (E : Exact) (hE : ExactValid E) (X : PairType) (d₀ : Compass)
    (n fuel : Nat) (hn : n + fuel ≤ 12) :
    frontierValue E X d₀ n fuel =
      ∑ j ∈ Finset.range (fuel + 1), hitValue X d₀ (n + j) := by
  induction fuel generalizing n with
  | zero => simp [frontier_zero hstep hshort E hE X d₀ n (by omega)]
  | succ fuel ih =>
    rw [frontier_step hstep hshort E hE X d₀ n fuel (by omega),
      ih (n + 1) (by omega)]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    omega

private theorem hit_zero (X : PairType) (d₀ : Compass) : hitValue X d₀ 0 = 0 := by
  simp [hitValue, FirstDirection]

private theorem hit_range (X : PairType) (d₀ : Compass) (depth : Nat) :
    (∑ j ∈ Finset.range (depth + 1), hitValue X d₀ j) =
      firstDirectionPartialRow X d₀ depth := by
  induction depth with
  | zero => simp [hit_zero, firstDirectionPartialRow]
  | succ depth ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [firstDirectionPartialRow, Finset.sum_Icc_succ_top (by omega : 1 ≤ depth + 1)]
    simp only [hitValue]
    congr 1
    apply Finset.sum_congr (by ext; simp)
    intro w _
    split_ifs <;> rfl

private theorem frontier_root (E : Exact) (X : PairType) (d₀ : Compass) (depth : Nat) :
    frontierValue E X d₀ 0 depth =
      resultValue E (earlyDFS E X (directionCode d₀) depth initial) := by
  have hr (w : DirectionWord 0) : Reached X d₀ w := by
    refine ⟨?_, ?_, ?_, Or.inl rfl⟩
    · simp [IsTrail, Function.Injective]
    · intro j hj
      have hj' : j = 0 := by omega
      simp [hj', kernelStart, kernelCentre]
    · intro j hj
      omega
  simp [frontierValue, hr, wordState]

/-- Early soundness reduces to the prefix-step invariant and the exact short value. -/
private theorem earlySound_of_step_and_short (hstep : PrefixStepLeaf) (hshort : ShortValueLeaf) :
    EarlySoundLeaf := by
  intro E hE X d₀ depth hdepth
  have hc : directionCode (direction d₀.val) = d₀.val := by
    rcases d₀ with ⟨d, hd⟩
    dsimp
    interval_cases d <;> rfl
  have hh := frontier_sum hstep hshort E hE X (direction d₀.val) 0 depth (by simpa using hdepth)
  rw [frontier_root, hc] at hh
  simpa only [Nat.zero_add, hit_range] using hh

/-- The early DFS enumerates exactly the closed trails through the cutoff. -/
theorem main : CertData.H3.Bridge.EarlySoundLeaf :=
  earlySound_of_step_and_short AKLT.W.H3C031.main AKLT.W.H3C033.main


end AKLT.W.H3C035

#print axioms AKLT.W.H3C035.main
