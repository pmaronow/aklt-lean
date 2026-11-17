module
public import AKLT.W.H3C031.Accounting
public import AKLT.Cert.H2.Words

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Cert.H3
open AKLT.Cert.H3.Production
open CertData.H3.Bridge

namespace AKLT.W.H3C031

private theorem append_one_snoc {n : Nat} (w : DirectionWord n) (d : Compass) :
    appendWords w (fun _ : Fin 1 => d) = AKLT.Cert.H2.snoc w d := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [AKLT.Cert.H2.snoc_last]
    simp [appendWords]
  · simp [appendWords, AKLT.Cert.H2.snoc, Fin.snoc_castSucc]

private theorem directionCode_direction (d : Fin 4) :
    directionCode (direction d.val) = d.val := by
  fin_cases d <;> rfl

private theorem encodeWord_snoc {n : Nat} (w : DirectionWord n) (d : Compass) :
    encodeWord (AKLT.Cert.H2.snoc w d) = encodeWord w * 4 + directionCode d := by
  unfold encodeWord
  rw [List.finRange_succ_last, List.map_append, List.sum_append]
  have hmap :
      List.map ((fun i : Fin (n + 1) =>
        directionCode (AKLT.Cert.H2.snoc w d i) * 4^(n + 1 - 1 - i.val)) ∘ Fin.castSucc)
        (List.finRange n) =
      List.map (fun i : Fin n =>
        (directionCode (w i) * 4^(n - 1 - i.val)) * 4) (List.finRange n) := by
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp_apply, Fin.val_castSucc]
    simp only [AKLT.Cert.H2.snoc, Fin.snoc_castSucc]
    have hexp : n - i.val = (n - 1 - i.val) + 1 := by omega
    rw [show n + 1 - 1 - i.val = n - i.val by omega, hexp, pow_succ]
    ring
  rw [List.map_map, hmap, List.sum_map_mul_right]
  simp [Fin.val_last, AKLT.Cert.H2.snoc_last]

private theorem wordVertex_snoc_last {n : Nat} (w : DirectionWord n) (d : Compass) :
    wordVertex kernelStart (AKLT.Cert.H2.snoc w d) (n + 1) =
      wordVertex kernelStart w n + d.step := by
  rw [AKLT.Cert.H2.vertex_succ kernelStart (AKLT.Cert.H2.snoc w d) n (by omega),
    AKLT.Cert.H2.snoc_vertex kernelStart w d n le_rfl,
    show (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n by exact Fin.ext rfl,
    AKLT.Cert.H2.snoc_last]

private theorem wordVertex_snoc_old {n : Nat} (w : DirectionWord n) (d : Compass)
    (j : Nat) (hj : j ≤ n) :
    wordVertex kernelStart (AKLT.Cert.H2.snoc w d) j = wordVertex kernelStart w j :=
  AKLT.Cert.H2.snoc_vertex kernelStart w d j hj

private theorem advance_direction (d : Fin 4) (x : Point) :
    advance x d.val = x + (direction d.val).step := by
  fin_cases d <;> rfl

private theorem walkRepresents_snoc_step {n : Nat} (w : DirectionWord n) (d : Fin 4)
    (s : PrefixState) (hrep : WalkRepresents kernelStart 2 w s.walk) :
    WalkRepresents kernelStart 2 (AKLT.Cert.H2.snoc w (direction d.val))
      (s.walk.step d.val) := by
  rcases hrep with ⟨hdepth, hpos, hinc, hcode, hdeparted, hused⟩
  have hlast : windowArrival (AKLT.Cert.H2.snoc w (direction d.val)) = direction d.val := by
    unfold windowArrival
    simp only [dite_eq_left (by omega : 0 < n + 1)]
    have heq : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by
      apply Fin.ext
      simp
    rw [heq, AKLT.Cert.H2.snoc_last]
  have hvlast := wordVertex_snoc_last w (direction d.val)
  have hadvance := advance_direction d s.walk.pos
  unfold WalkRepresents
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Walk.step, hdepth]
  · change advance s.walk.pos d.val = wordVertex kernelStart (AKLT.Cert.H2.snoc w (direction d.val)) (n + 1)
    calc
      advance s.walk.pos d.val = s.walk.pos + (direction d.val).step := hadvance
      _ = wordVertex kernelStart (AKLT.Cert.H2.snoc w (direction d.val)) (n + 1) := by
        rw [hpos, hvlast]
  · change d.val = directionCode (windowArrival (AKLT.Cert.H2.snoc w (direction d.val)))
    simp [hlast, directionCode_direction]
  · change (s.walk.code * 4 + d.val) % 1048576 =
      encodeWord (AKLT.Cert.H2.snoc w (direction d.val)) % 1048576
    rw [hcode, encodeWord_snoc, directionCode_direction]
    omega
  · change s.walk.pos :: s.walk.departed =
      (List.finRange (n + 1)).reverse.map
        (fun i => wordVertex kernelStart (AKLT.Cert.H2.snoc w (direction d.val)) i.val)
    rw [hpos, hdeparted]
    simp [List.finRange_succ_last, List.reverse_append,
      List.map_reverse, List.map_map, wordVertex_snoc_old]
  · change bond s.walk.pos (advance s.walk.pos d.val) :: s.walk.used =
      (List.finRange (n + 1)).reverse.map
        (fun i => bond (wordVertex kernelStart (AKLT.Cert.H2.snoc w (direction d.val)) i.val)
          (wordVertex kernelStart (AKLT.Cert.H2.snoc w (direction d.val)) (i.val + 1)))
    have hadvance' : advance (wordVertex kernelStart w n) d.val =
        wordVertex kernelStart w n + (direction d.val).step := by
      simpa [hpos] using hadvance
    rw [hpos, hused, hadvance']
    simp [List.finRange_succ_last, List.reverse_append,
      List.map_reverse, List.map_map, wordVertex_snoc_old, wordVertex_snoc_last]

private theorem departed_contains_iff_count {n : Nat} (w : DirectionWord n) (walk : Walk)
    (hdeparted : walk.departed = (List.finRange n).reverse.map
      (fun i => wordVertex kernelStart w i.val)) :
    walk.departed.contains (wordVertex kernelStart w n) = true ↔
      0 < departureCount kernelStart w n (wordVertex kernelStart w n) := by
  have hlist : walk.departed.contains (wordVertex kernelStart w n) = true ↔
      ∃ j : Nat, j < n ∧ wordVertex kernelStart w j = wordVertex kernelStart w n := by
    rw [List.contains_iff_mem, hdeparted]
    simp only [List.mem_map, List.mem_reverse]
    constructor
    · rintro ⟨i, hi, heq⟩
      exact ⟨i.val, i.isLt, heq⟩
    · rintro ⟨j, hj, heq⟩
      let i : Fin n := ⟨j, hj⟩
      exact ⟨i, List.mem_finRange i, heq⟩
  have hcount : 0 < departureCount kernelStart w n (wordVertex kernelStart w n) ↔
      ∃ j : Nat, j < n ∧ wordVertex kernelStart w j = wordVertex kernelStart w n := by
    simp [departureCount, Finset.card_pos, Finset.Nonempty, Finset.mem_filter, Finset.mem_range]
  exact hlist.trans hcount.symm

private theorem snoc_last_revisit {n : Nat} (w : DirectionWord n) (d : Compass) :
    wordRevisit kernelStart (AKLT.Cert.H2.snoc w d) (Fin.last n) =
      decide (0 < departureCount kernelStart w n (wordVertex kernelStart w n)) := by
  simp [wordRevisit, AKLT.Cert.H2.snoc_vertex, AKLT.Cert.H2.snoc_departure]

private theorem trailBaseWeight_snoc {n : Nat} (w : DirectionWord n) (d : Compass) :
    trailBaseWeight kernelStart (AKLT.Cert.H2.snoc w d) =
      trailBaseWeight kernelStart w *
        (if 0 < departureCount kernelStart w n (wordVertex kernelStart w n) then 1 / 5 else 1 / 3) := by
  unfold trailBaseWeight
  rw [Fin.prod_univ_castSucc]
  simp only [AKLT.Cert.H2.snoc_old_revisit, snoc_last_revisit, decide_eq_true_eq]

private theorem base_accounting {E : Exact} (hE : ExactValid E) {n : Nat}
    (w : DirectionWord n) (s : PrefixState) (hrep : PrefixRepresents E w s)
    (d : Fin 4) (_htrail : IsTrail kernelStart kernelIncoming
      (appendWords w (fun _ : Fin 1 => direction d.val))) :
    trailBaseWeight kernelStart (appendWords w (fun _ : Fin 1 => direction d.val)) =
      (transition E s d.val).base / (E.denominator^(n + 1) : Nat) := by
  rcases hrep with ⟨hwalk, _, hbase, _, _⟩
  rcases hwalk with ⟨_hdepth, hpos, _, _, hdeparted, _⟩
  have hcontains : s.walk.departed.contains s.walk.pos = true ↔
      0 < departureCount kernelStart w n (wordVertex kernelStart w n) := by
    simpa [hpos] using departed_contains_iff_count w s.walk hdeparted
  have hword := append_one_snoc w (direction d.val)
  have hbaseWord := trailBaseWeight_snoc w (direction d.val)
  rw [hword, hbaseWord]
  have hthird : (E.third : ℚ) / E.denominator = 1 / 3 := hE.2.2.2.1
  have hfifth : (E.fifth : ℚ) / E.denominator = 1 / 5 := hE.2.2.2.2.1
  have hbaseTrans : (transition E s d.val).base =
      if 0 < departureCount kernelStart w n (wordVertex kernelStart w n)
      then s.base * E.fifth else s.base * E.third := by
    by_cases hr : 0 < departureCount kernelStart w n (wordVertex kernelStart w n)
    · have hc := hcontains.mpr hr
      have hm : s.walk.pos ∈ s.walk.departed := List.contains_iff_mem.mp hc
      simp [transition, hm, hr]
    · have hc : s.walk.departed.contains s.walk.pos = false := by
        cases hx : s.walk.departed.contains s.walk.pos with
        | false => rfl
        | true => exact False.elim (hr (hcontains.mp hx))
      have hm : s.walk.pos ∉ s.walk.departed := by
        intro hx
        exact hr (hcontains.mp (List.contains_iff_mem.mpr hx))
      by_cases hd : d.val = s.walk.incoming <;> simp [transition, hm, hr, hd]
  rw [hbaseTrans, hbase]
  by_cases hr : 0 < departureCount kernelStart w n (wordVertex kernelStart w n)
  · simp only [ite_eq_left hr]
    have hden : (E.denominator : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hE.1)
    push_cast
    rw [pow_succ]
    have hfifth' : 5 * (E.fifth : ℚ) = E.denominator := by
      field_simp [hden] at hfifth
      nlinarith [hfifth]
    field_simp [hden]
    nlinarith [hfifth']
  · simp only [ite_eq_right hr]
    have hden : (E.denominator : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hE.1)
    push_cast
    rw [pow_succ]
    have hthird' : 3 * (E.third : ℚ) = E.denominator := by
      field_simp [hden] at hthird
      nlinarith [hthird]
    field_simp [hden]
    nlinarith [hthird']

/-- The phase-counter component of the transition invariant, proved below. -/
def ResidualPhaseNumerators : Prop :=
  ∀ (E : Exact), ExactValid E → ∀ (n : Nat) (w : DirectionWord n)
    (s : PrefixState), PrefixRepresents E w s → ∀ d : Fin 4,
    IsTrail kernelStart kernelIncoming (appendWords w (fun _ : Fin 1 => direction d.val)) →
    ∀ φ : Phase,
      prefixPhases (appendWords w (fun _ : Fin 1 => direction d.val)) φ =
        (phaseNumerator (transition E s d.val) φ : ℚ) / (E.denominator^(n + 1) : Nat)


private theorem firstVisitList_snoc {n : Nat} (w : DirectionWord n) (d : Compass) :
    firstVisitList (AKLT.Cert.H2.snoc w d) =
      (firstVisitList w).map Fin.castSucc ++
        (if 0 < departureCount kernelStart w n (wordVertex kernelStart w n)
          then [] else [Fin.last n]) := by
  unfold firstVisitList
  rw [List.finRange_succ_last, List.filter_append, List.filter_map]
  have hold : List.filter
      ((fun i => !wordRevisit kernelStart (AKLT.Cert.H2.snoc w d) i) ∘ Fin.castSucc)
      (List.finRange n) = List.filter (fun i => !wordRevisit kernelStart w i)
      (List.finRange n) := by
    apply List.filter_congr
    intro i hi
    simp [AKLT.Cert.H2.snoc_old_revisit]
  rw [hold]
  by_cases hr : 0 < departureCount kernelStart w n (wordVertex kernelStart w n)
  · have hrev : wordRevisit kernelStart (AKLT.Cert.H2.snoc w d) (Fin.last n) = true := by
      rw [snoc_last_revisit]
      simp [hr]
    simp [hrev, hr]
  · have hrev : wordRevisit kernelStart (AKLT.Cert.H2.snoc w d) (Fin.last n) = false := by
      rw [snoc_last_revisit]
      simp [hr]
    simp [hrev, hr]

private theorem itemTimes_accounting {E : Exact} {n : Nat} (w : DirectionWord n)
    (s : PrefixState) (hrep : PrefixRepresents E w s) (d : Fin 4)
    (_htrail : IsTrail kernelStart kernelIncoming
      (appendWords w (fun _ : Fin 1 => direction d.val))) :
    (transition E s d.val).items.map RewardItem.time =
      (firstVisitList (appendWords w (fun _ : Fin 1 => direction d.val))).reverse.map Fin.val := by
  rcases hrep with ⟨hwalk, _, _, htimes, _⟩
  rcases hwalk with ⟨hdepth, hpos, _, _, hdeparted, _⟩
  have hcontains : s.walk.departed.contains s.walk.pos = true ↔
      0 < departureCount kernelStart w n (wordVertex kernelStart w n) := by
    simpa [hpos] using departed_contains_iff_count w s.walk hdeparted
  have hword := append_one_snoc w (direction d.val)
  rw [hword, firstVisitList_snoc]
  by_cases hr : 0 < departureCount kernelStart w n (wordVertex kernelStart w n)
  · have hc := hcontains.mpr hr
    have hm : s.walk.pos ∈ s.walk.departed := List.contains_iff_mem.mp hc
    have hitems : (transition E s d.val).items = s.items := by
      simp [transition, hm]
    rw [hitems]
    simp [hr, htimes, List.map_map]
  · have hc : s.walk.departed.contains s.walk.pos = false := by
      cases hx : s.walk.departed.contains s.walk.pos with
      | false => rfl
      | true => exact False.elim (hr (hcontains.mp hx))
    have hm : s.walk.pos ∉ s.walk.departed := by
      intro hx
      exact hr (hcontains.mp (List.contains_iff_mem.mpr hx))
    have hitems : (transition E s d.val).items =
        { straight := d.val == s.walk.incoming,
          reward := E.reward s.walk.incoming d.val (deadMaskAt s.walk),
          time := s.walk.depth } :: s.items := by
      by_cases hd : d.val = s.walk.incoming <;> simp [transition, hm, hd]
    rw [hitems]
    simp [hr, hdepth, htimes, List.map_map]

/-- The reward-item component of the transition invariant, proved below. -/
def ResidualRewardItems : Prop :=
  ∀ (E : Exact), ExactValid E → ∀ (n : Nat) (w : DirectionWord n)
    (s : PrefixState), PrefixRepresents E w s → ∀ d : Fin 4,
    IsTrail kernelStart kernelIncoming (appendWords w (fun _ : Fin 1 => direction d.val)) →
      ∀ item ∈ (transition E s d.val).items,
        ∃ i : Fin (n + 1), i.val = item.time ∧
          item.straight = wordStraight kernelIncoming
            (appendWords w (fun _ : Fin 1 => direction d.val)) i ∧
          (item.reward : ℚ) / E.denominator =
            witnessKappa (appendWords w (fun _ : Fin 1 => direction d.val)) i

/-- Assemble the walk, phase, base-weight, timestamp, and reward components. -/
theorem main_from_residuals (hPhase : ResidualPhaseNumerators)
    (hItems : ResidualRewardItems) : PrefixStepLeaf := by
  intro E hE n w s hrep d htrail
  have hwalkSnoc := walkRepresents_snoc_step w d s hrep.1
  have hword := append_one_snoc w (direction d.val)
  have hwalkWord : WalkRepresents kernelStart 2
      (appendWords w (fun _ : Fin 1 => direction d.val)) (s.walk.step d.val) := by
    rw [hword]
    exact hwalkSnoc
  have hnextWalk : (transition E s d.val).walk = s.walk.step d.val := by
    by_cases hv : s.walk.pos ∈ s.walk.departed <;>
      by_cases hd : d.val = s.walk.incoming <;> simp [transition, hv, hd]
  have hwalk : WalkRepresents kernelStart 2
      (appendWords w (fun _ : Fin 1 => direction d.val)) (transition E s d.val).walk := by
    rw [hnextWalk]
    exact hwalkWord
  have hp := hPhase E hE n w s hrep d htrail
  have hb := base_accounting hE w s hrep d htrail
  have htimes := itemTimes_accounting w s hrep d htrail
  have hi := hItems E hE n w s hrep d htrail
  change WalkRepresents kernelStart 2 (appendWords w (fun _ : Fin 1 => direction d.val))
      (transition E s d.val).walk ∧
    (∀ φ : Phase, prefixPhases (appendWords w (fun _ : Fin 1 => direction d.val)) φ =
      (phaseNumerator (transition E s d.val) φ : ℚ) / (E.denominator^(n + 1) : Nat)) ∧
    trailBaseWeight kernelStart (appendWords w (fun _ : Fin 1 => direction d.val)) =
      (transition E s d.val).base / (E.denominator^(n + 1) : Nat) ∧
    (transition E s d.val).items.map RewardItem.time =
      (firstVisitList (appendWords w (fun _ : Fin 1 => direction d.val))).reverse.map Fin.val ∧
    (∀ item ∈ (transition E s d.val).items,
      ∃ i : Fin (n + 1), i.val = item.time ∧
        item.straight = wordStraight kernelIncoming
          (appendWords w (fun _ : Fin 1 => direction d.val)) i ∧
        (item.reward : ℚ) / E.denominator =
          witnessKappa (appendWords w (fun _ : Fin 1 => direction d.val)) i)
  exact ⟨hwalk, hp, hb, htimes, hi⟩


private theorem prefixPhases_snoc {n : Nat} (w : DirectionWord n) (d : Compass) (ψ : Phase) :
    prefixPhases (AKLT.Cert.H2.snoc w d) ψ =
      ∑ φ : Phase, prefixPhases w φ *
        truePhaseCoefficient (AKLT.Cert.H2.snoc w d) (Fin.last n) φ ψ := by
  unfold prefixPhases
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
  have hupdate :
      (fun (p : Phase → ℚ) (i : Fin n) (ψ : Phase) => ∑ φ : Phase, p φ *
        truePhaseCoefficient (AKLT.Cert.H2.snoc w d) i.castSucc φ ψ) =
      (fun (p : Phase → ℚ) (i : Fin n) (ψ : Phase) => ∑ φ : Phase, p φ *
        truePhaseCoefficient w i φ ψ) := by
    funext p i ψ
    simp only [truePhaseCoefficient, AKLT.Cert.H2.snoc_old_revisit,
      AKLT.Cert.H2.snoc_old_straight, snoc_witness_old]
  change (List.foldl
      (fun (p : Phase → ℚ) (i : Fin n) (ψ : Phase) => ∑ φ : Phase, p φ *
        truePhaseCoefficient (AKLT.Cert.H2.snoc w d) i.castSucc φ ψ)
      phaseInitial (List.finRange n) |> fun p => ∑ φ : Phase, p φ *
        truePhaseCoefficient (AKLT.Cert.H2.snoc w d) (Fin.last n) φ ψ) = _
  rw [hupdate]
  rfl

private theorem snoc_straight_code {n : Nat} (w : DirectionWord n) (walk : Walk)
    (h : WalkRepresents kernelStart 2 w walk) (d : Fin 4) :
    wordStraight kernelIncoming (AKLT.Cert.H2.snoc w (direction d.val)) (Fin.last n) =
      decide (d.val = walk.incoming) := by
  simp only [wordStraight, AKLT.Cert.H2.snoc_last, snoc_incoming_last]
  have hin := walk_incoming_code w walk h
  have hiff : (direction d.val = AKLT.Cert.H2.nextIncoming kernelIncoming w) ↔
      d.val = walk.incoming := by
    constructor
    · intro hd
      rw [← directionCode_direction d, hd, ← hin]
    · intro hd
      rw [hd, hin, direction_code_inverse]
  simp only [hiff]

private theorem exact_last_reward_response {E : Exact} (hE : ExactValid E)
    {n : Nat} (w : DirectionWord n) (walk : Walk)
    (h : WalkRepresents kernelStart 2 w walk) (d : Fin 4)
    (ht : IsTrail kernelStart kernelIncoming (AKLT.Cert.H2.snoc w (direction d.val))) :
    (E.reward walk.incoming d.val (deadMaskAt walk) : ℚ) / E.denominator =
        witnessKappa (AKLT.Cert.H2.snoc w (direction d.val)) (Fin.last n) ∧
    (E.response walk.incoming d.val (deadMaskAt walk) : ℚ) / E.denominator =
      passageFactor (decide (d.val = walk.incoming)) *
        witnessKappa (AKLT.Cert.H2.snoc w (direction d.val)) (Fin.last n) / 3 := by
  have hin := walk_incoming_code w walk h
  let a : Fin 4 := ⟨walk.incoming, by rw [hin]; exact direction_code_lt _⟩
  let mask : Fin 16 := ⟨deadMaskAt walk, deadMaskAt_lt walk⟩
  have hrev : direction d.val ≠ (direction a.val).reverse := by
    simpa only [a, hin, direction_code_inverse] using
      AKLT.Cert.H2.snoc_nonreverse kernelStart kernelIncoming w (direction d.val) ht
  have he := hE.2.2.2.2.2 a d hrev mask
  have hk := witness_last_reward w (direction d.val) walk h
  have hadir : direction a.val = AKLT.Cert.H2.nextIncoming kernelIncoming w := by
    simp only [a, hin, direction_code_inverse]
  dsimp only [a, mask] at he
  rw [show direction walk.incoming = AKLT.Cert.H2.nextIncoming kernelIncoming w from hadir,
    ← hk] at he
  simpa only [eq_comm (a := walk.incoming)] using he

private theorem phase_sum (f : Phase → ℚ) :
    (∑ φ : Phase, f φ) = f .A + f .B + f .C + f .D := by
  rw [show (Finset.univ : Finset Phase) = {.A,.B,.C,.D} by decide]
  simp
  ring


/-- Exact one-step accounting for the rational phase weights. -/
theorem phase_accounting : ResidualPhaseNumerators := by
  intro E hE n w s hrep d htrail ψ
  rw [append_one_snoc] at htrail ⊢
  rw [prefixPhases_snoc]
  simp_rw [hrep.2.1]
  simp only [truePhaseCoefficient, snoc_last_revisit, snoc_straight_code w s.walk hrep.1 d]
  have hden : (E.denominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hE.1
  have hthird : (E.denominator : ℚ) = (E.third : ℚ) * 3 := by
    have hh := hE.2.2.2.1
    field_simp [hden] at hh
    nlinarith [hh]
  have hfifth : (E.denominator : ℚ) = (E.fifth : ℚ) * 5 := by
    have hh := hE.2.2.2.2.1
    field_simp [hden] at hh
    nlinarith [hh]
  have hcontains : s.walk.departed.contains s.walk.pos = true ↔
      0 < departureCount kernelStart w n (wordVertex kernelStart w n) := by
    simpa [hrep.1.2.1] using
      departed_contains_iff_count w s.walk hrep.1.2.2.2.2.1
  by_cases hr : 0 < departureCount kernelStart w n (wordVertex kernelStart w n)
  · have hm : s.walk.pos ∈ s.walk.departed := List.contains_iff_mem.mp (hcontains.mpr hr)
    cases ψ <;>
      simp [hr, phaseTransition,
        phaseDiagonal, phaseNumerator, transition, hm] <;>
      simp only [pow_succ] <;>
      field_simp [hden] <;> rw [hfifth] <;> ring
  · have hm : s.walk.pos ∉ s.walk.departed := by
      intro hm
      exact hr (hcontains.mp (List.contains_iff_mem.mpr hm))
    have he := (exact_last_reward_response hE w s.walk hrep.1 d htrail).2
    by_cases hd : d.val = s.walk.incoming
    · simp only [hd, decide_true] at he
      cases ψ <;>
        simp [phase_sum, hr, hd, phaseTransition,
          phaseDiagonal, phaseNumerator, transition, hm] <;>
        simp only [← he, ← hE.2.1, pow_succ] <;>
        field_simp [hden] <;> try rw [hthird]
      all_goals ring
    · simp only [hd, decide_false] at he
      cases ψ <;>
        simp [phase_sum, hr, hd, phaseTransition,
          phaseDiagonal, phaseNumerator, transition, hm] <;>
        simp only [← he, ← hE.2.2.1, pow_succ] <;>
        field_simp [hden] <;> try rw [hthird]
      all_goals ring

/-- Existing witnesses are causal; a fresh item records the exact local reward. -/
theorem item_accounting : ResidualRewardItems := by
  intro E hE n w s hrep d htrail
  rw [append_one_snoc] at htrail ⊢
  have hold : ∀ item ∈ s.items, ∃ i : Fin (n+1), i.val = item.time ∧
      item.straight = wordStraight kernelIncoming (AKLT.Cert.H2.snoc w (direction d.val)) i ∧
      (item.reward : ℚ) / E.denominator = witnessKappa (AKLT.Cert.H2.snoc w (direction d.val)) i := by
    intro item hi
    obtain ⟨i, htime, hstraight, hreward⟩ := hrep.2.2.2.2 item hi
    exact ⟨i.castSucc, htime, by simpa only [AKLT.Cert.H2.snoc_old_straight] using hstraight,
      by simpa only [snoc_witness_old] using hreward⟩
  by_cases hm : s.walk.pos ∈ s.walk.departed
  · simpa [transition, hm] using hold
  · have hfresh : ∃ i : Fin (n+1), i.val = s.walk.depth ∧
        (d.val == s.walk.incoming) = wordStraight kernelIncoming
          (AKLT.Cert.H2.snoc w (direction d.val)) i ∧
        (E.reward s.walk.incoming d.val (deadMaskAt s.walk) : ℚ) / E.denominator =
          witnessKappa (AKLT.Cert.H2.snoc w (direction d.val)) i := by
      refine ⟨Fin.last n, hrep.1.1.symm, ?_,
        (exact_last_reward_response hE w s.walk hrep.1 d htrail).1⟩
      rw [snoc_straight_code w s.walk hrep.1 d]
      exact Bool.beq_eq_decide_eq _ _
    intro item hi
    have himem : item = (⟨d.val == s.walk.incoming,
        E.reward s.walk.incoming d.val (deadMaskAt s.walk), s.walk.depth⟩ : RewardItem) ∨
        item ∈ s.items := by
      by_cases hd : d.val = s.walk.incoming <;> simpa [transition, hm, hd] using hi
    rcases himem with rfl | hi
    · exact hfresh
    · exact hold item hi

/-- The production transition preserves the complete semantic prefix invariant. -/
theorem main : CertData.H3.Bridge.PrefixStepLeaf :=
  main_from_residuals phase_accounting item_accounting

#print axioms phase_accounting
#print axioms item_accounting
#print axioms main_from_residuals
#print axioms main

end AKLT.W.H3C031
