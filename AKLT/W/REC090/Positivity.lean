module
public import AKLT.Blueprint.Rec.NodesV2Local

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC090

theorem normSq_nonneg (v : Vec3) : 0 ≤ normSq v := by
  change 0 ≤ ∑ i, v i * v i
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem normSq_add (a b : Vec3) :
    normSq (a + b) = normSq a + normSq b + 2 * dot a b := by
  simp [normSq, dot, Fin.sum_univ_succ]
  ring

theorem normSq_eq_zero {v : Vec3} (h : normSq v = 0) : v = 0 := by
  ext i
  have hi : v i * v i ≤ normSq v :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)
  change v i = 0
  nlinarith [sq_nonneg (v i)]

theorem ball_factor_nonneg {a b : Vec3} (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have h := normSq_nonneg (a + b)
  rw [normSq_add] at h
  linarith

theorem ball_factor_zero {a b : Vec3} (ha : normSq a ≤ 1) (hb : normSq b ≤ 1)
    (h : 1 + dot a b = 0) : a = -b := by
  have hz : normSq (a + b) = 0 := by
    have hn := normSq_nonneg (a + b)
    rw [normSq_add] at *
    linarith
  exact eq_neg_of_add_eq_zero_left (normSq_eq_zero hz)

theorem goldenRatio_pos : 0 < goldenRatio := by
  unfold goldenRatio
  positivity

theorem goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold goldenRatio
  nlinarith

theorem icoRadius_pos : 0 < icoRadius := by
  exact Real.sqrt_pos.mpr (by linarith [goldenRatio_pos])

theorem icoRadius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  exact Real.sq_sqrt (by linarith [goldenRatio_pos])

theorem icoVector_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨j, a, b⟩
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [icoVector, signValue, normSq, dot, Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt icoRadius_pos] <;>
    nlinarith [goldenRatio_sq, icoRadius_sq]

theorem spinVector_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact (icoVector_unit j).le

theorem spinWeight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

theorem spinWeight_some_pos {s : Status} (hs : s ≠ .X) (j : IcoLetter) :
    0 < spinWeight s (some j) := by
  cases s <;> norm_num [spinWeight] at *

theorem network_spins_ball {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) (x : Plane) : normSq (D.spins n x) ≤ 1 := by
  classical
  unfold Network.spins
  split
  · exact spinVector_ball _
  · norm_num [normSq, dot]

theorem partition_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) : 0 ≤ D.partition τ pinned (fun _ => 1) := by
  classical
  unfold Network.partition
  apply Finset.sum_nonneg
  intro n _
  apply mul_nonneg
  · apply mul_nonneg
    · exact mul_nonneg (Finset.prod_nonneg fun x _ => spinWeight_nonneg _ _) zero_le_one
    · exact Finset.prod_nonneg fun e _ =>
        ball_factor_nonneg (network_spins_ball D n e.1) (network_spins_ball D n e.2)
  · apply Finset.prod_nonneg
    intro e _
    split
    · exact ball_factor_nonneg (τ e).property.le (network_spins_ball D n e.val.1)
    · exact zero_le_one

/-- Six vertices whose coordinate sums are positive. -/
abbrev PositiveLetter := Fin 3 × Fin 2

def positiveLetter (j : PositiveLetter) : IcoLetter := (j.1, j.2, 0)

theorem goldenRatio_gt_one : 1 < goldenRatio := by
  have hs : (1 : ℝ) < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  dsimp [goldenRatio]
  linarith

theorem positiveLetter_sum_pos (j : PositiveLetter) :
    0 < ∑ i, icoVector (positiveLetter j) i := by
  have heq : (∑ i, icoVector (positiveLetter j) i) =
      (signValue j.2 + goldenRatio) / icoRadius := by
    rcases j with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;>
      norm_num [positiveLetter, icoVector, signValue, Fin.sum_univ_succ] <;> ring
  rw [heq]
  apply div_pos _ icoRadius_pos
  have hsign : -1 ≤ signValue j.2 := by
    unfold signValue
    split <;> norm_num
  linarith [goldenRatio_gt_one]

theorem positiveLetter_injective :
    Function.Injective (fun j : PositiveLetter => icoVector (positiveLetter j)) := by
  intro a b hab
  have h0 := congrFun hab 0
  have h1 := congrFun hab 1
  have h2 := congrFun hab 2
  rcases a with ⟨a, s⟩
  rcases b with ⟨b, t⟩
  fin_cases a <;> fin_cases b <;> fin_cases s <;> fin_cases t <;>
    norm_num [positiveLetter, icoVector, signValue] at h0 h1 h2 ⊢
  all_goals
    try field_simp [ne_of_gt icoRadius_pos] at h0
    try field_simp [ne_of_gt icoRadius_pos] at h1
    try field_simp [ne_of_gt icoRadius_pos] at h2
    nlinarith [goldenRatio_pos, icoRadius_pos, goldenRatio_gt_one]

theorem positiveLetter_factor_pos (a b : PositiveLetter) :
    0 < 1 + dot (icoVector (positiveLetter a)) (icoVector (positiveLetter b)) := by
  apply lt_of_le_of_ne (ball_factor_nonneg (icoVector_unit _).le (icoVector_unit _).le)
  intro hz
  have heq := ball_factor_zero (icoVector_unit (positiveLetter a)).le
    (icoVector_unit (positiveLetter b)).le hz.symm
  have hs := congrArg (fun v : Vec3 => ∑ i, v i) heq
  simp only [Pi.neg_apply, Finset.sum_neg_distrib] at hs
  linarith [positiveLetter_sum_pos a, positiveLetter_sum_pos b]

/-- Fewer than six unit pin directions cannot exclude every positive letter. -/
theorem exists_positiveLetter {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → UnitVector) (hs : s.card < 6) :
    ∃ j : PositiveLetter, ∀ i ∈ s, 0 < 1 + dot (p i).val (icoVector (positiveLetter j)) := by
  classical
  let bad := fun i : ι => Finset.univ.filter fun j : PositiveLetter =>
    1 + dot (p i).val (icoVector (positiveLetter j)) = 0
  have hbad : ∀ i, (bad i).card ≤ 1 := by
    intro i
    apply Finset.card_le_one.mpr
    intro a ha b hb
    apply positiveLetter_injective
    have hza := (Finset.mem_filter.mp ha).2
    have hzb := (Finset.mem_filter.mp hb).2
    have hea := ball_factor_zero (p i).property.le (icoVector_unit _).le hza
    have heb := ball_factor_zero (p i).property.le (icoVector_unit _).le hzb
    exact neg_injective (hea.symm.trans heb)
  have hcard : (s.biUnion bad).card < (Finset.univ : Finset PositiveLetter).card := by
    calc
      (s.biUnion bad).card ≤ ∑ i ∈ s, (bad i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ s, 1 := Finset.sum_le_sum fun i _ => hbad i
      _ = s.card := by simp
      _ < 6 := hs
      _ = (Finset.univ : Finset PositiveLetter).card := by decide
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨j, ?_⟩
  intro i hi
  apply lt_of_le_of_ne (ball_factor_nonneg (p i).property.le (icoVector_unit _).le)
  intro hz
  exact hj (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz.symm⟩⟩)

theorem originalLegs_neighbor {G : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs G) : e.2 ∈ neighbors e.1 := by
  obtain ⟨x, _, he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp he
  cases heq
  exact (Finset.mem_sdiff.mp hz).1

theorem originalLegs_at_card_le_four (G : Finset Plane) (x : Plane) :
    ((originalLegs G).filter fun e => e.1 = x).card ≤ 4 := by
  classical
  let s := (originalLegs G).filter fun e => e.1 = x
  have hinj : Set.InjOn Prod.snd (↑s : Set (Plane × Plane)) := by
    intro a ha b hb hab
    have hax := (Finset.mem_filter.mp ha).2
    have hbx := (Finset.mem_filter.mp hb).2
    exact Prod.ext (hax.trans hbx.symm) hab
  calc
    s.card = (s.image Prod.snd).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (neighbors x).card := Finset.card_le_card (by
      intro z hz
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
      have hx := (Finset.mem_filter.mp he).2
      rw [← hx]
      exact originalLegs_neighbor (Finset.mem_filter.mp he).1)
    _ ≤ 4 := by
      exact (Finset.card_image_le).trans (by decide)

/-- Every original network has a positive normalizer, for either pin choice.
The argument uses the original lattice legs and does not require auxiliary rules. -/
theorem partition_pos {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) : 0 < D.partition τ pinned (fun _ => 1) := by
  classical
  let s := fun x : Plane => (Finset.univ : Finset (originalLegs G)).filter fun e => e.val.1 = x
  have hs : ∀ x, (s x).card < 6 := by
    intro x
    have hle : (s x).card ≤ ((originalLegs G).filter fun e => e.1 = x).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro e he
        exact Finset.mem_filter.mpr ⟨e.property, (Finset.mem_filter.mp he).2⟩
      · exact Subtype.val_injective.injOn
    exact lt_of_le_of_lt (hle.trans (originalLegs_at_card_le_four G x)) (by norm_num)
  choose j hj using fun x => exists_positiveLetter (s x) τ (hs x)
  let n : D.active → SpinLetter := fun x => some (positiveLetter (j x.val))
  let w : (D.active → SpinLetter) → ℝ := fun n' =>
    (∏ x : D.active, spinWeight (D.status x.val) (n' x)) *
      (∏ e ∈ D.bonds, (1 + dot (D.spins n' e.1) (D.spins n' e.2))) *
      ∏ e : originalLegs G,
        if pinned = true ∧ e.val.1 ∈ D.active then
          1 + dot (τ e).val (D.spins n' e.val.1) else 1
  have hn : ∀ x (hx : x ∈ D.active),
      D.spins n x = icoVector (positiveLetter (j x)) := by
    intro x hx
    simp [Network.spins, hx, n, spinVector]
  have hw : 0 < w n := by
    apply mul_pos
    · apply mul_pos
      · apply Finset.prod_pos
        intro x _
        exact spinWeight_some_pos (Finset.mem_filter.mp x.property).2 _
      · apply Finset.prod_pos
        intro e he
        have he' := (Finset.mem_filter.mp he).2
        rw [hn e.1 he'.1, hn e.2 he'.2.1]
        exact positiveLetter_factor_pos _ _
    · apply Finset.prod_pos
      intro e _
      split
      · rename_i he
        rw [hn e.val.1 he.2]
        exact hj e.val.1 e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
      · exact zero_lt_one
  apply lt_of_lt_of_le hw
  change w n ≤ ∑ n', _
  simp only [mul_one]
  change w n ≤ ∑ n', w n'
  apply Finset.single_le_sum (f := w) _ (Finset.mem_univ n)
  intro n' _
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.prod_nonneg fun x _ => spinWeight_nonneg _ _
    · exact Finset.prod_nonneg fun e _ =>
        ball_factor_nonneg (network_spins_ball D n' e.1) (network_spins_ball D n' e.2)
  · apply Finset.prod_nonneg
    intro e _
    split
    · exact ball_factor_nonneg (τ e).property.le (network_spins_ball D n' e.val.1)
    · exact zero_le_one

end AKLT.W.REC090
