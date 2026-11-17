module
public import AKLT.Blueprint.Rec.NodesResponse

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC015

private theorem phi_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold goldenRatio
  nlinarith [hs]

private theorem icoRadius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  have hp : 0 < goldenRatio + 2 := by
    unfold goldenRatio
    positivity
  simpa [icoRadius] using Real.sq_sqrt hp.le

private theorem normSq_div (v : Vec3) (c : ℝ) :
    normSq (fun i => v i / c) = normSq v / c ^ 2 := by
  unfold normSq dot
  calc
    (∑ i, v i / c * (v i / c)) = ∑ i, (v i * v i) / (c * c) := by
      apply Finset.sum_congr rfl
      intro i hi
      field_simp
    _ = (∑ i, v i * v i) / (c * c) := by rw [Finset.sum_div]
    _ = (∑ i, v i * v i) / c ^ 2 := by ring

private theorem icoVector_normSq (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨i, a, b⟩
  have hsigna : signValue a ^ 2 = 1 := by
    fin_cases a <;> norm_num [signValue]
  have hsignb : signValue b ^ 2 = 1 := by
    fin_cases b <;> norm_num [signValue]
  have hsa : signValue a * signValue a = 1 := by nlinarith [hsigna]
  have hsb : signValue b * signValue b = 1 := by nlinarith [hsignb]
  have hbφ : signValue b * goldenRatio * (signValue b * goldenRatio) = goldenRatio ^ 2 := by
    calc
      signValue b * goldenRatio * (signValue b * goldenRatio) =
          (signValue b * signValue b) * (goldenRatio * goldenRatio) := by ring
      _ = goldenRatio ^ 2 := by rw [hsb]; ring
  have hbase : normSq (if i = 0 then ![0, signValue a, signValue b * goldenRatio]
      else if i = 1 then ![signValue a, signValue b * goldenRatio, 0]
      else ![signValue b * goldenRatio, 0, signValue a]) = goldenRatio + 2 := by
    fin_cases i <;> simp [normSq, dot, Fin.sum_univ_succ] <;>
      rw [hsa, hbφ, phi_sq] <;> ring
  rw [icoVector, normSq_div, hbase, icoRadius_sq]
  have hp : 0 < goldenRatio + 2 := by unfold goldenRatio; positivity
  exact (div_self hp.ne').trans (by norm_num)

private theorem spinVector_normSq_le_one (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact le_of_eq (icoVector_normSq j)

private theorem dot_sq_le_normSq_mul (a b : Vec3) :
    dot a b ^ 2 ≤ normSq a * normSq b := by
  simpa only [dot, normSq, pow_two] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) a b)

private theorem dot_mem_unit_interval (a b : Vec3)
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) : -1 ≤ dot a b ∧ dot a b ≤ 1 := by
  have hsq := dot_sq_le_normSq_mul a b
  have hna : 0 ≤ normSq a := by
    unfold normSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (a i)
  have hnb : 0 ≤ normSq b := by
    unfold normSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (b i)
  have hprod : normSq a * normSq b ≤ 1 := by nlinarith
  constructor <;> nlinarith

private theorem network_spin_normSq_le_one {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) (x : Plane) :
    normSq (D.spins n x) ≤ 1 := by
  unfold Network.spins
  split
  · exact spinVector_normSq_le_one _
  · norm_num [normSq, dot]

private theorem network_weight_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) (n : (x : D.active) → SpinLetter) :
    0 ≤ (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
      (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
      ∏ e : originalLegs G,
        if pinned = true ∧ e.val.1 ∈ D.active then
          1 + dot (τ e).val (D.spins n e.val.1) else 1 := by
  apply mul_nonneg
  · apply mul_nonneg
    · apply Finset.prod_nonneg
      intro x _
      have hx : D.status x.val ≠ .X := (Finset.mem_filter.mp x.property).2
      cases hs : D.status x.val with
      | U => cases n x <;> norm_num [spinWeight]
      | D => cases n x <;> norm_num [spinWeight]
      | X => exact False.elim (hx hs)
    · apply Finset.prod_nonneg
      intro e _
      have h := dot_mem_unit_interval (D.spins n e.1) (D.spins n e.2)
        (network_spin_normSq_le_one D n e.1) (network_spin_normSq_le_one D n e.2)
      linarith [h.1]
  · apply Finset.prod_nonneg
    intro e _
    by_cases h : pinned = true ∧ e.val.1 ∈ D.active
    · rw [if_pos h]
      have hpin : normSq (τ e).val = 1 := (τ e).property
      have hd := dot_mem_unit_interval (τ e).val (D.spins n e.val.1) hpin.le
        (network_spin_normSq_le_one D n e.val.1)
      linarith [hd.1]
    · simp [h]

private theorem partition_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) :
    0 ≤ D.partition τ pinned (fun _ => 1) := by
  unfold Network.partition
  apply Finset.sum_nonneg
  intro n _
  have hw := network_weight_nonneg D τ pinned n
  simpa [mul_assoc] using hw

private theorem observable_partition_bounds {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) (u v : Plane) :
    -(D.partition τ pinned (fun _ => 1)) ≤
      D.partition τ pinned (fun n => dot (n u) (n v)) ∧
    D.partition τ pinned (fun n => dot (n u) (n v)) ≤
      D.partition τ pinned (fun _ => 1) := by
  let wt : ((x : D.active) → SpinLetter) → ℝ := fun n =>
    (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
      (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
      ∏ e : originalLegs G,
        if pinned = true ∧ e.val.1 ∈ D.active then
          1 + dot (τ e).val (D.spins n e.val.1) else 1
  have hpoint (n : (x : D.active) → SpinLetter) :
      -1 ≤ dot (D.spins n u) (D.spins n v) ∧ dot (D.spins n u) (D.spins n v) ≤ 1 :=
    dot_mem_unit_interval _ _ (network_spin_normSq_le_one D n u)
      (network_spin_normSq_le_one D n v)
  have hw (n : (x : D.active) → SpinLetter) : 0 ≤ wt n := by
    simpa [wt] using network_weight_nonneg D τ pinned n
  have hZ : D.partition τ pinned (fun _ => 1) = ∑ n, wt n := by
    unfold Network.partition
    apply Finset.sum_congr rfl
    intro n _
    dsimp [wt]
    ring
  have hN : D.partition τ pinned (fun n => dot (n u) (n v)) =
      ∑ n, wt n * dot (D.spins n u) (D.spins n v) := by
    unfold Network.partition
    apply Finset.sum_congr rfl
    intro n _
    dsimp [wt]
    ring
  constructor
  · rw [hZ, hN]
    calc
      -(∑ n, wt n) = ∑ n, -(wt n) := by rw [Finset.sum_neg_distrib]
      _ ≤ ∑ n, wt n * dot (D.spins n u) (D.spins n v) := by
        apply Finset.sum_le_sum
        intro n _
        have hq := (hpoint n).1
        have hm := mul_nonneg (hw n) (by linarith : 0 ≤ 1 + dot (D.spins n u) (D.spins n v))
        nlinarith
  · rw [hZ, hN]
    apply Finset.sum_le_sum
    intro n _
    have hq := (hpoint n).2
    have hm := mul_nonneg (hw n) (by linarith : 0 ≤ 1 - dot (D.spins n u) (D.spins n v))
    nlinarith

private theorem expectation_mem_unit_interval {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) (u v : Plane) :
    -1 ≤ D.expectation τ pinned (fun n => dot (n u) (n v)) ∧
    D.expectation τ pinned (fun n => dot (n u) (n v)) ≤ 1 := by
  let Z := D.partition τ pinned (fun _ => 1)
  let N := D.partition τ pinned (fun n => dot (n u) (n v))
  have hZ : 0 ≤ Z := partition_nonneg D τ pinned
  have hNZ := observable_partition_bounds D τ pinned u v
  change -Z ≤ N ∧ N ≤ Z at hNZ
  change -1 ≤ N / Z ∧ N / Z ≤ 1
  by_cases hz : Z = 0
  · have hN : N = 0 := by
      have hNlo := hNZ.1
      have hNhi := hNZ.2
      rw [hz] at hNlo hNhi
      exact le_antisymm hNhi (by linarith)
    simp [hz, hN]
  · have hZpos : 0 < Z := lt_of_le_of_ne hZ (Ne.symm hz)
    constructor
    · apply (le_div_iff₀ hZpos).2
      simpa using hNZ.1
    · apply (div_le_iff₀ hZpos).2
      simpa using hNZ.2

private theorem logarithmicMean_pos_of_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < logarithmicMean x y := by
  by_cases hxy : x = y
  · simpa [logarithmicMean, hxy] using hxy ▸ hx
  · simp only [logarithmicMean, if_neg hxy]
    by_cases h : y < x
    · have hlog : Real.log y < Real.log x := (Real.log_lt_log_iff hy hx).2 h
      exact div_pos (sub_pos.mpr h) (sub_pos.mpr hlog)
    · have h' : x < y := lt_of_le_of_ne (le_of_not_gt h) hxy
      have hlog : Real.log x < Real.log y := (Real.log_lt_log_iff hx hy).2 h'
      exact (div_pos_iff.mpr (Or.inr ⟨sub_neg.mpr h', sub_neg.mpr hlog⟩))

end AKLT.W.REC015

open AKLT.Blueprint.Rec

theorem AKLT.W.REC015.main : AKLT.Blueprint.Rec.BetaPrimePositiveStatement := by
  intro a haU f hN hOf
  let D' := removeSite a.D a.y
  have htrue := expectation_mem_unit_interval D' a.τ true f a.o
  have hfalse := expectation_mem_unit_interval D' a.τ false f a.o
  have hIt : 0 < 1 + removedPairMean a.D a.τ true a.y f a.o / 3 := by
    have h := htrue.1
    change -1 ≤ removedPairMean a.D a.τ true a.y f a.o at h
    change 0 < _
    dsimp [removedPairMean, D'] at h ⊢
    linarith
  have hI0 : 0 < 1 + removedPairMean a.D a.τ false a.y f a.o / 3 := by
    have h := hfalse.1
    change -1 ≤ removedPairMean a.D a.τ false a.y f a.o at h
    change 0 < _
    dsimp [removedPairMean, D'] at h ⊢
    linarith
  unfold AKLT.Defs.responseBetaPrime
  exact div_pos (by norm_num) (mul_pos (by norm_num) (logarithmicMean_pos_of_pos hIt hI0))
