import AKLT.Blueprint.Rec.NodesRecursion
import AKLT.Blueprint.Mom.NodesMoments
import AKLT.Blueprint.Mom.Assembly

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Rec

namespace AKLT.W.REC073

private theorem ico_unit : AKLT.Blueprint.Mom.IcoUnitStatement := by
  intro j
  have hs : Real.sqrt 5 ^ 2 = 5 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  have hp : goldenRatio ^ 2 = goldenRatio + 1 := by
    dsimp [goldenRatio]
    nlinarith
  rcases j with ⟨a, b, c⟩
  let v : Vec3 := if a = 0 then ![0, signValue b, signValue c * goldenRatio]
    else if a = 1 then ![signValue b, signValue c * goldenRatio, 0]
      else ![signValue c * goldenRatio, 0, signValue b]
  have hv : normSq v = 1 + goldenRatio ^ 2 := by
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      norm_num [v, normSq, dot, signValue, Fin.sum_univ_three] <;> ring
  have hr : icoRadius ^ 2 = goldenRatio + 2 := by
    dsimp [icoRadius]
    have hrad : 0 ≤ goldenRatio + 2 := by
      unfold goldenRatio
      positivity
    rw [Real.sq_sqrt hrad]
  simp only [icoVector]
  change normSq (fun i => v i / icoRadius) = 1
  rw [AKLT.Blueprint.Mom.normSq_div, hv, hp, hr]
  have hden : 0 < goldenRatio + 2 := by
    unfold goldenRatio
    positivity
  field_simp [ne_of_gt hden]
  ring_nf

private theorem normSq_nonneg (a : Vec3) : 0 ≤ normSq a := by
  rw [normSq, dot]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (a i)

private theorem ball_dot_bounds (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    |dot a b| ≤ 1 := by
  have hcs : (dot a b) ^ 2 ≤ normSq a * normSq b := by
    simpa [dot, normSq, pow_two] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b)
  have hprod : normSq a * normSq b ≤ 1 := by
    nlinarith [normSq_nonneg a, normSq_nonneg b]
  have hsquare : (dot a b) ^ 2 ≤ 1 := le_trans hcs hprod
  nlinarith [sq_abs (dot a b)]

private theorem one_add_dot_nonneg (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have h := ball_dot_bounds a b ha hb
  have h' := abs_le.mp h
  linarith

private theorem spin_ball (x : SpinLetter) : normSq (spinVector x) ≤ 1 := by
  cases x with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact le_of_eq (ico_unit j)

private theorem network_spin_ball {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) (x : Plane) : normSq (D.spins n x) ≤ 1 := by
  by_cases hx : x ∈ D.active
  · simp [Network.spins, hx]
    exact spin_ball (n ⟨x, hx⟩)
  · simp [Network.spins, hx, normSq, dot]

private noncomputable def networkWeight {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) (n : (x : D.active) → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
    ∏ e : originalLegs G,
      if pinned = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins n e.val.1) else 1

private theorem networkWeight_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) (n : (x : D.active) → SpinLetter) :
    0 ≤ networkWeight D τ pinned n := by
  unfold networkWeight
  apply mul_nonneg
  · apply mul_nonneg
    · apply Finset.prod_nonneg
      intro x hx
      have hs : D.status x.val = .U ∨ D.status x.val = .D := by
        have hneq : D.status x.val ≠ .X := by
          exact (Finset.mem_filter.mp x.property).2
        cases h : D.status x.val with
        | U => exact Or.inl rfl
        | D => exact Or.inr rfl
        | X => exact (hneq h).elim
      rcases hs with hs | hs <;> cases n x <;> norm_num [spinWeight, hs]
    · apply Finset.prod_nonneg
      intro e he
      exact one_add_dot_nonneg _ _ (network_spin_ball D n e.1) (network_spin_ball D n e.2)
  · apply Finset.prod_nonneg
    intro e he
    by_cases hp : pinned = true ∧ e.val.1 ∈ D.active
    · simpa [hp] using one_add_dot_nonneg _ _ (le_of_eq (τ e).property)
        (network_spin_ball D n e.val.1)
    · simp [hp]

private theorem network_expectation_abs_le_one {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) (u v : Plane) :
    |D.expectation τ pinned (fun n => dot (n u) (n v))| ≤ 1 := by
  classical
  let w := networkWeight D τ pinned
  let Z := D.partition τ pinned (fun _ => 1)
  have hweight : ∀ n, 0 ≤ w n := by
    intro n
    exact networkWeight_nonneg D τ pinned n
  have hobs : ∀ n : (x : D.active) → SpinLetter, |dot (D.spins n u) (D.spins n v)| ≤ 1 := by
    intro n
    exact ball_dot_bounds _ _ (network_spin_ball D n u) (network_spin_ball D n v)
  have hZ : Z = ∑ n, w n := by
    simp [Z, Network.partition, w, networkWeight]
  have hZnonneg : 0 ≤ Z := by
    rw [hZ]
    exact Finset.sum_nonneg fun n _ => hweight n
  have hnum : |D.partition τ pinned (fun n => dot (n u) (n v))| ≤ Z := by
    calc
      |D.partition τ pinned (fun n => dot (n u) (n v))| =
          |∑ n, w n * dot (D.spins n u) (D.spins n v)| := by
            apply congrArg abs
            simp only [Network.partition]
            apply Finset.sum_congr rfl
            intro n hn
            simp only [w, networkWeight]
            ring
      _ ≤ ∑ n, |w n * dot (D.spins n u) (D.spins n v)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n, w n := Finset.sum_le_sum fun n _ => by
        rw [abs_mul, abs_of_nonneg (hweight n)]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hobs n) (hweight n)
      _ = Z := hZ.symm
  have hratio : |D.partition τ pinned (fun n => dot (n u) (n v)) / Z| ≤ 1 := by
    by_cases hz : Z = 0
    · simp [hz]
    · rw [abs_div]
      rw [abs_of_nonneg hZnonneg]
      have hzpos : 0 < Z := lt_of_le_of_ne hZnonneg (Ne.symm hz)
      exact (div_le_one_of_le₀ hnum (le_of_lt hzpos))
  simpa [Network.expectation, Z] using hratio

private theorem pair_response_abs_le_two (p : PairData) :
    |p.response| ≤ 2 := by
  unfold PairData.response
  have ht := network_expectation_abs_le_one p.D p.τ true p.u p.v
  have hf := network_expectation_abs_le_one p.D p.τ false p.u p.v
  calc
    |p.D.expectation p.τ true (fun n => dot (n p.u) (n p.v)) -
        p.D.expectation p.τ false (fun n => dot (n p.u) (n p.v))|
      ≤ |p.D.expectation p.τ true (fun n => dot (n p.u) (n p.v))| +
        |p.D.expectation p.τ false (fun n => dot (n p.u) (n p.v))| := by
          simpa using abs_sub_le
            (p.D.expectation p.τ true (fun n => dot (n p.u) (n p.v))) 0
            (p.D.expectation p.τ false (fun n => dot (n p.u) (n p.v)))
    _ ≤ 1 + 1 := add_le_add ht hf
    _ = 2 := by norm_num

theorem main : AKLT.Blueprint.Rec.EnvelopeBoundsStatement := by
  intro X d
  constructor
  · change (0 : ℝ) ≤ sSup ({0} ∪ {r | ∃ G : Finset Plane, ∃ τ : PinAssignment G,
      ∃ D : Network G, ∃ u v c : Plane, D.ResponsePair X u v c ∧
      (d.toNat : ℕ∞) ≤ min (setDistance latticeDist u (↑(protectedSites G) : Set Plane))
        (setDistance latticeDist v (↑(protectedSites G) : Set Plane)) ∧
      r = |D.expectation τ true (fun n => dot (n u) (n v)) -
        D.expectation τ false (fun n => dot (n u) (n v))|})
    let S : Set ℝ := {0} ∪ {r | ∃ G : Finset Plane, ∃ τ : PinAssignment G,
        ∃ D : Network G, ∃ u v c : Plane, D.ResponsePair X u v c ∧
        (d.toNat : ℕ∞) ≤ min (setDistance latticeDist u (↑(protectedSites G) : Set Plane))
          (setDistance latticeDist v (↑(protectedSites G) : Set Plane)) ∧
        r = |D.expectation τ true (fun n => dot (n u) (n v)) -
          D.expectation τ false (fun n => dot (n u) (n v))|}
    have hmem : (0 : ℝ) ∈ S := Or.inl (Set.mem_singleton 0)
    have hupper : ∀ r ∈ S, r ≤ 2 := by
      intro r hr
      rcases hr with hr | hr
      · simp only [Set.mem_singleton_iff] at hr
        rw [hr]
        norm_num
      · rcases hr with ⟨G, τ, D, u, v, c, hp, hd, rfl⟩
        exact pair_response_abs_le_two ⟨G, τ, D, X, u, v, c, hp⟩
    have hbdd : BddAbove S := ⟨2, hupper⟩
    exact le_csSup hbdd hmem
  · apply AKLT.Blueprint.Rec.envelope_le_of_pair_bounds X d.toNat 2 (by norm_num)
    intro p hp hd
    exact pair_response_abs_le_two p

end AKLT.W.REC073

end

#print axioms AKLT.W.REC073.main
