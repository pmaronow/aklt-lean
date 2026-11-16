import AKLT.Blueprint.Rec.NodesRecursion

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs

namespace AKLT.W.REC078

lemma icoVector_normSq_eq_one (j : IcoLetter) : normSq (icoVector j) = 1 := by
  have hφ : goldenRatio ^ 2 = goldenRatio + 1 := by
    dsimp [goldenRatio]
    have hs : 0 ≤ (5 : ℝ) := by norm_num
    nlinarith [Real.sq_sqrt hs]
  have hr : 0 < icoRadius := by
    apply Real.sqrt_pos.2
    unfold goldenRatio
    positivity
  have hr2 : icoRadius ^ 2 = goldenRatio + 2 := by
    dsimp [icoRadius]
    have hrad : 0 ≤ goldenRatio + 2 := by
      unfold goldenRatio
      positivity
    rw [Real.sq_sqrt hrad]
  rcases j with ⟨i, kl⟩
  rcases kl with ⟨k, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases l <;>
    simp [normSq, dot, icoVector, signValue, Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt hr] <;> nlinarith [hφ, hr2]

lemma spinVector_normSq_le_one (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => rw [spinVector, icoVector_normSq_eq_one j]

lemma normSq_sub (x y : Vec3) : normSq (fun i => x i - y i) =
    normSq x + normSq y - 2 * dot x y := by
  simp only [normSq, dot]
  calc
    (∑ i, (x i - y i) * (x i - y i)) =
        ∑ i, (x i * x i + y i * y i - 2 * (x i * y i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i, x i * x i) + (∑ i, y i * y i) -
        2 * (∑ i, x i * y i) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

lemma normSq_add (x y : Vec3) : normSq (fun i => x i + y i) =
    normSq x + normSq y + 2 * dot x y := by
  simp only [normSq, dot]
  calc
    (∑ i, (x i + y i) * (x i + y i)) =
        ∑ i, (x i * x i + y i * y i + 2 * (x i * y i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i, x i * x i) + (∑ i, y i * y i) +
        2 * (∑ i, x i * y i) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]

lemma dot_abs_le_one {x y : Vec3} (hx : normSq x ≤ 1) (hy : normSq y ≤ 1) :
    |dot x y| ≤ 1 := by
  have hsub : 0 ≤ normSq (fun i => x i - y i) := by
    unfold normSq dot
    apply Finset.sum_nonneg
    intro i hi
    nlinarith [sq_nonneg (x i - y i)]
  have hadd : 0 ≤ normSq (fun i => x i + y i) := by
    unfold normSq dot
    apply Finset.sum_nonneg
    intro i hi
    nlinarith [sq_nonneg (x i + y i)]
  rw [normSq_sub] at hsub
  rw [normSq_add] at hadd
  rw [abs_le]
  constructor <;> nlinarith

lemma latticeDist_comm (x y : Plane) : latticeDist x y = latticeDist y x := by
  unfold latticeDist
  have h1 : x.1 - y.1 = -(y.1 - x.1) := by ring
  have h2 : x.2 - y.2 = -(y.2 - x.2) := by ring
  rw [h1, h2, Int.natAbs_neg, Int.natAbs_neg]

lemma latticeDist_triangle (x y z : Plane) : latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  unfold latticeDist
  have h1 : Int.natAbs (x.1 - z.1) ≤ Int.natAbs (x.1 - y.1) + Int.natAbs (y.1 - z.1) := by
    have heq : x.1 - z.1 = (x.1 - y.1) + (y.1 - z.1) := by ring
    rw [heq]
    exact Int.natAbs_add_le _ _
  have h2 : Int.natAbs (x.2 - z.2) ≤ Int.natAbs (x.2 - y.2) + Int.natAbs (y.2 - z.2) := by
    have heq : x.2 - z.2 = (x.2 - y.2) + (y.2 - z.2) := by ring
    rw [heq]
    exact Int.natAbs_add_le _ _
  omega

lemma shiftedDepth_le {G : Finset Plane} (u v x : Plane) (d s : ℕ)
    (hd : (d : ℕ∞) ≤ min
      (setDistance latticeDist u (↑(protectedSites G) : Set Plane))
      (setDistance latticeDist v (↑(protectedSites G) : Set Plane)))
    (hs : min (latticeDist x u) (latticeDist x v) ≤ s) :
    (((d : ℤ) - (s : ℤ)).toNat : ℕ∞) ≤
      setDistance latticeDist x (↑(protectedSites G) : Set Plane) := by
  let S : Set Plane := ↑(protectedSites G)
  change (((d : ℤ) - (s : ℤ)).toNat : ℕ∞) ≤
    ⨅ z : {z : Plane // z ∈ S}, (latticeDist x z.val : ℕ∞)
  have hdu : (d : ℕ∞) ≤ setDistance latticeDist u S :=
    hd.trans (min_le_left _ _)
  have hdv : (d : ℕ∞) ≤ setDistance latticeDist v S :=
    hd.trans (min_le_right _ _)
  have hds : d ≤ s ∨ s < d := by omega
  have hshift : d ≤ s → ((d : ℤ) - (s : ℤ)).toNat = 0 := by
    intro h
    apply Int.toNat_of_nonpos
    omega
  have hshift' : s < d → ((d : ℤ) - (s : ℤ)).toNat = d - s := by
    intro h
    have hn : 0 ≤ (d : ℤ) - (s : ℤ) := by omega
    have hc : (((d : ℤ) - (s : ℤ)).toNat : ℤ) = ((d - s : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hn]
      rw [Nat.cast_sub h.le]
    exact_mod_cast hc
  apply le_iInf
  intro z
  apply WithTop.coe_le_coe.mpr
  rcases hds with hds | hds
  · rw [hshift hds]
    exact Nat.zero_le _
  · rw [hshift' hds]
    have hduz : d ≤ latticeDist u z.val := by
      apply WithTop.coe_le_coe.mp
      exact hdu.trans (iInf_le (fun z : {z : Plane // z ∈ S} => (latticeDist u z.val : ℕ∞)) z)
    have hdvz : d ≤ latticeDist v z.val := by
      apply WithTop.coe_le_coe.mp
      exact hdv.trans (iInf_le (fun z : {z : Plane // z ∈ S} => (latticeDist v z.val : ℕ∞)) z)
    have htu : latticeDist u z.val ≤ latticeDist x u + latticeDist x z.val := by
      calc
        latticeDist u z.val ≤ latticeDist u x + latticeDist x z.val := latticeDist_triangle _ _ _
        _ = latticeDist x u + latticeDist x z.val := by rw [latticeDist_comm]
    have htv : latticeDist v z.val ≤ latticeDist x v + latticeDist x z.val := by
      calc
        latticeDist v z.val ≤ latticeDist v x + latticeDist x z.val := latticeDist_triangle _ _ _
        _ = latticeDist x v + latticeDist x z.val := by rw [latticeDist_comm]
    have hmin : d ≤ min (latticeDist x u) (latticeDist x v) + latticeDist x z.val := by
      by_cases hx : latticeDist x u ≤ latticeDist x v
      · rw [min_eq_left hx]
        omega
      · rw [min_eq_right (le_of_lt (lt_of_not_ge hx))]
        omega
    omega

lemma networkSpin_normSq_le_one {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) (x : Plane) : normSq (D.spins n x) ≤ 1 := by
  by_cases hx : x ∈ D.active
  · simpa [Network.spins, hx] using spinVector_normSq_le_one (n ⟨x, hx⟩)
  · simp [Network.spins, hx, normSq, dot]

lemma active_status_cases {G : Finset Plane} (D : Network G) {x : Plane}
    (hx : x ∈ D.active) : D.status x = .U ∨ D.status x = .D := by
  have hne : D.status x ≠ .X := (Finset.mem_filter.mp hx).2
  cases h : D.status x <;> simp_all

lemma spinWeight_nonneg (s : Status) (hs : s = .U ∨ s = .D) (j : SpinLetter) :
    0 ≤ spinWeight s j := by
  cases j <;> cases s <;> simp_all [spinWeight]
  all_goals norm_num

lemma networkBondFactor_nonneg {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) {e : Plane × Plane} (he : e ∈ D.bonds) :
    0 ≤ 1 + dot (D.spins n e.1) (D.spins n e.2) := by
  have hp : D.Present e.1 e.2 := by
    exact (Finset.mem_filter.mp (show e ∈ (internalBonds G).filter (fun e => D.Present e.1 e.2) from by
      simpa [Network.bonds] using he)).2
  have hdot := dot_abs_le_one (networkSpin_normSq_le_one D n e.1)
    (networkSpin_normSq_le_one D n e.2)
  have hlow : -1 ≤ dot (D.spins n e.1) (D.spins n e.2) := (abs_le.mp hdot).1
  linarith

lemma networkPinFactor_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (n : (x : D.active) → SpinLetter) (pinned : Bool) (e : originalLegs G) :
    0 ≤ if pinned = true ∧ e.val.1 ∈ D.active then
      1 + dot (τ e).val (D.spins n e.val.1) else 1 := by
  by_cases h : pinned = true ∧ e.val.1 ∈ D.active
  · simp only [if_pos h]
    have hdot := dot_abs_le_one (le_of_eq (τ e).property)
      (networkSpin_normSq_le_one D n e.val.1)
    linarith [(abs_le.mp hdot).1]
  · simp only [if_neg h]
    norm_num

def networkWeight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (n : (x : D.active) → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
    (∏ e : originalLegs G,
      if pinned = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins n e.val.1) else 1)

lemma networkWeight_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (n : (x : D.active) → SpinLetter) : 0 ≤ networkWeight D τ pinned n := by
  unfold networkWeight
  apply mul_nonneg
  · apply mul_nonneg
    · apply Finset.prod_nonneg
      intro x hx
      exact spinWeight_nonneg _ (active_status_cases D x.property) (n x)
    · apply Finset.prod_nonneg
      intro e he
      exact networkBondFactor_nonneg D n he
  · apply Finset.prod_nonneg
    intro e he
    exact networkPinFactor_nonneg D τ n pinned e

lemma partition_eq_weight_sum {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ pinned f = ∑ n : (x : D.active) → SpinLetter,
      networkWeight D τ pinned n * f (D.spins n) := by
  unfold Network.partition
  apply Finset.sum_congr rfl
  intro n hn
  unfold networkWeight
  ac_rfl

lemma partition_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) : 0 ≤ D.partition τ pinned (fun _ => 1) := by
  rw [partition_eq_weight_sum]
  simp only [mul_one]
  exact Finset.sum_nonneg (fun n hn => networkWeight_nonneg D τ pinned n)

lemma partition_observable_abs_le {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (a b : Plane) :
    |D.partition τ pinned (fun n => dot (n a) (n b))| ≤ D.partition τ pinned (fun _ => 1) := by
  rw [partition_eq_weight_sum, partition_eq_weight_sum]
  simp only [mul_one]
  calc
    |∑ n : (x : D.active) → SpinLetter,
        networkWeight D τ pinned n * dot (D.spins n a) (D.spins n b)| ≤
        ∑ n : (x : D.active) → SpinLetter,
          |networkWeight D τ pinned n * dot (D.spins n a) (D.spins n b)| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n : (x : D.active) → SpinLetter, networkWeight D τ pinned n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul, abs_of_nonneg (networkWeight_nonneg D τ pinned n)]
      calc
        networkWeight D τ pinned n * |dot (D.spins n a) (D.spins n b)| ≤
            networkWeight D τ pinned n * 1 :=
              mul_le_mul_of_nonneg_left
                (dot_abs_le_one (networkSpin_normSq_le_one D n a)
                  (networkSpin_normSq_le_one D n b))
                (networkWeight_nonneg D τ pinned n)
        _ = networkWeight D τ pinned n := by ring

lemma networkExpectation_abs_le_one {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) (a b : Plane) :
    |D.expectation τ pinned (fun n => dot (n a) (n b))| ≤ 1 := by
  let num := D.partition τ pinned (fun n => dot (n a) (n b))
  let den := D.partition τ pinned (fun _ => 1)
  have hden : 0 ≤ den := by exact partition_nonneg D τ pinned
  have hnum : |num| ≤ den := by exact partition_observable_abs_le D τ pinned a b
  change |num / den| ≤ 1
  by_cases hzero : den = 0
  · have hnumzero : num = 0 := abs_eq_zero.mp (le_antisymm (by simpa [hzero] using hnum) (abs_nonneg _))
    simp [hzero, hnumzero]
  · have hpos : 0 < den := lt_of_le_of_ne hden (Ne.symm hzero)
    rw [abs_div, abs_of_pos hpos]
    apply (div_le_iff₀ hpos).2
    simpa using hnum

lemma response_abs_le_two {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (X : PairType) (a b c : Plane) (_hp : D.ResponsePair X a b c) :
    |D.expectation τ true (fun n => dot (n a) (n b)) -
      D.expectation τ false (fun n => dot (n a) (n b))| ≤ 2 := by
  have ht := networkExpectation_abs_le_one D τ true a b
  have hf := networkExpectation_abs_le_one D τ false a b
  calc
    |D.expectation τ true (fun n => dot (n a) (n b)) -
        D.expectation τ false (fun n => dot (n a) (n b))| ≤
        |D.expectation τ true (fun n => dot (n a) (n b))| +
          |D.expectation τ false (fun n => dot (n a) (n b))| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add ht hf
    _ = 2 := by norm_num

lemma responseEnvelope_bddAbove (X : PairType) (d : ℤ) :
    BddAbove ({0} ∪ {r | ∃ G : Finset Plane, ∃ τ : PinAssignment G, ∃ D : Network G,
      ∃ a b c : Plane, D.ResponsePair X a b c ∧
      (d.toNat : ℕ∞) ≤ min
        (setDistance latticeDist a (↑(protectedSites G) : Set Plane))
        (setDistance latticeDist b (↑(protectedSites G) : Set Plane)) ∧
      r = |D.expectation τ true (fun n => dot (n a) (n b)) -
        D.expectation τ false (fun n => dot (n a) (n b))|}) := by
  refine ⟨2, ?_⟩
  intro r hr
  simp only [Set.mem_union] at hr
  rcases hr with hr0 | hr
  · simp only [Set.mem_singleton_iff] at hr0
    rw [hr0]
    norm_num
  · rcases hr with ⟨G, τ, D, a, b, c, hp, hdepth, rfl⟩
    exact response_abs_le_two D τ X a b c hp


theorem main : AKLT.Blueprint.Rec.PairEnvelopeShiftStatement := by
  intro G τ E X a b c hpair u v d hd
  let s := max (min (latticeDist a u) (latticeDist a v))
    (min (latticeDist b u) (latticeDist b v))
  let R := |E.expectation τ true (fun n => dot (n a) (n b)) -
    E.expectation τ false (fun n => dot (n a) (n b))|
  have hsa : min (latticeDist a u) (latticeDist a v) ≤ s := le_max_left _ _
  have hsb : min (latticeDist b u) (latticeDist b v) ≤ s := le_max_right _ _
  have hda := shiftedDepth_le u v a d s hd hsa
  have hdb := shiftedDepth_le u v b d s hd hsb
  have hdepth : (((d : ℤ) - (s : ℤ)).toNat : ℕ∞) ≤
      min (setDistance latticeDist a (↑(protectedSites G) : Set Plane))
        (setDistance latticeDist b (↑(protectedSites G) : Set Plane)) :=
    le_min hda hdb
  have hmem : R ∈ ({0} ∪ {r | ∃ G : Finset Plane, ∃ τ : PinAssignment G,
      ∃ D : Network G, ∃ a b c : Plane, D.ResponsePair X a b c ∧
      (((d : ℤ) - (s : ℤ)).toNat : ℕ∞) ≤
        min (setDistance latticeDist a (↑(protectedSites G) : Set Plane))
          (setDistance latticeDist b (↑(protectedSites G) : Set Plane)) ∧
      r = |D.expectation τ true (fun n => dot (n a) (n b)) -
        D.expectation τ false (fun n => dot (n a) (n b))|}) := by
    simp only [Set.mem_union]
    right
    exact ⟨G, τ, E, a, b, c, hpair, hdepth, rfl⟩
  have hle : R ≤ sSup ({0} ∪ {r | ∃ G : Finset Plane, ∃ τ : PinAssignment G,
      ∃ D : Network G, ∃ a b c : Plane, D.ResponsePair X a b c ∧
      (((d : ℤ) - (s : ℤ)).toNat : ℕ∞) ≤
        min (setDistance latticeDist a (↑(protectedSites G) : Set Plane))
          (setDistance latticeDist b (↑(protectedSites G) : Set Plane)) ∧
      r = |D.expectation τ true (fun n => dot (n a) (n b)) -
        D.expectation τ false (fun n => dot (n a) (n b))|}) :=
    le_csSup (responseEnvelope_bddAbove X ((d : ℤ) - (s : ℤ))) hmem
  simpa [R, s, responseEnvelope] using hle

end AKLT.W.REC078
