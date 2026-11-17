module
public import AKLT.Blueprint.H1.NodesLeaf

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M003

private lemma sf_const (s : Status) (c : ℝ) :
    siteFunctional s (fun _ : Vec3 => c) = c * siteFunctional s (fun _ => 1) := by
  simp only [siteFunctional]
  calc
    (∑ j, spinWeight s j * c) = ∑ j, c * spinWeight s j := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = c * ∑ j, spinWeight s j := by rw [Finset.mul_sum]
    _ = c * siteFunctional s (fun _ => 1) := by simp [siteFunctional]

private lemma sf_add (s : Status) (f g : Vec3 → ℝ) :
    siteFunctional s (fun n => f n + g n) = siteFunctional s f + siteFunctional s g := by
  simp [siteFunctional, Finset.sum_add_distrib, mul_add]

private lemma sf_sum {ι : Type*} [Fintype ι] (s : Status) (f : ι → Vec3 → ℝ) :
    siteFunctional s (fun n => ∑ i, f i n) = ∑ i, siteFunctional s (f i) := by
  simp only [siteFunctional]
  calc
    (∑ j, spinWeight s j * ∑ i, f i (spinVector j)) =
        ∑ j, ∑ i, spinWeight s j * f i (spinVector j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, spinWeight s j * f i (spinVector j) := Finset.sum_comm

private lemma sf_mul_const (s : Status) (c : ℝ) (f : Vec3 → ℝ) :
    siteFunctional s (fun n => c * f n) = c * siteFunctional s f := by
  simp only [siteFunctional]
  calc
    (∑ j, spinWeight s j * (c * f (spinVector j))) =
        ∑ j, c * (spinWeight s j * f (spinVector j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = c * ∑ j, spinWeight s j * f (spinVector j) := by rw [Finset.mul_sum]

private lemma sf_mul_const_right (s : Status) (c : ℝ) (f : Vec3 → ℝ) :
    siteFunctional s (fun n => f n * c) = siteFunctional s f * c := by
  rw [show (fun n => f n * c) = fun n => c * f n by
    funext n
    ring]
  rw [sf_mul_const]
  ring

private def secondMoment (s : Status) : ℝ := if s = .U then 1 / 3 else 1 / 5

private lemma sf_one (hM : AKLT.Blueprint.H1.MonomialMoments) (s : Status)
    (hs : s = .U ∨ s = .D) : siteFunctional s (fun _ : Vec3 => 1) = 1 := by
  have h := hM (fun _ : Fin 3 => 0) (by simp) s hs
  simpa [AKLT.Blueprint.H1.MonomialMoments, AKLT.Defs.rationalStatusMoment,
    AKLT.Defs.rationalMoment] using h

private lemma sf_coord (hM : AKLT.Blueprint.H1.MonomialMoments) (s : Status)
    (hs : s = .U ∨ s = .D) (i : Fin 3) :
    siteFunctional s (fun n => n i) = 0 := by
  let m : Fin 3 → ℕ := fun k => if k = i then 1 else 0
  have hdeg : (∑ k, m k) ≤ 4 := by
    rw [show (∑ k, m k) = 1 by simp [m]]
    norm_num
  have h := hM m hdeg s hs
  fin_cases i <;>
    simpa [m, AKLT.Blueprint.H1.MonomialMoments, AKLT.Defs.rationalStatusMoment,
      AKLT.Defs.rationalMoment, Fintype.sum_ite_eq', Fintype.prod_ite_eq'] using h

private lemma sf_coord_mul (hM : AKLT.Blueprint.H1.MonomialMoments) (s : Status)
    (hs : s = .U ∨ s = .D) (i j : Fin 3) :
    siteFunctional s (fun n => n i * n j) = (if i = j then secondMoment s else 0) := by
  let m : Fin 3 → ℕ := fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0)
  have hdeg : (∑ k, m k) ≤ 4 := by
    rw [show (∑ k, m k) = 2 by simp [m, Finset.sum_add_distrib]]
    norm_num
  have h := hM m hdeg s hs
  cases s with
  | U =>
    have hsU : Status.U = .U ∨ Status.U = .D := Or.inl rfl
    clear hs
    fin_cases i <;> fin_cases j <;>
      norm_num [m, secondMoment, AKLT.Blueprint.H1.MonomialMoments,
        AKLT.Defs.rationalStatusMoment, AKLT.Defs.rationalMoment,
        Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.exists_iff_succ,
        Finset.sum_add_distrib, pow_add] at h ⊢ <;>
      first | exact h | simpa [mul_comm] using h
  | D =>
    have hsD : Status.D = .U ∨ Status.D = .D := Or.inr rfl
    clear hs
    fin_cases i <;> fin_cases j <;>
      norm_num [m, secondMoment, AKLT.Blueprint.H1.MonomialMoments,
        AKLT.Defs.rationalStatusMoment, AKLT.Defs.rationalMoment,
        Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.exists_iff_succ,
        Finset.sum_add_distrib, pow_add] at h ⊢ <;>
      first | exact h | simpa [mul_comm] using h
  | X => cases hs with
    | inl h => cases h
    | inr h => cases h

private lemma sf_dot (hM : AKLT.Blueprint.H1.MonomialMoments) (s : Status)
    (hs : s = .U ∨ s = .D) (a : Vec3) :
    siteFunctional s (fun n => dot n a) = 0 := by
  change siteFunctional s (fun n => ∑ i : Fin 3, n i * a i) = 0
  rw [sf_sum]
  simp_rw [sf_mul_const_right]
  simp_rw [sf_coord hM s hs]
  simp

private lemma sf_dot_dot (hM : AKLT.Blueprint.H1.MonomialMoments) (s : Status)
    (hs : s = .U ∨ s = .D) (a b : Vec3) :
    siteFunctional s (fun n => dot n a * dot n b) = secondMoment s * dot a b := by
  have hexp : ∀ n : Vec3,
      dot n a * dot n b = ∑ i : Fin 3, ∑ j : Fin 3,
        (a j * b i) * (n j * n i) := by
    intro n
    simp only [dot, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hfun : (fun n : Vec3 => dot n a * dot n b) = fun n =>
      ∑ i : Fin 3, ∑ j : Fin 3, (a j * b i) * (n j * n i) := by
    funext n
    exact hexp n
  rw [hfun]
  rw [sf_sum]
  simp_rw [sf_sum]
  simp_rw [sf_mul_const, sf_coord_mul hM s hs]
  by_cases hU : s = .U
  · simp [secondMoment, hU, dot]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · simp [secondMoment, hU, dot]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

private lemma sf_coord_dot (hM : AKLT.Blueprint.H1.MonomialMoments) (s : Status)
    (hs : s = .U ∨ s = .D) (i : Fin 3) (a : Vec3) :
    siteFunctional s (fun n => n i * dot n a) = secondMoment s * a i := by
  have hexp : ∀ n : Vec3, n i * dot n a =
      ∑ j : Fin 3, a j * (n i * n j) := by
    intro n
    simp only [dot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hfun : (fun n : Vec3 => n i * dot n a) = fun n =>
      ∑ j : Fin 3, a j * (n i * n j) := by
    funext n
    exact hexp n
  rw [hfun]
  rw [sf_sum]
  simp_rw [sf_mul_const, sf_coord_mul hM s hs]
  by_cases hU : s = .U <;> simp [secondMoment, hU] <;> ring

private lemma sf_coord3 (hM : AKLT.Blueprint.H1.MonomialMoments) (s : Status)
    (hs : s = .U ∨ s = .D) (i j k : Fin 3) :
    siteFunctional s (fun n => n i * n j * n k) = 0 := by
  let m : Fin 3 → ℕ := fun x =>
    (if x = i then 1 else 0) + (if x = j then 1 else 0) + (if x = k then 1 else 0)
  have hdeg : (∑ x, m x) ≤ 4 := by
    rw [show (∑ x, m x) = 3 by simp [m, Finset.sum_add_distrib]]
    norm_num
  have hsum : (∑ x, m x) = 3 := by simp [m, Finset.sum_add_distrib]
  have h := hM m hdeg s hs
  have hzero : siteFunctional s (fun n => ∏ x : Fin 3, n x ^ m x) = 0 := by
    simpa [AKLT.Defs.rationalStatusMoment, AKLT.Defs.rationalMoment, hsum] using h
  have hfun : (fun n : Vec3 => n i * n j * n k) =
      fun n => ∏ x : Fin 3, n x ^ m x := by
    funext n
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [m, Fin.prod_univ_succ, pow_add] <;> ring
  rw [hfun]
  exact hzero

private lemma sf_coord_dot_dot (hM : AKLT.Blueprint.H1.MonomialMoments) (s : Status)
    (hs : s = .U ∨ s = .D) (i : Fin 3) (a b : Vec3) :
    siteFunctional s (fun n => n i * dot n a * dot n b) = 0 := by
  have hexp : ∀ n : Vec3, n i * dot n a * dot n b =
      ∑ j : Fin 3, ∑ k : Fin 3, (a k * b j) * (n i * n k * n j) := by
    intro n
    simp only [dot, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hfun : (fun n : Vec3 => n i * dot n a * dot n b) = fun n =>
      ∑ j : Fin 3, ∑ k : Fin 3, (a k * b j) * (n i * n k * n j) := by
    funext n
    exact hexp n
  rw [hfun]
  rw [sf_sum]
  simp_rw [sf_sum, sf_mul_const, sf_coord3 hM s hs]
  simp

private lemma slotProduct_eq (a : Fin 2 → UnitVector) (n : Vec3) :
    localProduct (fun j => (a j).val) n =
      (1 + dot n (a 0).val) * (1 + dot n (a 1).val) := by
  simp [localProduct, Fin.prod_univ_succ]

private lemma slotNormalizer (hM : AKLT.Blueprint.H1.MonomialMoments) (s : Status)
    (hs : s = .U ∨ s = .D) (a : Fin 2 → UnitVector) :
    siteFunctional s (localProduct fun j => (a j).val) =
      1 + secondMoment s * dot (a 0).val (a 1).val := by
  have hLocal : (fun n : Vec3 => localProduct (fun j => (a j).val) n) =
      fun n => (1 + dot n (a 0).val) * (1 + dot n (a 1).val) := by
    funext n
    exact slotProduct_eq a n
  change siteFunctional s (fun n => localProduct (fun j => (a j).val) n) = _
  rw [hLocal]
  have hexpand : (fun n : Vec3 => (1 + dot n (a 0).val) *
      (1 + dot n (a 1).val)) = fun n =>
        1 + dot n (a 0).val + dot n (a 1).val +
          dot n (a 0).val * dot n (a 1).val := by
    funext n
    ring
  rw [hexpand, sf_add, sf_add, sf_add]
  simp [sf_one hM s hs, sf_dot hM s hs, sf_dot_dot hM s hs]

private lemma slotNumerator (hM : AKLT.Blueprint.H1.MonomialMoments) (s : Status)
    (hs : s = .U ∨ s = .D) (a : Fin 2 → UnitVector) (i : Fin 3) :
    siteFunctional s (fun n => n i * localProduct (fun j => (a j).val) n) =
      secondMoment s * ((a 0).val i + (a 1).val i) := by
  have hLocal : (fun n : Vec3 => n i * localProduct (fun j => (a j).val) n) =
      fun n => n i * ((1 + dot n (a 0).val) * (1 + dot n (a 1).val)) := by
    funext n
    rw [slotProduct_eq]
  rw [hLocal]
  have hexpand : (fun n : Vec3 => n i *
      ((1 + dot n (a 0).val) * (1 + dot n (a 1).val))) = fun n =>
        (n i + n i * dot n (a 0).val + n i * dot n (a 1).val) +
          n i * dot n (a 0).val * dot n (a 1).val := by
    funext n
    ring
  rw [hexpand, sf_add, sf_add, sf_add]
  simp [sf_coord hM s hs, sf_coord_dot hM s hs,
    sf_coord_dot_dot hM s hs]
  ring

private lemma dot_comm' (a b : Vec3) : dot a b = dot b a := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma dot_add_left' (a b c : Vec3) :
    dot (fun i => a i + b i) c = dot a c + dot b c := by
  unfold dot
  simp [add_mul, Finset.sum_add_distrib]

private lemma dot_add_right' (a b c : Vec3) :
    dot a (fun i => b i + c i) = dot a b + dot a c := by
  unfold dot
  simp [mul_add, Finset.sum_add_distrib]

private lemma dot_sub_left' (a b c : Vec3) :
    dot (fun i => a i - b i) c = dot a c - dot b c := by
  unfold dot
  simp [sub_mul, Finset.sum_sub_distrib]

private lemma dot_sub_right' (a b c : Vec3) :
    dot a (fun i => b i - c i) = dot a b - dot a c := by
  unfold dot
  simp [mul_sub, Finset.sum_sub_distrib]

private lemma normSq_add' (a b : Vec3) :
    normSq (fun i => a i + b i) = normSq a + 2 * dot a b + normSq b := by
  unfold normSq
  calc
    dot (fun i => a i + b i) (fun i => a i + b i) =
        dot a a + dot a b + dot b a + dot b b := by
          rw [dot_add_left', dot_add_right', dot_add_right']
          ring
    _ = dot a a + 2 * dot a b + dot b b := by rw [dot_comm' b a]; ring

private lemma normSq_sub' (a b : Vec3) :
    normSq (fun i => a i - b i) = normSq a - 2 * dot a b + normSq b := by
  unfold normSq
  calc
    dot (fun i => a i - b i) (fun i => a i - b i) =
        dot a a - dot a b - dot b a + dot b b := by
          rw [dot_sub_left', dot_sub_right', dot_sub_right']
          ring
    _ = dot a a - 2 * dot a b + dot b b := by rw [dot_comm' b a]; ring

private lemma normSq_nonneg' (x : Vec3) : 0 ≤ normSq x := by
  unfold normSq dot
  apply Finset.sum_nonneg
  intro i hi
  nlinarith [sq_nonneg (x i)]

private lemma normSq_scale_div (x : Vec3) (c d : ℝ) (hd : d ≠ 0) :
    normSq (fun i => c * x i / d) = c ^ 2 * normSq x / d ^ 2 := by
  unfold normSq dot
  simp only [Fin.sum_univ_succ]
  field_simp
  ring

theorem main : AKLT.Blueprint.H1.CornerMeanBoundsStatement := by
  intro hM a s hs
  let x : Vec3 := (a 0).val
  let y : Vec3 := (a 1).val
  let t : ℝ := dot x y
  let A : ℝ := siteFunctional s (localProduct fun j => (a j).val)
  have hx : normSq x = 1 := (a 0).property
  have hy : normSq y = 1 := (a 1).property
  have hsum : normSq (fun i => x i + y i) = 2 + 2 * t := by
    rw [normSq_add', hx, hy]
    dsimp [t]
    ring
  have htlo : -1 ≤ t := by
    have hn := normSq_nonneg' (fun i => x i + y i)
    rw [hsum] at hn
    dsimp [t]
    linarith
  have hthi : t ≤ 1 := by
    have hn := normSq_nonneg' (fun i => x i - y i)
    rw [normSq_sub'] at hn
    rw [hx, hy] at hn
    dsimp [t]
    linarith
  have hAval : A = 1 + secondMoment s * t := by
    dsimp [A, t]
    exact slotNormalizer hM s hs a
  have hApos : 0 < A := by
    rw [hAval]
    by_cases hU : s = .U
    · simp [secondMoment, hU]
      nlinarith [htlo]
    · simp [secondMoment, hU]
      nlinarith [htlo]
  have hMean : localMean s (fun j => (a j).val) =
      fun i => secondMoment s * (x i + y i) / A := by
    funext i
    simp only [localMean]
    rw [slotNumerator hM s hs a i]
  have hMeanSq : normSq (localMean s (fun j => (a j).val)) =
      secondMoment s ^ 2 * normSq (fun i => x i + y i) / A ^ 2 := by
    rw [hMean]
    exact normSq_scale_div (fun i => x i + y i) (secondMoment s) A (ne_of_gt hApos)
  rcases hs with hsU | hsD
  · subst s
    have hAeq : A = 1 + (1 / 3 : ℝ) * t := by simpa [secondMoment] using hAval
    have hfactor : A ^ 2 - 4 * ((1 / 3 : ℝ) ^ 2 * (2 + 2 * t)) =
        (1 - t) ^ 2 / 9 := by rw [hAeq]; ring
    have hfac : 4 * ((1 / 3 : ℝ) ^ 2 * (2 + 2 * t)) ≤ A ^ 2 := by
      nlinarith [hfactor, sq_nonneg (1 - t)]
    have hquot : ((1 / 3 : ℝ) ^ 2 * (2 + 2 * t)) / A ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hApos)).2
      nlinarith [hfac]
    constructor
    · exact hApos
    · rw [hMeanSq, hsum]
      simpa [secondMoment] using hquot
  · subst s
    have hAeq : A = 1 + (1 / 5 : ℝ) * t := by simpa [secondMoment] using hAval
    have hfactor : A ^ 2 - 9 * ((1 / 5 : ℝ) ^ 2 * (2 + 2 * t)) =
        ((1 - t) * (7 - t)) / 25 := by rw [hAeq]; ring
    have hprod : 0 ≤ (1 - t) * (7 - t) :=
      mul_nonneg (by linarith [hthi]) (by linarith [hthi])
    have hfac : 9 * ((1 / 5 : ℝ) ^ 2 * (2 + 2 * t)) ≤ A ^ 2 := by
      nlinarith [hfactor, hprod]
    have hquot : ((1 / 5 : ℝ) ^ 2 * (2 + 2 * t)) / A ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hApos)).2
      nlinarith [hfac]
    constructor
    · exact hApos
    · rw [hMeanSq, hsum]
      simpa [secondMoment] using hquot

end AKLT.W.H1M003
