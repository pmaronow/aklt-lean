module
public import AKLT.Blueprint.H1.NodesPassage
public import AKLT.Blueprint.Mom.Assembly

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M005

private def e₁ (i : Fin 3) : Fin 3 → ℕ := fun k => if k = i then 1 else 0

private lemma prod_pow_add (x : Fin 3 → ℝ) (m q : Fin 3 → ℕ) :
    (∏ k, x k ^ (m k + q k)) = (∏ k, x k ^ m k) * (∏ k, x k ^ q k) := by
  simp_rw [pow_add]
  rw [Finset.prod_mul_distrib]

private lemma prod_pow_e₁ (x : Fin 3 → ℝ) (i : Fin 3) :
    (∏ k, x k ^ e₁ i k) = x i := by
  classical
  simp [e₁]

private lemma prod_pow_e₁₂ (x : Fin 3 → ℝ) (i j : Fin 3) :
    (∏ k, x k ^ (e₁ i k + e₁ j k)) = x i * x j := by
  rw [prod_pow_add, prod_pow_e₁, prod_pow_e₁]

private lemma prod_pow_e₁₂₃ (x : Fin 3 → ℝ) (i j k : Fin 3) :
    (∏ l, x l ^ (e₁ i l + e₁ j l + e₁ k l)) = x i * x j * x k := by
  rw [prod_pow_add, prod_pow_e₁₂, prod_pow_e₁]

private lemma coordMoments (hM : AKLT.Blueprint.H1.MonomialMoments) :
    (∀ i, siteFunctional .U (fun n => n i) = 0) ∧
    (∀ i j, siteFunctional .U (fun n => n i * n j) = if i = j then 1 / 3 else 0) ∧
    (∀ i j k, siteFunctional .U (fun n => n i * n j * n k) = 0) ∧
    (∀ i, siteFunctional .D (fun n => n i) = 0) ∧
    (∀ i j, siteFunctional .D (fun n => n i * n j) = if i = j then 1 / 5 else 0) := by
  have hU := fun m hm => hM m hm Status.U (Or.inl rfl)
  have hD := fun m hm => hM m hm Status.D (Or.inr rfl)
  constructor
  · intro i
    have h := hU (e₁ i) (by simp [e₁])
    have he : (fun n : Vec3 => ∏ k, n k ^ e₁ i k) = fun n => n i := by
      funext n
      exact prod_pow_e₁ n i
    rw [he] at h
    simpa [rationalStatusMoment, rationalMoment, e₁] using h
  constructor
  · intro i j
    by_cases hij : i = j
    · subst j
      have hs : (∑ k, (e₁ i k + e₁ i k)) = 2 := by
        have hsingle : (∑ k, e₁ i k) = 1 := by simp [e₁]
        calc
          (∑ k, (e₁ i k + e₁ i k)) = (∑ k, e₁ i k) + ∑ k, e₁ i k :=
            Finset.sum_add_distrib
          _ = 1 + 1 := by rw [hsingle]
          _ = 2 := by norm_num
      have h := hU (fun k => e₁ i k + e₁ i k) (by rw [hs]; norm_num)
      have he : (fun n : Vec3 => ∏ k, n k ^ (e₁ i k + e₁ i k)) = fun n => n i * n i := by
        funext n
        simpa [two_mul] using prod_pow_e₁₂ n i i
      rw [he] at h
      have hex : ∃ k, e₁ i k + e₁ i k = 2 := ⟨i, by simp [e₁]⟩
      have hval : rationalStatusMoment Status.U (fun k => e₁ i k + e₁ i k) = 1 / 3 := by
        unfold rationalStatusMoment rationalMoment
        rw [hs]
        simp [hex]
      rw [hval] at h
      simpa using h
    · have hs : (∑ k, (e₁ i k + e₁ j k)) = 2 := by
        have hi : (∑ k, e₁ i k) = 1 := by simp [e₁]
        have hj : (∑ k, e₁ j k) = 1 := by simp [e₁]
        calc
          (∑ k, (e₁ i k + e₁ j k)) = (∑ k, e₁ i k) + ∑ k, e₁ j k :=
            Finset.sum_add_distrib
          _ = 1 + 1 := by rw [hi, hj]
          _ = 2 := by norm_num
      have h := hU (fun k => e₁ i k + e₁ j k) (by rw [hs]; norm_num)
      have he : (fun n : Vec3 => ∏ k, n k ^ (e₁ i k + e₁ j k)) = fun n => n i * n j := by
        funext n
        exact prod_pow_e₁₂ n i j
      rw [he] at h
      have hno : ¬ ∃ k, e₁ i k + e₁ j k = 2 := by
        rintro ⟨k, hk⟩
        by_cases hki : k = i
        · subst k
          simp [e₁, hij] at hk
        · by_cases hkj : k = j
          · subst k
            norm_num [e₁, hki] at hk
          · simp [e₁, hki, hkj] at hk
      have hval : rationalStatusMoment Status.U (fun k => e₁ i k + e₁ j k) = 0 := by
        unfold rationalStatusMoment rationalMoment
        rw [hs]
        simp [hno]
      rw [hval] at h
      simpa [hij] using h
  constructor
  · intro i j k
    have hs : (∑ l, (e₁ i l + e₁ j l + e₁ k l)) = 3 := by
      have hi : (∑ l, e₁ i l) = 1 := by simp [e₁]
      have hj : (∑ l, e₁ j l) = 1 := by simp [e₁]
      have hk : (∑ l, e₁ k l) = 1 := by simp [e₁]
      calc
        (∑ l, (e₁ i l + e₁ j l + e₁ k l)) =
            ((∑ l, e₁ i l) + ∑ l, e₁ j l) + ∑ l, e₁ k l := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        _ = (1 + 1) + 1 := by rw [hi, hj, hk]
        _ = 3 := by norm_num
    have h := hU (fun l => e₁ i l + e₁ j l + e₁ k l) (by rw [hs]; norm_num)
    have he : (fun n : Vec3 => ∏ l, n l ^ (e₁ i l + e₁ j l + e₁ k l)) =
        fun n => n i * n j * n k := by
      funext n
      exact prod_pow_e₁₂₃ n i j k
    rw [he] at h
    have hval : rationalStatusMoment Status.U (fun l => e₁ i l + e₁ j l + e₁ k l) = 0 := by
      unfold rationalStatusMoment rationalMoment
      rw [hs]
      norm_num
    rw [hval] at h
    simpa using h
  constructor
  · intro i
    have h := hD (e₁ i) (by simp [e₁])
    have he : (fun n : Vec3 => ∏ k, n k ^ e₁ i k) = fun n => n i := by
      funext n
      exact prod_pow_e₁ n i
    rw [he] at h
    simpa [rationalStatusMoment, rationalMoment, e₁] using h
  · intro i j
    by_cases hij : i = j
    · subst j
      have hs : (∑ k, (e₁ i k + e₁ i k)) = 2 := by
        have hsingle : (∑ k, e₁ i k) = 1 := by simp [e₁]
        calc
          (∑ k, (e₁ i k + e₁ i k)) = (∑ k, e₁ i k) + ∑ k, e₁ i k :=
            Finset.sum_add_distrib
          _ = 1 + 1 := by rw [hsingle]
          _ = 2 := by norm_num
      have h := hD (fun k => e₁ i k + e₁ i k) (by rw [hs]; norm_num)
      have he : (fun n : Vec3 => ∏ k, n k ^ (e₁ i k + e₁ i k)) = fun n => n i * n i := by
        funext n
        simpa [two_mul] using prod_pow_e₁₂ n i i
      rw [he] at h
      have hex : ∃ k, e₁ i k + e₁ i k = 2 := ⟨i, by simp [e₁]⟩
      have hval : rationalStatusMoment Status.D (fun k => e₁ i k + e₁ i k) = 1 / 5 := by
        have hpos : Status.D = Status.D ∧ (∑ k, (e₁ i k + e₁ i k)) ≠ 0 := by
          rw [hs]
          norm_num
        unfold rationalStatusMoment
        rw [ite_eq_left hpos]
        unfold rationalMoment
        rw [hs]
        norm_num [hex]
      rw [hval] at h
      simpa using h
    · have hs : (∑ k, (e₁ i k + e₁ j k)) = 2 := by
        have hi : (∑ k, e₁ i k) = 1 := by simp [e₁]
        have hj : (∑ k, e₁ j k) = 1 := by simp [e₁]
        calc
          (∑ k, (e₁ i k + e₁ j k)) = (∑ k, e₁ i k) + ∑ k, e₁ j k :=
            Finset.sum_add_distrib
          _ = 1 + 1 := by rw [hi, hj]
          _ = 2 := by norm_num
      have h := hD (fun k => e₁ i k + e₁ j k) (by rw [hs]; norm_num)
      have he : (fun n : Vec3 => ∏ k, n k ^ (e₁ i k + e₁ j k)) = fun n => n i * n j := by
        funext n
        exact prod_pow_e₁₂ n i j
      rw [he] at h
      have hno : ¬ ∃ k, e₁ i k + e₁ j k = 2 := by
        rintro ⟨k, hk⟩
        by_cases hki : k = i
        · subst k
          simp [e₁, hij] at hk
        · by_cases hkj : k = j
          · subst k
            norm_num [e₁, hki] at hk
          · simp [e₁, hki, hkj] at hk
      have hval : rationalStatusMoment Status.D (fun k => e₁ i k + e₁ j k) = 0 := by
        have hpos : Status.D = Status.D ∧ (∑ k, (e₁ i k + e₁ j k)) ≠ 0 := by
          rw [hs]
          norm_num
        unfold rationalStatusMoment
        rw [ite_eq_left hpos]
        unfold rationalMoment
        rw [hs]
        simp [hno]
      rw [hval] at h
      simpa [hij] using h

private lemma sf_add (s : Status) (f g : Vec3 → ℝ) :
    siteFunctional s (fun n => f n + g n) = siteFunctional s f + siteFunctional s g := by
  simp [siteFunctional, Finset.sum_add_distrib, mul_add]

private lemma sf_const (hM : AKLT.Blueprint.H1.MonomialMoments)
    (s : Status) (hs : s = .U ∨ s = .D) :
    siteFunctional s (fun _ : Vec3 => 1) = 1 := by
  have h := hM (fun _ : Fin 3 => 0) (by simp) s hs
  have he : (fun n : Vec3 => ∏ i, n i ^ (0 : ℕ)) = fun _ => 1 := by
    funext n
    simp
  rw [he] at h
  simpa [rationalStatusMoment, rationalMoment] using h

private lemma sf_dot (s : Status) (h1 : ∀ i, siteFunctional s (fun n => n i) = 0)
    (a : Vec3) : siteFunctional s (fun n => dot n a) = 0 := by
  have he : (fun n => dot n a) = fun n => ∑ i : Fin 3, a i * n i := by
    funext n
    unfold dot
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he, AKLT.Blueprint.Mom.siteFunctional_sum]
  simp [h1]

private lemma sf_dot_dot (s : Status) (ρ : ℝ)
    (h2 : ∀ i j, siteFunctional s (fun n => n i * n j) = if i = j then ρ else 0)
    (a b : Vec3) :
    siteFunctional s (fun n => dot n a * dot n b) = ρ * dot a b := by
  have hdot (n : Vec3) (a : Vec3) : dot n a = ∑ i : Fin 3, a i * n i := by
    unfold dot
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hexp (n : Vec3) : dot n a * dot n b =
      ∑ i : Fin 3, ∑ j : Fin 3, (a j * b i) * (n j * n i) := by
    rw [hdot n a, hdot n b]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [show (fun n => dot n a * dot n b) =
      fun n => ∑ i : Fin 3, ∑ j : Fin 3, (a j * b i) * (n j * n i) from funext hexp]
  calc
    siteFunctional s (fun n => ∑ i : Fin 3, ∑ j : Fin 3, (a j * b i) * (n j * n i)) =
        siteFunctional s (fun n => ∑ i : Fin 3, (1 : ℝ) *
          (∑ j : Fin 3, (a j * b i) * (n j * n i))) := by
            congr 1
            funext n
            simp
    _ = ∑ i : Fin 3, siteFunctional s (fun n => ∑ j : Fin 3,
          (a j * b i) * (n j * n i)) := by
            rw [AKLT.Blueprint.Mom.siteFunctional_sum]
            simp
    _ = ∑ i : Fin 3, ρ * (a i * b i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [AKLT.Blueprint.Mom.siteFunctional_sum s (fun j : Fin 3 => a j * b i)
            (fun j n => n j * n i)]
          simp_rw [h2]
          rw [Finset.sum_eq_single i]
          · simp [mul_comm]
          · intro j hj hji
            simp [hji]
          · simp
    _ = ρ * dot a b := by
          rw [dot, ← Finset.mul_sum]
private lemma sf_dot_dot_dot (s : Status)
    (h3 : ∀ i j k, siteFunctional s (fun n => n i * n j * n k) = 0)
    (a b c : Vec3) :
    siteFunctional s (fun n => dot n a * dot n b * dot n c) = 0 := by
  have hdot (n : Vec3) (a : Vec3) : dot n a = ∑ i : Fin 3, a i * n i := by
    unfold dot
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hexp (n : Vec3) : dot n a * dot n b * dot n c =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (a k * b j * c i) * (n k * n j * n i) := by
    rw [hdot n a, hdot n b, hdot n c]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [show (fun n => dot n a * dot n b * dot n c) =
      fun n => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (a k * b j * c i) * (n k * n j * n i) from funext hexp]
  rw [show siteFunctional s (fun n => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      (a k * b j * c i) * (n k * n j * n i)) =
      siteFunctional s (fun n => ∑ i : Fin 3, (1 : ℝ) *
        (∑ j : Fin 3, ∑ k : Fin 3, (a k * b j * c i) * (n k * n j * n i))) by
        congr 1; funext n; simp]
  rw [AKLT.Blueprint.Mom.siteFunctional_sum]
  simp only [one_mul]
  apply Finset.sum_eq_zero
  intro i hi
  rw [show siteFunctional s (fun n => ∑ j : Fin 3, ∑ k : Fin 3,
      (a k * b j * c i) * (n k * n j * n i)) =
      siteFunctional s (fun n => ∑ j : Fin 3, (1 : ℝ) *
        (∑ k : Fin 3, (a k * b j * c i) * (n k * n j * n i))) by
        congr 1; funext n; simp]
  rw [AKLT.Blueprint.Mom.siteFunctional_sum s (fun _ : Fin 3 => 1)
    (fun j n => ∑ k : Fin 3, (a k * b j * c i) * (n k * n j * n i))]
  simp only [one_mul]
  apply Finset.sum_eq_zero
  intro j hj
  rw [AKLT.Blueprint.Mom.siteFunctional_sum s (fun k : Fin 3 => a k * b j * c i)
    (fun k n => n k * n j * n i)]
  simp_rw [h3]
  simp

private lemma sf_congr (s : Status) {f g : Vec3 → ℝ} (h : f = g) :
    siteFunctional s f = siteFunctional s g := by rw [h]

theorem main : AKLT.Blueprint.H1.PassageSiteMomentsStatement := by
  intro hM a b o
  rcases coordMoments hM with ⟨hU1, hU2, hU3, hD1, hD2⟩
  have hConstU := sf_const hM Status.U (Or.inl rfl)
  have hConstD := sf_const hM Status.D (Or.inr rfl)
  have hUa := sf_dot Status.U hU1 a
  have hUb := sf_dot Status.U hU1 b
  have hUo := sf_dot Status.U hU1 o
  have hDa := sf_dot Status.D hD1 a
  have hDb := sf_dot Status.D hD1 b
  have hUab := sf_dot_dot Status.U (1 / 3) hU2 a b
  have hUao := sf_dot_dot Status.U (1 / 3) hU2 a o
  have hUbo := sf_dot_dot Status.U (1 / 3) hU2 b o
  have hDab := sf_dot_dot Status.D (1 / 5) hD2 a b
  have hUabo := sf_dot_dot_dot Status.U hU3 a b o
  constructor
  · have hExpand : (fun n : Vec3 => (1 + dot n a) * (1 + dot n b) * (1 + dot n o)) =
        fun n => 1 + dot n a + dot n b + dot n o +
          dot n a * dot n b + dot n a * dot n o + dot n b * dot n o +
          dot n a * dot n b * dot n o := by
      funext n
      ring
    rw [hExpand]
    simp only [sf_add, hConstU, hUa, hUb, hUo, hUab, hUao, hUbo, hUabo]
    ring
  · have hExpand : (fun n : Vec3 => (1 + dot n a) * (1 + dot n b)) =
        fun n => 1 + dot n a + dot n b + dot n a * dot n b := by
      funext n
      ring
    rw [hExpand]
    simp only [sf_add, hConstD, hDa, hDb, hDab]
    ring

end AKLT.W.H1M005
