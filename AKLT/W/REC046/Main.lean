module
public import AKLT.Blueprint.Rec.NodesWalk

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.W.REC046

private lemma log_gap_bound {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    |b - c| ≤ max b c * |Real.log c - Real.log b| := by
  by_cases hbc : b ≤ c
  · have hlogs : 0 ≤ Real.log c - Real.log b := by
      exact sub_nonneg.mpr (Real.log_le_log hb hbc)
    have hdiv : Real.log (b / c) = Real.log b - Real.log c :=
      Real.log_div (ne_of_gt hb) (ne_of_gt hc)
    have hlog := Real.log_le_sub_one_of_pos (div_pos hb hc)
    have hratio : 1 - b / c ≤ -Real.log (b / c) := by linarith
    have hscaled := mul_le_mul_of_nonneg_left hratio (le_of_lt hc)
    have hnum : c * (1 - b / c) = c - b := by
      field_simp
    have hbound : c - b ≤ c * (Real.log c - Real.log b) := by
      calc
        c - b = c * (1 - b / c) := hnum.symm
        _ ≤ c * -Real.log (b / c) := hscaled
        _ = c * (Real.log c - Real.log b) := by rw [hdiv]; ring
    rw [abs_of_nonpos (sub_nonpos.mpr hbc), max_eq_right hbc,
      abs_of_nonneg hlogs]
    nlinarith [hbound]
  · have hcb : c ≤ b := le_of_not_ge hbc
    have hlogs : 0 ≤ Real.log b - Real.log c := by
      exact sub_nonneg.mpr (Real.log_le_log hc hcb)
    have hdiv : Real.log (c / b) = Real.log c - Real.log b :=
      Real.log_div (ne_of_gt hc) (ne_of_gt hb)
    have hlog := Real.log_le_sub_one_of_pos (div_pos hc hb)
    have hratio : 1 - c / b ≤ -Real.log (c / b) := by linarith
    have hscaled := mul_le_mul_of_nonneg_left hratio (le_of_lt hb)
    have hnum : b * (1 - c / b) = b - c := by
      field_simp
    have hbound : b - c ≤ b * (Real.log b - Real.log c) := by
      calc
        b - c = b * (1 - c / b) := hnum.symm
        _ ≤ b * -Real.log (c / b) := hscaled
        _ = b * (Real.log b - Real.log c) := by rw [hdiv]; ring
    rw [abs_of_nonneg (sub_nonneg.mpr hcb), max_eq_left hcb]
    have hlogabs : |Real.log c - Real.log b| = Real.log b - Real.log c := by
      rw [abs_of_nonpos]
      · ring
      · linarith
    rw [hlogabs]
    exact hbound

private lemma prefixProd_succ {n : ℕ} (x : Fin (n + 1) → ℝ) (i : Fin n) :
    (∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.succ.val), x j) =
      x 0 * ∏ k ∈ Finset.univ.filter (fun k : Fin n => k.val ≤ i.val), x k.succ := by
  classical
  have hset :
      Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.succ.val) =
        insert 0 (Finset.map (Fin.succEmb n)
          (Finset.univ.filter (fun k : Fin n => k.val ≤ i.val))) := by
    ext j
    rcases Fin.eq_zero_or_eq_succ j with hj | ⟨k, hj⟩
    · subst j
      simp
    · subst j
      simp [Fin.val_succ]
  rw [hset, Finset.prod_insert]
  · rw [Finset.prod_map]
    rfl
  · intro hzero
    simp only [Finset.mem_map] at hzero
    rcases hzero with ⟨k, hk, hEq⟩
    have hv := congrArg Fin.val hEq
    simp [Fin.succEmb] at hv

private theorem product_exposure_aux : ∀ n : ℕ, ∀ b c x : Fin n → ℝ,
    (∀ i, 0 < b i ∧ 0 < c i ∧ c i ≤ 1 ∧ b i ≤ x i ∧ 1 ≤ x i) →
    |(∏ i, b i) - ∏ i, c i| ≤
      ∑ i, |Real.log (c i) - Real.log (b i)| *
        ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ i.val), x j := by
  intro n
  induction n with
  | zero =>
      intro b c x h
      simp
  | succ n ih =>
      intro b c x h
      let bt : Fin n → ℝ := fun i => b i.succ
      let ct : Fin n → ℝ := fun i => c i.succ
      let xt : Fin n → ℝ := fun i => x i.succ
      have ht : ∀ i, 0 < bt i ∧ 0 < ct i ∧ ct i ≤ 1 ∧ bt i ≤ xt i ∧ 1 ≤ xt i := by
        intro i
        exact h i.succ
      have hind := ih bt ct xt ht
      have hqpos : 0 < ∏ i : Fin n, ct i := by
        apply Finset.prod_pos
        intro i hi
        exact (ht i).2.1
      have hqle : ∏ i : Fin n, ct i ≤ 1 := by
        apply Finset.prod_le_one₀
        · intro i hi
          exact le_of_lt (ht i).2.1
        · intro i hi
          exact (ht i).2.2.1
      have hb0le : b 0 ≤ x 0 := (h 0).2.2.2.1
      have hx0one : 1 ≤ x 0 := (h 0).2.2.2.2
      have hscalar := log_gap_bound (h 0).1 (h 0).2.1
      have hmaxle : max (b 0) (c 0) ≤ x 0 := max_le hb0le (le_trans (h 0).2.2.1 hx0one)
      have hscalar' : |b 0 - c 0| ≤ x 0 * |Real.log (c 0) - Real.log (b 0)| := by
        calc
          |b 0 - c 0| ≤ max (b 0) (c 0) * |Real.log (c 0) - Real.log (b 0)| := hscalar
          _ ≤ x 0 * |Real.log (c 0) - Real.log (b 0)| :=
            mul_le_mul_of_nonneg_right hmaxle (abs_nonneg _)
      have htail_nonneg : 0 ≤
          ∑ i : Fin n, |Real.log (ct i) - Real.log (bt i)| *
            ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ i.val), xt j := by
        apply Finset.sum_nonneg
        intro i hi
        apply mul_nonneg (abs_nonneg _)
        apply Finset.prod_nonneg
        intro j hj
        exact le_trans (by linarith [(ht j).2.2.2.2]) (ht j).2.2.2.2
      have hdecomp :
          (∏ i : Fin (n + 1), b i) - ∏ i : Fin (n + 1), c i =
            (b 0 - c 0) * (∏ i : Fin n, ct i) +
              b 0 * ((∏ i : Fin n, bt i) - ∏ i : Fin n, ct i) := by
        simp only [Fin.prod_univ_succ]
        dsimp [bt, ct]
        ring
      have habs :
          |(∏ i : Fin (n + 1), b i) - ∏ i : Fin (n + 1), c i| ≤
            |b 0 - c 0| * (∏ i : Fin n, ct i) +
              b 0 * |(∏ i : Fin n, bt i) - ∏ i : Fin n, ct i| := by
        calc
          |(∏ i : Fin (n + 1), b i) - ∏ i : Fin (n + 1), c i|
              = |(b 0 - c 0) * (∏ i : Fin n, ct i) +
                  b 0 * ((∏ i : Fin n, bt i) - ∏ i : Fin n, ct i)| := by rw [hdecomp]
          _ ≤ |(b 0 - c 0) * (∏ i : Fin n, ct i)| +
                |b 0 * ((∏ i : Fin n, bt i) - ∏ i : Fin n, ct i)| := abs_add_le _ _
          _ = |b 0 - c 0| * (∏ i : Fin n, ct i) +
                b 0 * |(∏ i : Fin n, bt i) - ∏ i : Fin n, ct i| := by
              rw [abs_mul, abs_mul, abs_of_pos hqpos, abs_of_pos (h 0).1]
      have hfirst : |b 0 - c 0| * (∏ i : Fin n, ct i) ≤
          x 0 * |Real.log (c 0) - Real.log (b 0)| := by
        calc
          |b 0 - c 0| * (∏ i : Fin n, ct i) ≤ |b 0 - c 0| * 1 :=
            mul_le_mul_of_nonneg_left hqle (abs_nonneg _)
          _ = |b 0 - c 0| := by ring
          _ ≤ x 0 * |Real.log (c 0) - Real.log (b 0)| := hscalar'
      have hsecond : b 0 * |(∏ i : Fin n, bt i) - ∏ i : Fin n, ct i| ≤
          x 0 * (∑ i : Fin n, |Real.log (ct i) - Real.log (bt i)| *
            ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ i.val), xt j) := by
        calc
          b 0 * |(∏ i : Fin n, bt i) - ∏ i : Fin n, ct i| ≤
              b 0 * (∑ i : Fin n, |Real.log (ct i) - Real.log (bt i)| *
                ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ i.val), xt j) :=
            mul_le_mul_of_nonneg_left hind (le_of_lt (h 0).1)
          _ ≤ x 0 * (∑ i : Fin n, |Real.log (ct i) - Real.log (bt i)| *
                ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ i.val), xt j) :=
            mul_le_mul_of_nonneg_right hb0le htail_nonneg
      have hsumform :
          (∑ i : Fin (n + 1), |Real.log (c i) - Real.log (b i)| *
            ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.val), x j) =
            x 0 * (∑ i : Fin n, |Real.log (ct i) - Real.log (bt i)| *
              ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ i.val), xt j) +
                x 0 * |Real.log (c 0) - Real.log (b 0)| := by
        have hp0 :
            (∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ (0 : Fin (n + 1)).val), x j) = x 0 := by
          have hs : Finset.univ.filter
              (fun j : Fin (n + 1) => j.val ≤ (0 : Fin (n + 1)).val) = {0} := by
            ext j
            simp
          rw [hs]
          simp
        rw [Fin.sum_univ_succ, hp0]
        simp only [prefixProd_succ]
        calc
          |Real.log (c 0) - Real.log (b 0)| * x 0 +
              ∑ i : Fin n, |Real.log (c i.succ) - Real.log (b i.succ)| *
                (x 0 * ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ i.val), x j.succ) =
              x 0 * |Real.log (c 0) - Real.log (b 0)| +
                x 0 * (∑ i : Fin n, |Real.log (c i.succ) - Real.log (b i.succ)| *
                  ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ i.val), x j.succ) := by
            rw [Finset.mul_sum]
            congr 1
            · ring
            · apply Finset.sum_congr rfl
              intro i hi
              ring
          _ = x 0 * (∑ i : Fin n, |Real.log (ct i) - Real.log (bt i)| *
                ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ i.val), xt j) +
              x 0 * |Real.log (c 0) - Real.log (b 0)| := by
            dsimp [bt, ct, xt]
            ring
      calc
        |(∏ i : Fin (n + 1), b i) - ∏ i : Fin (n + 1), c i|
            ≤ |b 0 - c 0| * (∏ i : Fin n, ct i) +
                b 0 * |(∏ i : Fin n, bt i) - ∏ i : Fin n, ct i| := habs
        _ ≤ x 0 * |Real.log (c 0) - Real.log (b 0)| +
              x 0 * (∑ i : Fin n, |Real.log (ct i) - Real.log (bt i)| *
                ∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ i.val), xt j) :=
            add_le_add hfirst hsecond
        _ = ∑ i : Fin (n + 1), |Real.log (c i) - Real.log (b i)| *
              ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.val), x j := by
            rw [hsumform]
            ring

theorem main : AKLT.Blueprint.Rec.ProductExposureStatement := by
  intro n b c x h
  exact product_exposure_aux n b c x h

end AKLT.W.REC046
