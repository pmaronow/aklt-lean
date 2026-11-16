import AKLT.Gen.Gram.Theory
import Mathlib.Data.List.GetD

/-! A streaming integer checker. Ragged factor rows are zero-padded, allowing a
lower triangular factor to store only its nonzero prefix. All computation uses
structural list/Nat recursion and integer arithmetic. -/

namespace AKLT.Gen.Gram

open Matrix
open scoped ComplexOrder

abbrev IntRows := List (List ℤ)

/-- Zero-padded list-of-lists interpretation, with an explicit dimension. -/
def matrix (n : ℕ) (M : IntRows) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (M.getD i [] ).getD j 0

/-- Real interpretation of an input matrix; malformed inputs are rejected by `checker`. -/
noncomputable def toMatrix (M : IntRows) : Matrix (Fin M.length) (Fin M.length) ℝ :=
  castMatrix (matrix M.length M)

/-- Structural transpose, using a supplied number of columns. -/
def transposeRows : ℕ → IntRows → IntRows
  | 0, _ => []
  | n + 1, M => M.map (fun r => r.getD 0 0) :: transposeRows n (M.map List.tail)

/-- Dot product of zero-padded rows; stops at the shorter stored prefix. -/
def dotI : List ℤ → List ℤ → ℤ
  | a :: as, b :: bs => a * b + dotI as bs
  | _, _ => 0

/-- Residual row, traversing the matrix row and the factor rows together. -/
def residualRow (whole : IntRows) (c g : ℤ) (mr lr : List ℤ) : List ℤ :=
  mr.zipWith (fun a l => c * a - g * dotI lr l) whole

/-- Sum of absolute values, including the diagonal. -/
def absSum : List ℤ → ℤ
  | [] => 0
  | a :: as => |a| + absSum as

/-- `2 Eᵢᵢ > ∑ⱼ |Eᵢⱼ|` is equivalent to positive strict diagonal dominance. -/
def rowOK (whole : IntRows) (c g : ℤ) (i : ℕ) (mr lr : List ℤ) : Bool :=
  let er := residualRow whole c g mr lr
  decide (0 < er.getD i 0) && decide (absSum er < 2 * er.getD i 0)

/-- Row-wise structural traversal, also rejecting mismatched row counts. -/
def checkRows (whole : IntRows) (c g : ℤ) : ℕ → IntRows → IntRows → Bool
  | _, [], [] => true
  | i, mr :: ms, lr :: ls => rowOK whole c g i mr lr && checkRows whole c g (i+1) ms ls
  | _, _, _ => false

/-- Shape, symmetry and scale checks, separated for independently checked shards. -/
def header (M L : IntRows) (g d S : ℤ) : Bool :=
  M.all (fun r => r.length == M.length) && (L.length == M.length) &&
  L.all (fun r => decide (r.length ≤ M.length)) &&
  (M == transposeRows M.length M) &&
  decide (0 < g) && decide (0 < d) && decide (0 < S)

/-- Complete division-free Gram/residual certificate checker. -/
def checker (M L : IntRows) (g d S : ℤ) : Bool :=
  header M L g d S && checkRows L (d * S ^ 2) g 0 M L

theorem getD_transposeRows (n : ℕ) (M : IntRows) (i j : ℕ) (hi : i < n) :
    ((transposeRows n M).getD i []).getD j 0 = (M.getD j []).getD i 0 := by
  induction n generalizing M i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      simpa [transposeRows, List.getD] using
        (List.getD_map (l := M) (d := []) (n := j) (fun r : List ℤ => r.getD 0 0))
    | succ i =>
      simp only [transposeRows, List.getD_cons_succ]
      rw [ih _ _ (by omega)]
      have ht := List.getD_map (l := M) (d := []) (n := j) List.tail
      change (M.map List.tail).getD j [] = (M.getD j []).tail at ht
      rw [ht]
      cases h : M.getD j [] <;> simp

theorem dotI_eq_sum (n : ℕ) (a b : List ℤ) (ha : a.length ≤ n) (hb : b.length ≤ n) :
    dotI a b = ∑ j : Fin n, a.getD j 0 * b.getD j 0 := by
  induction n generalizing a b with
  | zero =>
    have : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst a
    simp [dotI]
  | succ n ih =>
    cases a with
    | nil => simp [dotI]
    | cons x xs =>
      cases b with
      | nil => simp [dotI]
      | cons y ys =>
        rw [dotI, Fin.sum_univ_succ, ih xs ys (by simp_all) (by simp_all)]
        simp

theorem absSum_eq_sum (a : List ℤ) :
    absSum a = ∑ j : Fin a.length, |a.getD j 0| := by
  induction a with
  | nil => simp [absSum]
  | cons x xs ih => simp [absSum, Fin.sum_univ_succ, ih]

theorem checkRows_length {whole ms ls : IntRows} {c g : ℤ} {i : ℕ}
    (h : checkRows whole c g i ms ls = true) : ms.length = ls.length := by
  induction ms generalizing ls i with
  | nil => cases ls <;> simp_all [checkRows]
  | cons m ms ih =>
    cases ls with
    | nil => simp [checkRows] at h
    | cons l ls =>
      simp only [checkRows, Bool.and_eq_true] at h
      simpa using ih h.2

theorem checkRows_getD {whole ms ls : IntRows} {c g : ℤ} {i : ℕ}
    (h : checkRows whole c g i ms ls = true) (j : ℕ) (hj : j < ms.length) :
    rowOK whole c g (i+j) (ms.getD j []) (ls.getD j []) = true := by
  induction ms generalizing ls i j with
  | nil => simp at hj
  | cons m ms ih =>
    cases ls with
    | nil => simp [checkRows] at h
    | cons l ls =>
      simp only [checkRows, Bool.and_eq_true] at h
      cases j with
      | zero => simpa using h.1
      | succ j =>
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (ih (i := i+1) h.2 j (by simpa using hj))

/-- Split a check into independent row shards without weakening its meaning. -/
theorem checkRows_append (whole ms mt ls lt : IntRows) (c g : ℤ) (i : ℕ)
    (hlen : ms.length = ls.length) :
    checkRows whole c g i (ms ++ mt) (ls ++ lt) =
      (checkRows whole c g i ms ls && checkRows whole c g (i + ms.length) mt lt) := by
  induction ms generalizing ls i with
  | nil => cases ls <;> simp_all [checkRows]
  | cons m ms ih =>
    cases ls with
    | nil => simp at hlen
    | cons l ls =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [List.cons_append, checkRows, ih _ _ hlen]
      simp [Bool.and_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem header_spec {M L : IntRows} {g d S : ℤ} (h : header M L g d S = true) :
    (∀ r ∈ M, r.length = M.length) ∧ L.length = M.length ∧
      (∀ r ∈ L, r.length ≤ M.length) ∧ (matrix M.length M).IsSymm ∧
      0 < g ∧ 0 < d ∧ 0 < S := by
  simp only [header, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq, and_assoc] at h
  rcases h with ⟨hm, hl, hls, hs, hg, hd, hS⟩
  refine ⟨hm, hl, hls, ?_, hg, hd, hS⟩
  ext i j
  have ht := getD_transposeRows M.length M i j i.isLt
  rw [← hs] at ht
  exact ht.symm

theorem residualRow_entry {whole : IntRows} {mr lr : List ℤ} {c g : ℤ} {n : ℕ}
    (hw : whole.length = n) (hm : mr.length = n) (j : Fin n) :
    (residualRow whole c g mr lr).getD j 0 =
      c * mr.getD j 0 - g * dotI lr (whole.getD j []) := by
  unfold residualRow
  have hj : j.val < (mr.zipWith (fun a l => c * a - g * dotI lr l) whole).length := by
    simp only [List.length_zipWith, hw, hm, min_self]
    exact j.isLt
  rw [List.getD_eq_getElem _ _ hj, List.getElem_zipWith]
  rw [List.getD_eq_getElem _ _ (show j.val < mr.length by omega),
    List.getD_eq_getElem _ _ (show j.val < whole.length by omega)]

/-- Accepted residual rows have the strict integer dominance used by the analytic theorem. -/
theorem checkRows_strictDiagDominant {M L : IntRows} {c g : ℤ}
    (hm : ∀ r ∈ M, r.length = M.length) (hl : L.length = M.length)
    (hls : ∀ r ∈ L, r.length ≤ M.length)
    (h : checkRows L c g 0 M L = true) :
    ∀ i, ∑ j ∈ Finset.univ.erase i,
      |(c • matrix M.length M - g •
        (matrix M.length L * (matrix M.length L)ᵀ)) i j| <
      (c • matrix M.length M - g •
        (matrix M.length L * (matrix M.length L)ᵀ)) i i := by
  intro i
  have hmi : (M.getD i []).length = M.length := by
    rw [List.getD_eq_getElem _ _ i.isLt]
    exact hm _ (List.getElem_mem i.isLt)
  have hli (j : Fin M.length) : (L.getD j []).length ≤ M.length := by
    have hj : j.val < L.length := by omega
    rw [List.getD_eq_getElem _ _ hj]
    exact hls _ (List.getElem_mem hj)
  let er := residualRow L c g (M.getD i []) (L.getD i [])
  have her : er.length = M.length := by simp only [er, residualRow, List.length_zipWith, hmi, hl, min_self]
  have he (j : Fin M.length) : er.getD j 0 =
      (c • matrix M.length M - g •
        (matrix M.length L * (matrix M.length L)ᵀ)) i j := by
    rw [residualRow_entry hl hmi j, dotI_eq_sum M.length _ _ (hli i) (hli j)]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.transpose_apply, matrix]
    simp only [zsmul_eq_mul, Int.cast_id]
  have hr := checkRows_getD h i i.isLt
  simp only [Nat.zero_add, rowOK, Bool.and_eq_true, decide_eq_true_eq] at hr
  change 0 < er.getD i 0 ∧ absSum er < 2 * er.getD i 0 at hr
  have hs : absSum er = ∑ j : Fin M.length, |er.getD j 0| := by
    have hh := absSum_eq_sum er
    rw [her] at hh
    exact hh
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp only [← he]
  rw [← hs, abs_of_pos hr.1]
  linarith [hr.2]

/-- Kernel-checkable integer certificates imply real positive definiteness. -/
theorem checker_sound {M L : IntRows} {g d S : ℤ} (h : checker M L g d S = true) :
    (toMatrix M).PosDef := by
  simp only [checker, Bool.and_eq_true] at h
  obtain ⟨hm, hl, hls, hsym, hg, hd, hS⟩ := header_spec h.1
  exact (int_gram_residual_posDef hsym hg hd hS
    (checkRows_strictDiagDominant hm hl hls h.2)).2

/-- The same integer checker certifies a complex Hermitian matrix. -/
theorem checker_sound_complex {M L : IntRows} {g d S : ℤ}
    (h : checker M L g d S = true) :
    (castMatrix (matrix M.length M) : Matrix (Fin M.length) (Fin M.length) ℂ).PosDef := by
  simp only [checker, Bool.and_eq_true] at h
  obtain ⟨hm, hl, hls, hsym, hg, hd, hS⟩ := header_spec h.1
  exact (int_gram_residual_posDef hsym hg hd hS
    (checkRows_strictDiagDominant hm hl hls h.2)).2

/-- Rational positive definiteness from the same division-free certificate. -/
theorem checker_sound_rat {M L : IntRows} {g d S : ℤ}
    (h : checker M L g d S = true) :
    (castMatrix (matrix M.length M) : Matrix (Fin M.length) (Fin M.length) ℚ).PosDef := by
  simp only [checker, Bool.and_eq_true] at h
  obtain ⟨hm, hl, hls, hsym, hg, hd, hS⟩ := header_spec h.1
  exact (int_gram_residual_posDef_rat hsym hg hd hS
    (checkRows_strictDiagDominant hm hl hls h.2)).2

/-- Assemble separately kernel-checked consecutive row shards. -/
theorem checkRows_append_true {whole ms mt ls lt : IntRows} {c g : ℤ} {i t : ℕ}
    (hm : ms.length = t) (hl : ls.length = t)
    (hs : checkRows whole c g i ms ls = true)
    (ht : checkRows whole c g (i+t) mt lt = true) :
    checkRows whole c g i (ms ++ mt) (ls ++ lt) = true := by
  rw [checkRows_append whole ms mt ls lt c g i (hm.trans hl.symm), hs, hm, ht]
  rfl

end AKLT.Gen.Gram
