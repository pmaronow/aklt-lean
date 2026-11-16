import AKLT.Cert.H1.Production.TopLeaves
import Mathlib.LinearAlgebra.Matrix.SchurComplement

namespace AKLT.W.H1C005

open AKLT.Defs

private def leadIndex {n j : ℕ} (hj : j ≤ n) (a : Fin j) : Fin n :=
  ⟨a.val, Nat.lt_of_lt_of_le a.isLt hj⟩

private def insertIndex {n j : ℕ} (hj : j + 1 ≤ n) (x : Fin n) : Fin (j + 1) → Fin n :=
  fun a => if ha : a.val < j then ⟨a.val, by omega⟩ else x

private def sumInsertIndex {n j : ℕ} (hj : j + 1 ≤ n) (x : Fin n) : Fin j ⊕ Fin 1 → Fin n
  | Sum.inl a => leadIndex (by omega) a
  | Sum.inr _ => x

private def pairIndex {n : ℕ} (x y : Fin n) (a : Fin 2) : Fin n :=
  if a.val = 0 then x else y

private def twoInsertIndex {n j : ℕ} (hj : j + 2 ≤ n) (x y : Fin n) :
    Fin j ⊕ Fin 2 → Fin n
  | Sum.inl a => leadIndex (by omega) a
  | Sum.inr a => pairIndex x y a

private def borderMinor {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (j : ℕ)
    (hj : j + 1 ≤ n) (i l : Fin n) : ℤ :=
  (M.submatrix (insertIndex hj i) (insertIndex hj l)).det

private def borderSumMinor {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (j : ℕ)
    (hj : j + 1 ≤ n) (i l : Fin n) : ℤ :=
  (M.submatrix (sumInsertIndex hj i) (sumInsertIndex hj l)).det

private def rationalMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  M.map (Int.castRingHom ℚ)

private def leadingBlock {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (j : ℕ)
    (hj : j ≤ n) : Matrix (Fin j) (Fin j) ℚ :=
  (rationalMatrix M).submatrix (leadIndex hj) (leadIndex hj)

private lemma borderMinor_cast {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (j : ℕ)
    (hj : j + 1 ≤ n) (i l : Fin n) :
    (borderMinor M j hj i l : ℚ) =
      ((rationalMatrix M).submatrix (insertIndex hj i) (insertIndex hj l)).det := by
  change (Int.castRingHom ℚ) ((M.submatrix (insertIndex hj i) (insertIndex hj l)).det) = _
  rw [(Int.castRingHom ℚ).map_det]
  rfl

private lemma borderSumMinor_cast {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (j : ℕ)
    (hj : j + 1 ≤ n) (i l : Fin n) :
    (borderSumMinor M j hj i l : ℚ) =
      ((rationalMatrix M).submatrix (sumInsertIndex hj i) (sumInsertIndex hj l)).det := by
  change (Int.castRingHom ℚ) ((M.submatrix (sumInsertIndex hj i) (sumInsertIndex hj l)).det) = _
  rw [(Int.castRingHom ℚ).map_det]
  rfl

private lemma leadingMinor_cast {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (j : ℕ)
    (hj : j ≤ n) : (leadingMinor M j hj : ℚ) = (leadingBlock M j hj).det := by
  change (Int.castRingHom ℚ) ((M.submatrix (fun i : Fin j => (⟨i.val, by omega⟩ : Fin n))
    (fun i : Fin j => (⟨i.val, by omega⟩ : Fin n))).det) = _
  rw [(Int.castRingHom ℚ).map_det]
  rfl

private def singleCol {j : ℕ} {K : Type*} (B : Matrix (Fin j) (Fin 2) K)
    (b : Fin 2) : Matrix (Fin j) (Fin 1) K := fun x _ => B x b

private def singleRow {j : ℕ} {K : Type*} (C : Matrix (Fin 2) (Fin j) K)
    (a : Fin 2) : Matrix (Fin 1) (Fin j) K := fun _ x => C a x

private lemma singleSchurEntry {j : ℕ} {K : Type*} [CommRing K]
    (A : Matrix (Fin j) (Fin j) K) [Invertible A]
    (B : Matrix (Fin j) (Fin 2) K) (C : Matrix (Fin 2) (Fin j) K)
    (a b : Fin 2) :
    (singleRow C a * ⅟A * singleCol B b) 0 0 = (C * ⅟A * B) a b := by
  simp [singleRow, singleCol, Matrix.mul_apply]

private lemma oneBorder_det_eq_schur {j : ℕ} {K : Type*} [CommRing K]
    (A : Matrix (Fin j) (Fin j) K) [Invertible A]
    (B : Matrix (Fin j) (Fin 2) K) (C : Matrix (Fin 2) (Fin j) K)
    (D : Matrix (Fin 2) (Fin 2) K) (a b : Fin 2) :
    (Matrix.fromBlocks A (singleCol B b) (singleRow C a)
      (fun _ _ : Fin 1 => D a b)).det =
      A.det * (D - C * ⅟A * B) a b := by
  let D1 : Matrix (Fin 1) (Fin 1) K := fun _ _ => D a b
  calc
    _ = A.det * (D1 - singleRow C a * ⅟A * singleCol B b).det :=
      Matrix.det_fromBlocks₁₁ A (singleCol B b) (singleRow C a) D1
    _ = A.det * (D - C * ⅟A * B) a b := by
      rw [Matrix.det_fin_one]
      rw [Matrix.sub_apply]
      simp only [D1]
      rw [singleSchurEntry]
      simp [Matrix.sub_apply]

private lemma borderMinor_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hn : 1 ≤ n)
    (i l : Fin n) : borderMinor M 0 hn i l = M i l := by
  simp [borderMinor, insertIndex, Matrix.det_unique]

private lemma borderMinor_diag {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (j : ℕ)
    (hj : j + 1 ≤ n) :
    borderMinor M j hj ⟨j, by omega⟩ ⟨j, by omega⟩ = leadingMinor M (j + 1) hj := by
  unfold borderMinor leadingMinor
  have hm : insertIndex hj ⟨j, by omega⟩ = fun a : Fin (j + 1) => ⟨a.val, by omega⟩ := by
    funext a
    by_cases ha : a.val < j
    · simp [insertIndex, ha]
    · have hval : a.val = j := by omega
      apply Fin.ext
      simp [insertIndex, hval]
  rw [hm]

private lemma borderMinor_eq_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (j : ℕ)
    (hj : j + 1 ≤ n) (i l : Fin n) :
    borderMinor M j hj i l = borderSumMinor M j hj i l := by
  unfold borderMinor borderSumMinor
  let e : Fin j ⊕ Fin 1 ≃ Fin (j + 1) := finSumFinEquiv
  have hrow : insertIndex hj i ∘ e = sumInsertIndex hj i := by
    funext a
    cases a with
    | inl a =>
        apply Fin.ext
        simp [insertIndex, sumInsertIndex, leadIndex, e, finSumFinEquiv_apply_left]
    | inr a =>
        have ha : a = 0 := Fin.eq_zero a
        subst a
        apply Fin.ext
        simp [insertIndex, sumInsertIndex, e, finSumFinEquiv_apply_right]
  have hcol : insertIndex hj l ∘ e = sumInsertIndex hj l := by
    funext a
    cases a with
    | inl a =>
        apply Fin.ext
        simp [insertIndex, sumInsertIndex, leadIndex, e, finSumFinEquiv_apply_left]
    | inr a =>
        have ha : a = 0 := Fin.eq_zero a
        subst a
        apply Fin.ext
        simp [insertIndex, sumInsertIndex, e, finSumFinEquiv_apply_right]
  rw [← Matrix.det_submatrix_equiv_self e (M.submatrix (insertIndex hj i) (insertIndex hj l))]
  rw [Matrix.submatrix_submatrix, hrow, hcol]

private lemma borderMinor_succ_eq_two {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (j : ℕ)
    (hj : j + 2 ≤ n) (p : Fin n) (hp : p.val = j) (i l : Fin n) :
    borderMinor M (j + 1) (by omega) i l =
      (M.submatrix (twoInsertIndex hj p i) (twoInsertIndex hj p l)).det := by
  unfold borderMinor
  let e : Fin j ⊕ Fin 2 ≃ Fin (j + 2) := finSumFinEquiv
  have hrow : insertIndex (by omega : (j + 1) + 1 ≤ n) i ∘ e = twoInsertIndex hj p i := by
    funext a
    cases a with
    | inl a =>
        apply Fin.ext
        simp [insertIndex, twoInsertIndex, leadIndex, e, finSumFinEquiv_apply_left]
    | inr a =>
        fin_cases a <;>
          apply Fin.ext <;>
          simp [insertIndex, twoInsertIndex, pairIndex, e,
            finSumFinEquiv_apply_right, hp]
  have hcol : insertIndex (by omega : (j + 1) + 1 ≤ n) l ∘ e = twoInsertIndex hj p l := by
    funext a
    cases a with
    | inl a =>
        apply Fin.ext
        simp [insertIndex, twoInsertIndex, leadIndex, e, finSumFinEquiv_apply_left]
    | inr a =>
        fin_cases a <;>
          apply Fin.ext <;>
          simp [insertIndex, twoInsertIndex, pairIndex, e,
            finSumFinEquiv_apply_right, hp]
  rw [← Matrix.det_submatrix_equiv_self e (M.submatrix
    (insertIndex (by omega : (j + 1) + 1 ≤ n) i)
    (insertIndex (by omega : (j + 1) + 1 ≤ n) l))]
  rw [Matrix.submatrix_submatrix, hrow, hcol]

private def Residual_desnanotJacobi : Prop :=
  ∀ n : ℕ, ∀ M : Matrix (Fin n) (Fin n) ℤ, ∀ j : ℕ,
  ∀ hj : j + 2 ≤ n, leadingMinor M j (by omega) ≠ 0 →
  ∀ i l : Fin n, j < i.val → j < l.val →
    leadingMinor M j (by omega) * borderMinor M (j + 1) (by omega) i l =
      borderMinor M j (by omega) ⟨j, by omega⟩ ⟨j, by omega⟩ *
        borderMinor M j (by omega) i l -
      borderMinor M j (by omega) i ⟨j, by omega⟩ *
        borderMinor M j (by omega) ⟨j, by omega⟩ l

private lemma pairIndex_zero {n : ℕ} (x y : Fin n) : pairIndex x y (0 : Fin 2) = x := by
  simp [pairIndex]

private lemma pairIndex_one {n : ℕ} (x y : Fin n) : pairIndex x y (1 : Fin 2) = y := by
  simp [pairIndex]

private theorem desnanotJacobi : Residual_desnanotJacobi := by
  intro n M j hj hdet i l hji hjl
  let p : Fin n := ⟨j, by omega⟩
  have hp : p.val = j := rfl
  let Q := rationalMatrix M
  let L : Fin j → Fin n := leadIndex (by omega)
  let A : Matrix (Fin j) (Fin j) ℚ := Q.submatrix L L
  let B : Matrix (Fin j) (Fin 2) ℚ := fun a b => Q (L a) (pairIndex p l b)
  let C : Matrix (Fin 2) (Fin j) ℚ := fun a b => Q (pairIndex p i a) (L b)
  let D : Matrix (Fin 2) (Fin 2) ℚ := fun a b => Q (pairIndex p i a) (pairIndex p l b)
  have hAcast : (leadingMinor M j (by omega) : ℚ) = A.det := by
    simpa [A, Q, L, leadingBlock, rationalMatrix] using (leadingMinor_cast M j (by omega))
  have hAne : A.det ≠ 0 := by
    rw [← hAcast]
    exact_mod_cast hdet
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hAne)
  let S : Matrix (Fin 2) (Fin 2) ℚ := D - C * ⅟A * B
  let oneMat (x y : Fin n) : Matrix (Fin j ⊕ Fin 1) (Fin j ⊕ Fin 1) ℚ :=
    Q.submatrix (sumInsertIndex (by omega) x) (sumInsertIndex (by omega) y)
  have hOne (a b : Fin 2) :
      oneMat (pairIndex p i a) (pairIndex p l b) =
        Matrix.fromBlocks A (singleCol B b) (singleRow C a)
          (fun _ _ : Fin 1 => D a b) := by
    ext x y
    cases x <;> cases y <;>
      simp [oneMat, A, B, C, D, Q, L, rationalMatrix, sumInsertIndex,
        leadIndex, pairIndex, singleCol, singleRow, Matrix.fromBlocks]
  let bigMat : Matrix (Fin j ⊕ Fin 2) (Fin j ⊕ Fin 2) ℚ :=
    Q.submatrix (twoInsertIndex hj p i) (twoInsertIndex hj p l)
  have hBig : bigMat = Matrix.fromBlocks A B C D := by
    ext x y
    cases x <;> cases y <;>
      simp [bigMat, A, B, C, D, Q, L, rationalMatrix, twoInsertIndex,
        leadIndex, pairIndex, Matrix.fromBlocks]
  have hBigCast : (borderMinor M (j + 1) (by omega) i l : ℚ) = bigMat.det := by
    rw [borderMinor_succ_eq_two M j hj p hp i l]
    change (Int.castRingHom ℚ) ((M.submatrix (twoInsertIndex hj p i)
      (twoInsertIndex hj p l)).det) = _
    rw [(Int.castRingHom ℚ).map_det]
    rfl
  have hBigDet : bigMat.det = A.det * S.det := by
    rw [hBig]
    exact Matrix.det_fromBlocks₁₁ A B C D
  have hOneCast (a b : Fin 2) :
      (borderMinor M j (by omega) (pairIndex p i a) (pairIndex p l b) : ℚ) =
        A.det * S a b := by
    rw [borderMinor_eq_sum M j (by omega) (pairIndex p i a) (pairIndex p l b)]
    rw [borderSumMinor_cast]
    change (oneMat (pairIndex p i a) (pairIndex p l b)).det = _
    calc
      (oneMat (pairIndex p i a) (pairIndex p l b)).det =
          (Matrix.fromBlocks A (singleCol B b) (singleRow C a)
            (fun _ _ : Fin 1 => D a b)).det := congrArg Matrix.det (hOne a b)
      _ = A.det * S a b := by
        simpa [S] using (oneBorder_det_eq_schur A B C D a b)
  let u₀ : Fin 2 := ⟨0, by omega⟩
  let u₁ : Fin 2 := ⟨1, by omega⟩
  have hSdet : S.det = S u₀ u₀ * S u₁ u₁ - S u₀ u₁ * S u₁ u₀ := by
    simpa [u₀, u₁] using (Matrix.det_fin_two S)
  have hpp : (borderMinor M j (by omega) p p : ℚ) = A.det * S u₀ u₀ := by
    simpa [u₀, pairIndex] using hOneCast u₀ u₀
  have hill : (borderMinor M j (by omega) i l : ℚ) = A.det * S u₁ u₁ := by
    simpa [u₁, pairIndex] using hOneCast u₁ u₁
  have hip : (borderMinor M j (by omega) i p : ℚ) = A.det * S u₁ u₀ := by
    simpa [u₀, u₁, pairIndex] using hOneCast u₁ u₀
  have hpl : (borderMinor M j (by omega) p l : ℚ) = A.det * S u₀ u₁ := by
    simpa [u₀, u₁, pairIndex] using hOneCast u₀ u₁
  have hq :
      (leadingMinor M j (by omega) : ℚ) *
          (borderMinor M (j + 1) (by omega) i l : ℚ) =
        (borderMinor M j (by omega) p p : ℚ) *
            (borderMinor M j (by omega) i l : ℚ) -
          (borderMinor M j (by omega) i p : ℚ) *
            (borderMinor M j (by omega) p l : ℚ) := by
    rw [hAcast, hBigCast, hBigDet]
    rw [hpp, hill, hip, hpl]
    rw [hSdet]
    ring
  exact_mod_cast hq

private lemma bareissState_snd_succ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (j : ℕ) (hj : j < n) :
    (bareissState M (j + 1)).2 = bareissPivot M j := by
  simp [bareissState, bareissPivot, hj]

private theorem stageInvariant (hdj : Residual_desnanotJacobi) :
    ∀ j : ℕ, ∀ n : ℕ, ∀ M : Matrix (Fin n) (Fin n) ℤ,
      (hj : j < n) → (∀ k < j, bareissPivot M k ≠ 0) →
      (bareissState M j).2 = leadingMinor M j (by omega) ∧
      ∀ i l : Fin n, j ≤ i.val → j ≤ l.val →
        (bareissState M j).1 i l = borderMinor M j (by omega) i l := by
  intro j
  induction j with
  | zero =>
      intro n M hn _
      constructor
      · simp [bareissState, leadingMinor, Matrix.det_fin_zero]
      · intro i l hi hl
        have hn' : 1 ≤ n := by omega
        simpa [bareissState] using (borderMinor_zero M hn' i l).symm
  | succ j ih =>
      intro n M hn hprev
      have hn' : j + 1 ≤ n := by omega
      have hjn : j < n := by omega
      have hprior : ∀ k < j, bareissPivot M k ≠ 0 := by
        intro k hk
        exact hprev k (by omega)
      obtain ⟨hdenEq, hentries⟩ := ih n M (by omega) hprior
      let p : Fin n := ⟨j, hjn⟩
      constructor
      · have he := hentries p p (by simp [p]) (by simp [p])
        rw [bareissState_snd_succ M j hjn]
        simp only [bareissPivot, dite_eq_left hjn]
        change (bareissState M j).1 p p = leadingMinor M (j + 1) hn'
        rw [he]
        exact borderMinor_diag M j hn'
      · intro i l hi hl
        have hden : (bareissState M j).2 ≠ 0 := by
          by_cases hj0 : j = 0
          · subst j
            simp [bareissState]
          · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
            have hprevPivot := hprev (j - 1) (by omega)
            have hsnd : (bareissState M j).2 = bareissPivot M (j - 1) := by
              have heq : j - 1 + 1 = j := by omega
              rw [← heq]
              exact bareissState_snd_succ M (j - 1) (by omega)
            exact hsnd ▸ hprevPivot
        have hp_le : j ≤ p.val := by change j ≤ j; exact Nat.le_refl j
        have hpivot := hentries p p hp_le hp_le
        have hIl := hentries i l (by omega) (by omega)
        have hiP := hentries i p (by omega) hp_le
        have hpL := hentries p l hp_le (by omega)
        have hj2 : j + 2 ≤ n := by omega
        have hlead : leadingMinor M j (by omega) ≠ 0 := by
          intro hz
          apply hden
          rw [hdenEq, hz]
        have hDJ := hdj n M j hj2 hlead i l (by omega) (by omega)
        have hnum :
            (bareissState M j).1 p p * (bareissState M j).1 i l -
                (bareissState M j).1 i p * (bareissState M j).1 p l =
              borderMinor M (j + 1) (by omega) i l * (bareissState M j).2 := by
          rw [hpivot, hIl, hiP, hpL, hdenEq]
          nlinarith [hDJ]
        have hquot := Int.ediv_eq_of_eq_mul_left hden hnum
        have hrec : (bareissState M (j + 1)).1 i l =
            ((bareissState M j).1 p p * (bareissState M j).1 i l -
              (bareissState M j).1 i p * (bareissState M j).1 p l) /
              (bareissState M j).2 := by
          have hji : j < i.val := by omega
          have hjl : j < l.val := by omega
          simp [bareissState, hjn, hji, hjl, p]
        rw [hrec, hquot]

private theorem main_of_desnanotJacobi (hdj : Residual_desnanotJacobi) :
    AKLT.Cert.H1.Production.TopLeaves.bareiss := by
  intro n M hsym j hj hprev
  have hstage := stageInvariant hdj j n M hj hprev
  rcases hstage with ⟨hdenEq, hentries⟩
  let p : Fin n := ⟨j, hj⟩
  have hp_le : j ≤ p.val := by change j ≤ j; exact Nat.le_refl j
  have hpivot := hentries p p hp_le hp_le
  constructor
  · simp only [bareissPivot, dite_eq_left hj]
    rw [hpivot]
    exact borderMinor_diag M j (by omega)
  · intro i l hi hl
    have hi' : j ≤ i.val := by omega
    have hl' : j ≤ l.val := by omega
    have hj2 : j + 2 ≤ n := by omega
    have hIl := hentries i l hi' hl'
    have hiP := hentries i p hi' hp_le
    have hpL := hentries p l hp_le hl'
    have hden : (bareissState M j).2 ≠ 0 := by
      by_cases hj0 : j = 0
      · subst j
        simp [bareissState]
      · have hprevPivot := hprev (j - 1) (by omega)
        have hsnd : (bareissState M j).2 = bareissPivot M (j - 1) := by
          have heq : j - 1 + 1 = j := by omega
          rw [← heq]
          exact bareissState_snd_succ M (j - 1) (by omega)
        exact hsnd ▸ hprevPivot
    have hlead : leadingMinor M j (by omega) ≠ 0 := by
      intro hz
      apply hden
      rw [hdenEq, hz]
    have hnum :
        (bareissState M j).1 p p * (bareissState M j).1 i l -
          (bareissState M j).1 i p * (bareissState M j).1 p l =
        (bareissState M j).2 * borderMinor M (j + 1) (by omega) i l := by
      rw [hpivot, hIl, hiP, hpL, hdenEq]
      have hdj' := hdj n M j hj2 hlead i l (by omega) (by omega)
      nlinarith [hdj']
    refine ⟨borderMinor M (j + 1) (by omega) i l, ?_⟩
    simpa [bareissPivot, hj, p] using hnum

theorem main : AKLT.Cert.H1.Production.TopLeaves.bareiss :=
  main_of_desnanotJacobi desnanotJacobi

end AKLT.W.H1C005
