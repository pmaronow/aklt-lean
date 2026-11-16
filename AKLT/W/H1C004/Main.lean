import AKLT.Cert.H1.Production.TopLeaves
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement

namespace AKLT.W.H1C004

open Matrix

private def leadIndex {k n : ℕ} (h : k ≤ n) (i : Fin k) : Fin n :=
  ⟨i.val, by omega⟩

private def leadDet {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (h : k ≤ n) : ℝ :=
  (A.submatrix (leadIndex h) (leadIndex h)).det

private theorem leadIndex_self (n : ℕ) : leadIndex (n := n) (Nat.le_refl n) = id := by
  funext i
  apply Fin.ext
  rfl

private theorem real_sylvester (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    A.PosDef ↔ ∀ k : ℕ, ∀ h : k ≤ n, 0 < k → 0 < leadDet A k h := by
  induction n with
  | zero =>
      constructor
      · intro _ k h hk
        omega
      · intro _
        constructor
        · ext i j
          exact Fin.elim0 i
        · intro x hx
          have hx0 : x = 0 := by
            ext i
            exact Fin.elim0 i
          exact (hx hx0).elim
  | succ n ih =>
      constructor
      · intro hpos k hk hkpos
        have hinj : Function.Injective (leadIndex hk : Fin k → Fin (n + 1)) := by
          intro i j hij
          apply Fin.ext
          simpa [leadIndex] using congrArg Fin.val hij
        have hsub : (A.submatrix (leadIndex hk) (leadIndex hk)).PosDef :=
          hpos.submatrix hinj
        have hdet := hsub.det_pos
        exact hdet
      · intro hmin
        let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
        let A₀ : Matrix (Fin n) (Fin n) ℝ := A.submatrix (Fin.castAdd 1) (Fin.castAdd 1)
        let B : Matrix (Fin n) (Fin 1) ℝ := fun i j => A (Fin.castAdd 1 i) (Fin.natAdd n j)
        let D : Matrix (Fin 1) (Fin 1) ℝ := A.submatrix (Fin.natAdd n) (Fin.natAdd n)
        have hA₀sym : A₀.IsSymm := by
          exact hA.submatrix (Fin.castAdd 1)
        have hA₀min : ∀ k : ℕ, ∀ h : k ≤ n, 0 < k → 0 < leadDet A₀ k h := by
          intro k hk hkpos
          have hk' : k ≤ n + 1 := le_trans hk (Nat.le_succ n)
          have heq : A₀.submatrix (leadIndex hk) (leadIndex hk) =
              A.submatrix (leadIndex hk') (leadIndex hk') := by
            ext i j
            simp [A₀, leadIndex]
          change 0 < (A₀.submatrix (leadIndex hk) (leadIndex hk)).det
          rw [heq]
          exact hmin k hk' hkpos
        have hA₀pos : A₀.PosDef := ih A₀ hA₀sym |>.2 hA₀min
        have hA₀det : 0 < A₀.det := hA₀pos.det_pos
        have hdecomp : A.submatrix e e = Matrix.fromBlocks A₀ B Bᴴ D := by
          ext i j
          rcases i with i | i <;> rcases j with j | j
          · rfl
          · rfl
          · simp only [Matrix.submatrix_apply, e, finSumFinEquiv_apply_right,
              finSumFinEquiv_apply_left, Matrix.fromBlocks_apply₂₁,
              Matrix.conjTranspose_apply, Matrix.transpose_apply, B]
            exact (hA.apply (Fin.natAdd n i) (Fin.castAdd 1 j)).symm
          · rfl
        letI : Invertible A₀ := hA₀pos.isUnit.invertible
        let S : Matrix (Fin 1) (Fin 1) ℝ := D - Bᴴ * A₀⁻¹ * B
        have hdetFormula : (Matrix.fromBlocks A₀ B Bᴴ D).det = A₀.det * S.det := by
          simpa [S] using Matrix.det_fromBlocks₁₁ A₀ B Bᴴ D
        have hfullDet : 0 < A.det := by
          have h := hmin (n + 1) (Nat.le_refl _) (by omega)
          simpa [leadDet, leadIndex_self] using h
        have hSdet : 0 < S.det := by
          have hprod : 0 < A₀.det * S.det := by
            rw [← hdetFormula, ← hdecomp]
            simpa using hfullDet
          by_contra hn
          have hn' : S.det ≤ 0 := le_of_not_gt hn
          have hbad := mul_nonpos_of_nonneg_of_nonpos hA₀det.le hn'
          linarith
        have hS00 : 0 < S 0 0 := by simpa using hSdet
        have hSdiag : S = Matrix.diagonal (fun _ : Fin 1 => S 0 0) := by
          ext i j
          have hij : i = j := Subsingleton.elim _ _
          subst j
          have hi : i = 0 := Subsingleton.elim _ _
          rw [hi]
          simp [Matrix.diagonal]
        have hSpsd : S.PosSemidef := by
          rw [hSdiag]
          exact Matrix.PosSemidef.diagonal (fun _ => hS00.le)
        have hblockpsd : (Matrix.fromBlocks A₀ B Bᴴ D).PosSemidef :=
          (Matrix.PosDef.fromBlocks₁₁ B D hA₀pos).2 hSpsd
        have hApsd : A.PosSemidef := by
          have h' : (A.submatrix e e).PosSemidef := by simpa [hdecomp] using hblockpsd
          exact (posSemidef_submatrix_equiv e).1 h'
        have hApos : A.PosDef := by
          apply (hApsd.posDef_iff_det_ne_zero).2
          exact hfullDet.ne'
        exact hApos

private theorem leadingMinor_cast (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ)
    (k : ℕ) (h : k ≤ n) :
    ((Int.castRingHom ℝ) (AKLT.Defs.leadingMinor M k h)) =
      leadDet (M.map (Int.castRingHom ℝ)) k h := by
  simp only [AKLT.Defs.leadingMinor, leadDet]
  rw [RingHom.map_det]
  congr 1

theorem main : AKLT.Cert.H1.Production.TopLeaves.sylvester := by
  intro n M hM
  let A : Matrix (Fin n) (Fin n) ℝ := M.map (Int.castRingHom ℝ)
  have hAsym : A.IsSymm := by
    exact hM.map (Int.castRingHom ℝ)
  have hcriterion := real_sylvester n A hAsym
  constructor
  · intro hpos k hk hkpos
    have hreal := (hcriterion.mp hpos) k hk hkpos
    have hcast := leadingMinor_cast n M k hk
    have hreal' : (0 : ℝ) < (AKLT.Defs.leadingMinor M k hk : ℤ) := by
      change 0 < (Int.castRingHom ℝ) (AKLT.Defs.leadingMinor M k hk)
      rw [hcast]
      exact hreal
    exact_mod_cast hreal' 
  · intro hmin
    apply hcriterion.mpr
    intro k hk hkpos
    have hcast := leadingMinor_cast n M k hk
    have hreal' : (0 : ℝ) < (AKLT.Defs.leadingMinor M k hk : ℝ) := by
      exact_mod_cast hmin k hk hkpos
    have hreal : 0 < (Int.castRingHom ℝ) (AKLT.Defs.leadingMinor M k hk) := by
      simpa using hreal'
    rw [hcast] at hreal
    exact hreal 

end AKLT.W.H1C004
