module
public import AKLT.Blueprint.Q.NodesPolynomial

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Q

namespace AKLT.W.Q024

private abbrev PPair := MvPolynomial (Fin 2 × Fin 2) ℂ

private def inputPoly (c : Fin 5 → Fin 5 → ℂ) : PPair :=
  ∑ j : Fin 5, ∑ k : Fin 5,
    MvPolynomial.C (c j k) * MvPolynomial.X (0, 0) ^ (4 - j.val) *
      MvPolynomial.X (0, 1) ^ j.val * MvPolynomial.X (1, 0) ^ (4 - k.val) *
      MvPolynomial.X (1, 1) ^ k.val

private def diagonalSum (c : Fin 5 → Fin 5 → ℂ) (s : Fin 9) : ℂ :=
  ∑ j : Fin 5, ∑ k : Fin 5, if j.val + k.val = s.val then c j k else 0

private def quotientCoeff (c : Fin 5 → Fin 5 → ℂ) (a b : Fin 4) : ℂ :=
  match a.val, b.val with
  | 0, 0 => c 0 1
  | 0, 1 => c 0 2
  | 0, 2 => c 0 3
  | 0, 3 => c 0 4
  | 1, 0 => c 0 2 + c 1 1
  | 1, 1 => c 0 3 + c 1 2
  | 1, 2 => c 0 4 + c 1 3
  | 1, 3 => c 1 4
  | 2, 0 => c 0 3 + c 1 2 + c 2 1
  | 2, 1 => c 0 4 + c 1 3 + c 2 2
  | 2, 2 => c 1 4 + c 2 3
  | 2, 3 => c 2 4
  | 3, 0 => c 0 4 + c 1 3 + c 2 2 + c 3 1
  | 3, 1 => c 1 4 + c 2 3 + c 3 2
  | 3, 2 => c 2 4 + c 3 3
  | 3, 3 => c 3 4
  | _, _ => 0

private def quotientPoly (c : Fin 5 → Fin 5 → ℂ) : PPair :=
  ∑ a : Fin 4, ∑ b : Fin 4,
    MvPolynomial.C (quotientCoeff c a b) * MvPolynomial.X (0, 0) ^ (3 - a.val) *
      MvPolynomial.X (0, 1) ^ a.val * MvPolynomial.X (1, 0) ^ (3 - b.val) *
      MvPolynomial.X (1, 1) ^ b.val

private theorem coeff_pairTerm (c : ℂ) (t s : ℕ) :
    (MvPolynomial.C (σ := Fin 2) c * MvPolynomial.X (0 : Fin 2) ^ (8 - t) *
      MvPolynomial.X (1 : Fin 2) ^ t).coeff
      (Finsupp.single (0 : Fin 2) (8 - s) + Finsupp.single (1 : Fin 2) s) = if t = s then c else 0 := by
  have hmon : MvPolynomial.C (σ := Fin 2) c * MvPolynomial.X (0 : Fin 2) ^ (8 - t) *
      MvPolynomial.X 1 ^ t =
      MvPolynomial.monomial
        (Finsupp.single (0 : Fin 2) (8 - t) + Finsupp.single (1 : Fin 2) t) c := by
    calc
      _ = MvPolynomial.monomial (Finsupp.single (0 : Fin 2) (8 - t)) c *
          MvPolynomial.X (1 : Fin 2) ^ t := by
        rw [← MvPolynomial.C_mul_X_pow_eq_monomial (s := (0 : Fin 2)) (a := c)]
      _ = MvPolynomial.monomial
          (Finsupp.single (0 : Fin 2) (8 - t) + Finsupp.single (1 : Fin 2) t) c := by
        rw [← MvPolynomial.monomial_add_single]
  rw [hmon, MvPolynomial.coeff_monomial]
  have heq : Finsupp.single (0 : Fin 2) (8 - t) + Finsupp.single (1 : Fin 2) t =
      Finsupp.single (0 : Fin 2) (8 - s) + Finsupp.single (1 : Fin 2) s ↔ t = s := by
    constructor
    · intro h
      have := congrArg (fun d : Fin 2 →₀ ℕ => d (1 : Fin 2)) h
      simpa using this
    · intro h
      subst s
      rfl
  by_cases h : t = s
  · subst s
    simp
  · have hne : Finsupp.single (0 : Fin 2) (8 - t) + Finsupp.single (1 : Fin 2) t ≠
        Finsupp.single (0 : Fin 2) (8 - s) + Finsupp.single (1 : Fin 2) s :=
      fun he => h (heq.mp he)
    split_ifs with he
    · exact (hne he).elim
    · simp

private theorem rename_pairTerm (c : ℂ) (j k : Fin 5) :
    MvPolynomial.rename (Prod.snd : Fin 2 × Fin 2 → Fin 2)
      (MvPolynomial.C (σ := Fin 2 × Fin 2) c *
        MvPolynomial.X ((0 : Fin 2), 0) ^ (4 - j.val) *
        MvPolynomial.X (0, 1) ^ j.val * MvPolynomial.X (1, 0) ^ (4 - k.val) *
        MvPolynomial.X (1, 1) ^ k.val) =
      MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ (8 - (j.val + k.val)) *
        MvPolynomial.X 1 ^ (j.val + k.val) := by
  simp only [map_mul, map_pow, MvPolynomial.rename_C, MvPolynomial.rename_X]
  calc
    _ = MvPolynomial.C c *
        (MvPolynomial.X (0 : Fin 2) ^ (4 - j.val) * MvPolynomial.X 0 ^ (4 - k.val)) *
        (MvPolynomial.X (1 : Fin 2) ^ j.val * MvPolynomial.X 1 ^ k.val) := by ring
    _ = MvPolynomial.C c * MvPolynomial.X 0 ^ ((4 - j.val) + (4 - k.val)) *
        MvPolynomial.X 1 ^ (j.val + k.val) := by rw [← pow_add, ← pow_add]
    _ = _ := by
      have hj : j.val ≤ 4 := by omega
      have hk : k.val ≤ 4 := by omega
      have hexp : (4 - j.val) + (4 - k.val) = 8 - (j.val + k.val) := by omega
      rw [hexp]

private theorem pairDiagonal_coeff (c : Fin 5 → Fin 5 → ℂ) (s : Fin 9) :
    (MvPolynomial.rename Prod.snd (inputPoly c)).coeff
      (Finsupp.single 0 (8 - s.val) + Finsupp.single 1 s.val) = diagonalSum c s := by
  classical
  simp only [inputPoly, map_sum, MvPolynomial.coeff_sum]
  simp_rw [rename_pairTerm]
  simp_rw [coeff_pairTerm]
  simp [diagonalSum]

private theorem finite_division (c : Fin 5 → Fin 5 → ℂ)
    (hdiag : ∀ s : Fin 9, diagonalSum c s = 0) :
    inputPoly c =
      (MvPolynomial.X (0, 0) * MvPolynomial.X (1, 1) -
        MvPolynomial.X (0, 1) * MvPolynomial.X (1, 0)) * quotientPoly c := by
  classical
  have h0 : c 0 0 = 0 := by simpa [diagonalSum, Fin.sum_univ_succ] using hdiag 0
  have h1 : c 0 1 + c 1 0 = 0 := by simpa [diagonalSum, Fin.sum_univ_succ] using hdiag 1
  have h2 : c 0 2 + (c 1 1 + c 2 0) = 0 := by
    simpa [diagonalSum, Fin.sum_univ_succ] using hdiag 2
  have h3 : c 0 3 + (c 1 2 + (c 2 1 + c 3 0)) = 0 := by
    simpa [diagonalSum, Fin.sum_univ_succ] using hdiag 3
  have h4 : c 0 4 + (c 1 3 + (c 2 2 + (c 3 1 + c 4 0))) = 0 := by
    simpa [diagonalSum, Fin.sum_univ_succ] using hdiag 4
  have h5 : c 1 4 + (c 2 3 + (c 3 2 + c 4 1)) = 0 := by
    simpa [diagonalSum, Fin.sum_univ_succ] using hdiag 5
  have h6 : c 2 4 + (c 3 3 + c 4 2) = 0 := by
    simpa [diagonalSum, Fin.sum_univ_succ] using hdiag 6
  have h7 : c 3 4 + c 4 3 = 0 := by
    simpa [diagonalSum, Fin.sum_univ_succ] using hdiag 7
  have h8 : c 4 4 = 0 := by simpa [diagonalSum, Fin.sum_univ_succ] using hdiag 8
  have hp0 : MvPolynomial.C (σ := Fin 2 × Fin 2) (c 0 0) * MvPolynomial.X (0, 0)^4 * MvPolynomial.X (1, 0)^4 = 0 := by rw [h0]; simp
  have hp1 : MvPolynomial.C (σ := Fin 2 × Fin 2) (c 0 1 + c 1 0) * MvPolynomial.X (0, 0)^3 * MvPolynomial.X (0, 1) * MvPolynomial.X (1, 0)^4 = 0 := by rw [h1]; simp
  have hp2 : MvPolynomial.C (σ := Fin 2 × Fin 2) (c 0 2 + (c 1 1 + c 2 0)) * MvPolynomial.X (0, 0)^2 * MvPolynomial.X (0, 1)^2 * MvPolynomial.X (1, 0)^4 = 0 := by rw [h2]; simp
  have hp3 : MvPolynomial.C (σ := Fin 2 × Fin 2) (c 0 3 + (c 1 2 + (c 2 1 + c 3 0))) * MvPolynomial.X (0, 0) * MvPolynomial.X (0, 1)^3 * MvPolynomial.X (1, 0)^4 = 0 := by rw [h3]; simp
  have hp4 : MvPolynomial.C (σ := Fin 2 × Fin 2) (c 0 4 + (c 1 3 + (c 2 2 + (c 3 1 + c 4 0)))) * MvPolynomial.X (0, 1)^4 * MvPolynomial.X (1, 0)^4 = 0 := by rw [h4]; simp
  have hp5 : MvPolynomial.C (σ := Fin 2 × Fin 2) (c 1 4 + (c 2 3 + (c 3 2 + c 4 1))) * MvPolynomial.X (0, 1)^4 * MvPolynomial.X (1, 0)^3 * MvPolynomial.X (1, 1) = 0 := by rw [h5]; simp
  have hp6 : MvPolynomial.C (σ := Fin 2 × Fin 2) (c 2 4 + (c 3 3 + c 4 2)) * MvPolynomial.X (0, 1)^4 * MvPolynomial.X (1, 0)^2 * MvPolynomial.X (1, 1)^2 = 0 := by rw [h6]; simp
  have hp7 : MvPolynomial.C (σ := Fin 2 × Fin 2) (c 3 4 + c 4 3) * MvPolynomial.X (0, 1)^4 * MvPolynomial.X (1, 0) * MvPolynomial.X (1, 1)^3 = 0 := by rw [h7]; simp
  have hp8 : MvPolynomial.C (σ := Fin 2 × Fin 2) (c 4 4) * MvPolynomial.X (0, 1)^4 * MvPolynomial.X (1, 1)^4 = 0 := by rw [h8]; simp
  simp only [map_add] at hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8
  simp [inputPoly, quotientPoly, quotientCoeff, Fin.sum_univ_succ]
  linear_combination hp0 + hp1 + hp2 + hp3 + hp4 + hp5 + hp6 + hp7 + hp8

private def pairCoefficients (ψ : PairHilbert) : Fin 5 → Fin 5 → ℂ := fun j k =>
  ψ (j, k) * (Real.sqrt (Nat.choose 4 j.val : ℝ) : ℂ) *
    (Real.sqrt (Nat.choose 4 k.val : ℝ) : ℂ)

theorem main : AKLT.Blueprint.Q.PairDiagonalDivisionStatement := by
  classical
  intro ψ hzero
  let c := pairCoefficients ψ
  have hdiag : ∀ s : Fin 9, diagonalSum c s = 0 := by
    intro s
    have hcoeff := congrArg (fun p : MvPolynomial (Fin 2) ℂ =>
      p.coeff (Finsupp.single 0 (8 - s.val) + Finsupp.single 1 s.val)) hzero
    change (MvPolynomial.rename Prod.snd (pairPolynomial ψ)).coeff _ = 0 at hcoeff
    have hInput : pairPolynomial ψ = inputPoly c := by
      simp [inputPoly, pairPolynomial, pairCoefficients, c, mul_assoc]
    rw [hInput, pairDiagonal_coeff c s] at hcoeff
    simpa [diagonalSum, c, pairCoefficients] using hcoeff
  have hfactor : pairPolynomial ψ = pairSinglet * quotientPoly c := by
    have hInput : pairPolynomial ψ = inputPoly c := by
      simp [inputPoly, pairPolynomial, pairCoefficients, c, mul_assoc]
    rw [hInput]
    exact finite_division c hdiag
  exact ⟨quotientPoly c, hfactor⟩

#print axioms main

end AKLT.W.Q024
