import AKLT.Defs.Frame
import AKLT.Challenge.Main

noncomputable section
open scoped BigOperators

namespace AKLT.Defs

/-- `d:poly`: ordinary monomial coefficients of homogeneous binary forms of degree d. -/
abbrev BinaryForm (d : ℕ) := Fin (d + 1) → ℂ

/-- `d:poly`: the prescribed monomial norm, including inverse binomial weights. -/
def binaryNormSq (d : ℕ) (p : BinaryForm d) : ℝ :=
  ∑ j, Complex.normSq (p j) / (Nat.choose d j.val : ℝ)

/-- Evaluation of a binary form in its two spinor coordinates. -/
def binaryEval (d : ℕ) (p : BinaryForm d) (z : Spinor) : ℂ :=
  ∑ j, p j * z 0 ^ (d - j.val) * z 1 ^ j.val

/-- The actual polynomial represented by the finite coefficient array. -/
def binaryPolynomial (d : ℕ) (p : BinaryForm d) : MvPolynomial (Fin 2) ℂ :=
  ∑ j, MvPolynomial.C (p j) * MvPolynomial.X 0 ^ (d - j.val) *
    MvPolynomial.X 1 ^ j.val

/-- Inverse-matrix substitution helper. The paper's action is the restricted
`binaryActionPolynomial` below. -/
def binaryInverseSubstitutionPolynomial (d : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ)
    (p : BinaryForm d) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => ∑ j, MvPolynomial.C (g⁻¹ i j) * MvPolynomial.X j) (binaryPolynomial d p)

/-- `d:poly`: the paper's SU(2) action, `p(z) ↦ p(g⁻¹ z)`.
The special-unitary domain excludes singular and nonunitary substitutions. -/
def binaryActionPolynomial (d : ℕ) (g : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (p : BinaryForm d) : MvPolynomial (Fin 2) ℂ :=
  binaryInverseSubstitutionPolynomial d (g : Matrix (Fin 2) (Fin 2) ℂ) p

/-- `d:poly`: evaluate a frozen physical vector in ordinary monomial coordinates.
The square-root binomial factors undo the frozen orthonormal coordinate conversion. -/
def physicalEval {L N : AKLT.Challenge.Size} (ψ : AKLT.Challenge.Hilbert L N)
    (z : AKLT.Challenge.Site L N → Spinor) : ℂ :=
  ∑ σ : AKLT.Challenge.Configuration L N, ψ σ *
    ∏ x, (Real.sqrt (Nat.choose 4 (σ x).val : ℝ) : ℂ) *
      z x 0 ^ (4 - (σ x).val) * z x 1 ^ (σ x).val

/-- `d:model`: no second Hamiltonian is defined; this is the frozen H. -/
abbrev hamiltonian := AKLT.Challenge.H

/-- `d:model`: no second VBS state is defined; this is the frozen B. -/
abbrev vbs := AKLT.Challenge.B

end AKLT.Defs
