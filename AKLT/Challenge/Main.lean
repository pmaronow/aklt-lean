module
public import Mathlib

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-!
# The square-lattice spin-2 AKLT model

Definition 1.1 (`d:model`, `sec1-result.tex`) specifies the torus, bonds,
determinant, VBS product, and Hamiltonian. Definition 3.1 (`d:poly`,
`sec3-quantum-frames.tex`) specifies the polynomial model and its norm.
The main theorem is Theorem 1.2 (`t:main`, `sec1-result.tex`).
Only Mathlib is imported.
-/

noncomputable section

open scoped BigOperators

namespace AKLT.Challenge

/-- The periods in Definition 1.1: natural numbers at least three. -/
abbrev Size := {n : ℕ // 3 ≤ n}

/-- The lower bound on each period supplies a nonzero modulus for finite `ZMod` instances. -/
@[expose] instance size_neZero (L : Size) : NeZero L.val := ⟨by have := L.property; omega⟩

/-- The torus Λ_{L,N} = ℤ/Lℤ × ℤ/Nℤ of Definition 1.1. -/
abbrev Site (L N : Size) := ZMod L.val × ZMod N.val

/-- The positive coordinate directions in Definition 1.1: `0` is horizontal, `1` vertical. -/
abbrev Direction := Fin 2

/-- Each unoriented nearest-neighbor bond of Definition 1.1 is indexed once by its
initial site and positive direction. The bound in `Size` excludes loops and repetitions. -/
abbrev Bond (L N : Size) := Site L N × Direction

/-- The terminal endpoint of a positively oriented bond in Definition 1.1. -/
def nextSite {L N : Size} (x : Site L N) (d : Direction) : Site L N :=
  if d = 0 then (x.1 + 1, x.2) else (x.1, x.2 + 1)

/-- The underlying unordered bond of Definition 1.1; orientation fixes only
the sign of its determinant factor q_e. -/
def bondSites {L N : Size} (e : Bond L N) : Finset (Site L N) :=
  {e.1, nextSite e.1 e.2}

/-- Spin 2 in the orthonormal coordinates e_k = √(choose 4 k) z₁^(4-k) z₂^k
of Definition 3.1, for k = 0,…,4. This is Sym⁴ ℂ² with the SU(2) action
f(z) ↦ f(g⁻¹z). Its standard ℓ² inner product is the paper's inner product,
not the unweighted monomial inner product. -/
abbrev V := EuclideanSpace ℂ (Fin 5)

/-- J_z in the spin-2 basis of Definition 3.1, with magnetic labels 2-k.
Together with `spinPlus` and `spinMinus`, this fixes the concrete model of V.
The label of e_k under spinZ is the negative of the paper's displayed weight
for z₁^(4-k) z₂^k; this relabeling preserves the Casimir, projection, and Hamiltonian. -/
def spinZ : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => if i = j then (2 : ℂ) - (i.val : ℂ) else 0

/-- J₊ e_k = √(k(5-k)) e_{k-1}, with missing boundary entries zero.
These are the degree-four symmetric-power spin matrices of Definition 3.1. -/
def spinPlus : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => if i.val + 1 = j.val then
    (Real.sqrt ((j.val * (5 - j.val) : ℕ) : ℝ) : ℂ) else 0

/-- J₋ = J₊* in the model of Definition 3.1.
In particular, J² = J_z² + (J₊J₋ + J₋J₊)/2 = 6I. -/
def spinMinus : Matrix (Fin 5) (Fin 5) ℂ := spinPlus.conjTranspose

/-- Tensor-product basis labels for ⊗_x V in Definition 1.1. -/
abbrev Configuration (L N : Size) := Site L N → Fin 5

/-- The finite-dimensional Hilbert space ℋ_Λ of Definition 1.1, with the
standard sum inner product in its orthonormal tensor-product coordinates. -/
abbrev Hilbert (L N : Size) := EuclideanSpace ℂ (Configuration L N)

/-- A single-site matrix tensored with the identity at every other site,
as in Definition 1.1. Off-site Kronecker deltas are written as equality of configurations. -/
def atSite {L N : Size} (A : Matrix (Fin 5) (Fin 5) ℂ) (x : Site L N) :
    Module.End ℂ (Hilbert L N) :=
  Matrix.toEuclideanLin fun σ τ =>
    if ∀ y, y ≠ x → σ y = τ y then A (σ x) (τ x) else 0

/-- A component of the total spin at the two endpoints of a bond in Definition 1.1. -/
def onBond {L N : Size} (A : Matrix (Fin 5) (Fin 5) ℂ) (e : Bond L N) :
    Module.End ℂ (Hilbert L N) :=
  atSite A e.1 + atSite A (nextSite e.1 e.2)

/-- The bond's total-spin square in Definition 1.1, written
Z² + (J₊J₋ + J₋J₊)/2. All components act on the two endpoints,
all spectator factors are identities, and multiplication composes maps. -/
def bondCasimir {L N : Size} (e : Bond L N) : Module.End ℂ (Hilbert L N) :=
  let Z := onBond spinZ e
  let U := onBond spinPlus e
  let D := onBond spinMinus e
  Z * Z + (1 / 2 : ℂ) • (U * D + D * U)

/-- The eigenvalue 4(4+1)=20 subspace of the bond Casimir in Definition 1.1:
the spin-4 summand of V_x ⊗ V_y tensored with all spectator factors. -/
def spin4Space {L N : Size} (e : Bond L N) : Submodule ℂ (Hilbert L N) :=
  Module.End.eigenspace (bondCasimir e) 20

/-- The orthogonal projection onto the specified spin-4 space in Definition 1.1.
Finite dimension supplies the projection without spectral choices. -/
def P {L N : Size} (e : Bond L N) : Module.End ℂ (Hilbert L N) :=
  (spin4Space e).starProjection.toLinearMap

/-- The spin-2 AKLT Hamiltonian of Definition 1.1, with coefficient one per bond. -/
def H (L N : Size) : Module.End ℂ (Hilbert L N) := ∑ e : Bond L N, P e

/-- The polynomial ring in two spinor variables per site, as used in Definition 3.1. -/
abbrev SpinorPolynomial (L N : Size) := MvPolynomial (Site L N × Fin 2) ℂ

/-- The determinant q_xy = z_{x,1}z_{y,2} - z_{x,2}z_{y,1} of Definition 1.1,
using zero-based variable indices and the positive-coordinate orientation. -/
def singlet {L N : Size} (e : Bond L N) : SpinorPolynomial L N :=
  let y := nextSite e.1 e.2
  MvPolynomial.X (e.1, 0) * MvPolynomial.X (y, 1) -
    MvPolynomial.X (e.1, 1) * MvPolynomial.X (y, 0)

/-- The unnormalized VBS product ∏_e q_e of Definition 1.1.
Four incident bonds per site give degree four at every site. -/
def vbsPolynomial (L N : Size) : SpinorPolynomial L N :=
  ∏ e : Bond L N, singlet e

/-- The exponent vector of the basis monomial ∏_x z_{x,1}^(4-σ_x) z_{x,2}^σ_x
from Definition 3.1. -/
def monomialDegree {L N : Size} (σ : Configuration L N) :
    (Site L N × Fin 2) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p =>
    if p.2 = 0 then 4 - (σ p.1).val else (σ p.1).val

/-- The VBS vector of Definition 1.1, in the orthonormal basis fixed by `V`.
Divide monomial coefficients by ∏_x √(choose 4 σ_x) to change coordinates,
without a global normalization or rescaling of the polynomial. -/
def B (L N : Size) : Hilbert L N :=
  WithLp.toLp 2 fun σ =>
    (vbsPolynomial L N).coeff (monomialDegree σ) /
      ∏ x : Site L N, (Real.sqrt (Nat.choose 4 (σ x).val : ℝ) : ℂ)


end AKLT.Challenge
