module

public import Mathlib

/-! The unconditional spin-2 square-lattice AKLT headline.
Definitions are copied faithfully from the statement layers;
no certificate or analytic proof module is imported. See FIDELITY.md. -/

@[expose] public section
set_option backward.proofsInPublic true
noncomputable section
open scoped BigOperators ENNReal

/- Statement source: AKLT/Challenge/Main.lean. -/
/- Reset only Lean’s auxiliary-proof cache at the original source boundary,
preserving generated proof names. All declarations remain kernel checked. -/
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace AKLT.Challenge

/-- Side lengths in the domain of §1: natural numbers at least three. -/
abbrev Size := {n : ℕ // 3 ≤ n}

/-- The §1 side bound supplies a nonzero modulus for finite `ZMod` instances. -/
@[expose] instance size_neZero (L : Size) : NeZero L.val := ⟨by have := L.property; omega⟩

/-- The torus Λ_{L,N} = ℤ/Lℤ × ℤ/Nℤ (§1, before (`d:model`, `sec1-result.tex`)). -/
abbrev Site (L N : Size) := ZMod L.val × ZMod N.val

/-- Positive coordinate directions: `0` is horizontal, `1` vertical. -/
abbrev Direction := Fin 2

/-- Each unoriented nearest-neighbor bond is indexed once by its initial
site and positive direction. The bound in `Size` excludes loops and repetitions. -/
abbrev Bond (L N : Size) := Site L N × Direction

/-- The terminal endpoint of a positively oriented bond (§1, the set E). -/
def nextSite {L N : Size} (x : Site L N) (d : Direction) : Site L N :=
  if d = 0 then (x.1 + 1, x.2) else (x.1, x.2 + 1)

/-- Spin 2 in orthonormal coordinates e_k = √(choose 4 k) z₁^(4-k) z₂^k,
k = 0,…,4. This is Sym⁴ ℂ² with the SU(2) action f(z) ↦ f(g⁻¹z),
unitary for (`d:poly`, `sec3-quantum-frames.tex`). Thus the standard ℓ² inner product here is precisely
the paper's inner product, not the unweighted monomial inner product. -/
abbrev V := EuclideanSpace ℂ (Fin 5)

/-- J_z in the standard spin-2 basis, with magnetic labels 2-k.
Together with `spinPlus` and `spinMinus` this fixes the concrete model of V. -/
def spinZ : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => if i = j then (2 : ℂ) - (i.val : ℂ) else 0

/-- J₊ e_k = √(k(5-k)) e_{k-1}; missing boundary entries are zero.
These are the usual degree-four symmetric-power spin matrices (§1, spin 2). -/
def spinPlus : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => if i.val + 1 = j.val then
    (Real.sqrt ((j.val * (5 - j.val) : ℕ) : ℝ) : ℂ) else 0

/-- J₋ = J₊*. In particular J² = J_z² + (J₊J₋ + J₋J₊)/2 = 6I. -/
def spinMinus : Matrix (Fin 5) (Fin 5) ℂ := spinPlus.conjTranspose

/-- Tensor-product basis labels for ⊗_x V (§1, before (`d:model`, `sec1-result.tex`)). -/
abbrev Configuration (L N : Size) := Site L N → Fin 5

/-- The finite-dimensional Hilbert space ℋ_Λ, with the standard sum inner
product on its tensor-product orthonormal coordinates (§1; §2, (`d:poly`, `sec3-quantum-frames.tex`)). -/
abbrev Hilbert (L N : Size) := EuclideanSpace ℂ (Configuration L N)

/-- A single-site matrix tensored with the identity at every other site.
The off-site Kronecker deltas are written as equality of configurations. -/
def atSite {L N : Size} (A : Matrix (Fin 5) (Fin 5) ℂ) (x : Site L N) :
    Module.End ℂ (Hilbert L N) :=
  Matrix.toEuclideanLin fun σ τ =>
    if ∀ y, y ≠ x → σ y = τ y then A (σ x) (τ x) else 0

/-- A component of the total spin at the endpoints of e (§1, P_e). -/
def onBond {L N : Size} (A : Matrix (Fin 5) (Fin 5) ℂ) (e : Bond L N) :
    Module.End ℂ (Hilbert L N) :=
  atSite A e.1 + atSite A (nextSite e.1 e.2)

/-- (J_x + J_y)² = Z² + (J₊J₋ + J₋J₊)/2, where the components in
this formula are total components on the bond. Multiplication composes maps.
All other tensor factors are identities (§1, total-spin-4 subspace). -/
def bondCasimir {L N : Size} (e : Bond L N) : Module.End ℂ (Hilbert L N) :=
  let Z := onBond spinZ e
  let U := onBond spinPlus e
  let D := onBond spinMinus e
  Z * Z + (1 / 2 : ℂ) • (U * D + D * U)

/-- The eigenvalue 4(4+1)=20 space of the bond Casimir: the total-spin-4
summand of V_x ⊗ V_y tensored with all spectator factors (§1, P_e). -/
def spin4Space {L N : Size} (e : Bond L N) : Submodule ℂ (Hilbert L N) :=
  Module.End.eigenspace (bondCasimir e) 20

/-- P_e of §1: the orthogonal projection onto the specified spin-4 space.
Finite dimension supplies the orthogonal projection with no spectral choices. -/
def P {L N : Size} (e : Bond L N) : Module.End ℂ (Hilbert L N) :=
  (spin4Space e).starProjection.toLinearMap

/-- The spin-2 AKLT Hamiltonian, exactly (`d:model`, `sec1-result.tex`), with coefficient one per bond. -/
def H (L N : Size) : Module.End ℂ (Hilbert L N) := ∑ e : Bond L N, P e

/-- The polynomial ring in the two spinor variables at each site (`d:poly`, `sec3-quantum-frames.tex`). -/
abbrev SpinorPolynomial (L N : Size) := MvPolynomial (Site L N × Fin 2) ℂ

/-- q_xy = z_{x,1}z_{y,2} - z_{x,2}z_{y,1}, using zero-based variable
indices and the positive-coordinate orientation (§2, immediately before (`d:model`, `sec1-result.tex`)). -/
def singlet {L N : Size} (e : Bond L N) : SpinorPolynomial L N :=
  let y := nextSite e.1 e.2
  MvPolynomial.X (e.1, 0) * MvPolynomial.X (y, 1) -
    MvPolynomial.X (e.1, 1) * MvPolynomial.X (y, 0)

/-- The unnormalised VBS polynomial ∏_e q_e, exactly (`d:model`, `sec1-result.tex`).
There are four incident bonds per site, hence degree four at every site. -/
def vbsPolynomial (L N : Size) : SpinorPolynomial L N :=
  ∏ e : Bond L N, singlet e

/-- The exponent vector of ∏_x z_{x,1}^(4-σ_x) z_{x,2}^σ_x (§2, (`d:model`, `sec1-result.tex`)). -/
def monomialDegree {L N : Size} (σ : Configuration L N) :
    (Site L N × Fin 2) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p =>
    if p.2 = 0 then 4 - (σ p.1).val else (σ p.1).val

/-- B of (`d:model`, `sec1-result.tex`), expressed in the orthonormal basis fixed in `V`.
Divide monomial coefficients by ∏_x √(choose 4 σ_x) to change coordinates;
no global normalization or rescaling of the polynomial is introduced. -/
def B (L N : Size) : Hilbert L N :=
  WithLp.toLp 2 fun σ =>
    (vbsPolynomial L N).coeff (monomialDegree σ) /
      ∏ x : Site L N, (Real.sqrt (Nat.choose 4 (σ x).val : ℝ) : ℂ)

end AKLT.Challenge

/- Statement source: AKLT/Challenge/MainV2.lean. -/
/- Reset only Lean’s auxiliary-proof cache at the original source boundary,
preserving generated proof names. All declarations remain kernel checked. -/
run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})
namespace AKLT.Challenge

/-- `t:main`: for every torus with both periods at least three, the VBS vector
is nonzero and spans the kernel. There are a positive constant and one size
threshold above which every nonzero eigenvalue has that uniform lower bound.
Both assertions allow every parity; uniqueness has no eventual-size restriction.
The subtype `Size` already expresses the lower bound three on each period. -/
def MainStatementV2 : Prop :=
  (∀ L N : Size, B L N ≠ 0 ∧
    LinearMap.ker (H L N) = Submodule.span ℂ {B L N}) ∧
  ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, 3 ≤ L₀ ∧
    ∀ L N : Size, L₀ ≤ L.val → L₀ ≤ N.val →
      ∀ μ : ℝ, μ ≠ 0 → (H L N).HasEigenvalue (μ : ℂ) → c ≤ μ

end AKLT.Challenge

namespace AKLTPalomar

/-- Paper t:main: all-period ground-state uniqueness, and an eventual uniform gap. -/
def Main : Prop := AKLT.Challenge.MainStatementV2

/-- The unconditional theorem of the paper, t:main in sec1-result.tex. -/
theorem aklt_gap : Main := by
  sorry

end AKLTPalomar
