import AKLT.Uniq.Hamiltonian

/-!
The frozen Casimir is symmetric, and the kernel of its spin-four projection
is exactly the range of its defect from the eigenvalue 20.  This removes all
spectral and orthogonality obligations from the remaining polynomial bridge.
-/

noncomputable section
open AKLT.Challenge

namespace AKLT.Uniq

variable {L N : Size}

theorem atSite_adjoint (A : Matrix (Fin 5) (Fin 5) ℂ) (x : Site L N) :
    (atSite A x).adjoint = atSite A.conjTranspose x := by
  classical
  let M : Matrix (Configuration L N) (Configuration L N) ℂ :=
    fun σ τ => if ∀ y, y ≠ x → σ y = τ y then A (σ x) (τ x) else 0
  have hm : M.conjTranspose =
      (fun σ τ => if ∀ y, y ≠ x → σ y = τ y then A.conjTranspose (σ x) (τ x) else 0) := by
    ext σ τ
    have heq : (∀ y, y ≠ x → τ y = σ y) ↔ (∀ y, y ≠ x → σ y = τ y) := by
      constructor <;> intro h y hy <;> exact (h y hy).symm
    change star (if ∀ y, y ≠ x → τ y = σ y then A (τ x) (σ x) else 0) =
      if ∀ y, y ≠ x → σ y = τ y then star (A (τ x) (σ x)) else 0
    by_cases h : ∀ y, y ≠ x → σ y = τ y
    · exact (congrArg star (ite_eq_left (heq.mpr h))).trans (ite_eq_left h).symm
    · exact (congrArg star (ite_eq_right (mt heq.mp h))).trans
        ((star_zero ℂ).trans (ite_eq_right h).symm)
  exact (Matrix.toEuclideanLin_conjTranspose_eq_adjoint M).symm.trans
    (congrArg (fun T : Matrix (Configuration L N) (Configuration L N) ℂ =>
      Matrix.toEuclideanLin T) hm)

theorem onBond_adjoint (A : Matrix (Fin 5) (Fin 5) ℂ) (e : Bond L N) :
    (onBond A e).adjoint = onBond A.conjTranspose e := by
  simp [onBond, atSite_adjoint]

theorem spinZ_hermitian : spinZ.IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, spinZ]
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Ne.symm h]

theorem onBond_Z_symmetric (e : Bond L N) : (onBond spinZ e).IsSymmetric := by
  apply (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr
  rw [LinearMap.isSelfAdjoint_iff', onBond_adjoint, spinZ_hermitian.eq]

/-- Node C1: symmetry of the actual frozen Casimir on the full torus Hilbert space. -/
def CasimirSymmetricStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, (bondCasimir e).IsSymmetric

theorem casimirSymmetric : CasimirSymmetricStatement := by
  intro L N e
  have hUD : onBond spinMinus e = (onBond spinPlus e).adjoint := by
    rw [onBond_adjoint]
    rfl
  change (onBond spinZ e * onBond spinZ e + (1 / 2 : ℂ) •
    (onBond spinPlus e * onBond spinMinus e +
      onBond spinMinus e * onBond spinPlus e)).IsSymmetric
  apply LinearMap.IsSymmetric.add
  · simpa only [pow_two] using (onBond_Z_symmetric e).pow 2
  · apply LinearMap.IsSymmetric.smul (by simp only [map_div₀, map_one, map_ofNat])
    rw [hUD]
    simpa only [LinearMap.adjoint_adjoint] using
      (LinearMap.isSymmetric_adjoint_mul_self (onBond spinPlus e).adjoint).add
        (LinearMap.isSymmetric_adjoint_mul_self (onBond spinPlus e))

/-- Defect from the total-spin-four eigenvalue. -/
def casimirDefect (e : Bond L N) : Module.End ℂ (Hilbert L N) :=
  (20 : ℂ) • LinearMap.id - bondCasimir e

theorem casimirDefect_symmetric (e : Bond L N) : (casimirDefect e).IsSymmetric := by
  exact (LinearMap.IsSymmetric.id.smul (by simp only [map_ofNat])).sub
    (casimirSymmetric L N e)

theorem ker_casimirDefect (e : Bond L N) :
    LinearMap.ker (casimirDefect e) = spin4Space e := by
  ext v
  simp only [LinearMap.mem_ker, casimirDefect, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero, spin4Space, Module.End.mem_eigenspace_iff]
  exact eq_comm

/-- Node C2: the spin-four projection kernel as a polynomial-action range. -/
def ProjectionRangeStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N,
    LinearMap.ker (P e) = LinearMap.range (casimirDefect e)

theorem projectionRange : ProjectionRangeStatement := by
  intro L N e
  rw [P, Submodule.ker_starProjection, ← ker_casimirDefect,
    LinearMap.orthogonal_ker, (casimirDefect_symmetric e).adjoint_eq]

theorem projection_eq_zero_iff_range (e : Bond L N) (v : Hilbert L N) :
    P e v = 0 ↔ ∃ w : Hilbert L N, casimirDefect e w = v := by
  change v ∈ LinearMap.ker (P e) ↔ v ∈ LinearMap.range (casimirDefect e)
  rw [projectionRange]

#print axioms atSite_adjoint
#print axioms onBond_adjoint
#print axioms spinZ_hermitian
#print axioms onBond_Z_symmetric
#print axioms casimirSymmetric
#print axioms casimirDefect_symmetric
#print axioms ker_casimirDefect
#print axioms projectionRange
#print axioms projection_eq_zero_iff_range

end AKLT.Uniq
