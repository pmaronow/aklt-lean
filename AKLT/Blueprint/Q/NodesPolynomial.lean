module
public import AKLT.Blueprint.Q.Definitions

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.Blueprint.Q

/-- `d:poly`, sec3 lines 74–76, and `l:quantumfibre`, lines 575–578:
evaluation of the physical polynomial agrees with frozen coordinates. -/
def StateEvaluationStatement : Prop :=
  ∀ L N : Size, ∀ ψ : Hilbert L N, ∀ z : Site L N → Spinor,
    MvPolynomial.eval (fun v => z v.1 v.2) (statePolynomial ψ) = physicalEval ψ z

/-- `p:toruskernel`, sec3 lines 199–205, used only to evaluate B here:
the product is homogeneous of degree four at each site, including periods three.
Count the four incident factors; this node makes no kernel assertion. -/
def VbsHomogeneityStatement : Prop :=
  ∀ L N : Size, siteHomogeneous (vbsPolynomial L N) (fun _ => 4)

/-- `d:poly` / frozen B coordinates, used at sec3 line 583:
homogeneous coefficients reconstruct exactly after dividing then multiplying
by positive square roots of choose(4,j). The zero polynomial is allowed. -/
def CoefficientReconstructionStatement : Prop :=
  ∀ L N : Size, ∀ p : SpinorPolynomial L N,
    siteHomogeneous p (fun _ => 4) → statePolynomial (polynomialState p) = p

/-- `l:edge`, sec3 lines 112–124: the 25-dimensional pair Casimir's eigenvalue-20
space is the orthogonal complement of the diagonal-evaluation kernel.
Use the explicit spin matrices and nine diagonal coefficient vectors; this
isolates the representation/normalization bridge from polynomial division. -/
def PairSpinFourStatement : Prop :=
  Module.End.eigenspace pairCasimir 20 = (LinearMap.ker pairDiagonal)ᗮ

/-- `l:edge`, lines 100–109: vanishing on the diagonal implies divisibility
by the determinant for bidegree (4,4). An explicit 25-to-9 coefficient
elimination or the dimension-16 multiplication image proves this fixed-size step. -/
def PairDiagonalDivisionStatement : Prop :=
  ∀ ψ : PairHilbert, pairDiagonal ψ = 0 → pairSinglet ∣ pairPolynomial ψ

/-- `l:edge`, lines 128–134: expand spectator coordinates and apply the
two-site kernel implication coefficient by coefficient. The premise is
the explicit finite pair fact, not a closed leaf used as an assumption. -/
def SpectatorDivisibilityStatement : Prop :=
  (∀ v : PairHilbert, pairProjector v = 0 → pairSinglet ∣ pairPolynomial v) →
  ∀ L N : Size, ∀ e : Bond L N, ∀ ψ : Hilbert L N,
    P e ψ = 0 → singlet e ∣ statePolynomial ψ

/-- `l:divisibility`, sec3 lines 154–165: each actual edge determinant is prime
in the full multivariate polynomial ring. Use a primitive linear polynomial
over the other variables and Gauss, then an injective variable renaming. -/
def SingletPrimeStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, Prime (singlet e)

/-- `l:divisibility`, lines 167–170: distinct unoriented bonds have nonassociate
determinants. Compare variable supports; all polynomial units are nonzero constants. -/
def SingletNonassociateStatement : Prop :=
  ∀ L N : Size, ∀ e f : Bond L N, e ≠ f → ¬ Associated (singlet e) (singlet f)

/-- `l:divisibility`, lines 171–174: multiply distinct prime divisors.
No factoriality assumption is needed once primality is supplied. -/
def PrimeProductStatement : Prop :=
  ∀ (ι : Type) [Fintype ι], ∀ (R : Type) [CommRing R] [IsDomain R],
    ∀ q : ι → R, (∀ i, Prime (q i)) →
      (∀ i j, i ≠ j → ¬ Associated (q i) (q j)) →
      ∀ p : R, (∀ i, q i ∣ p) → (∏ i, q i) ∣ p

/-- `l:quantumfibre`, sec3 lines 625–626: positivity of each orthogonal
projection makes a zero incident-star sum annihilate each incident edge. -/
def IncidentKernelStatement : Prop :=
  ∀ L N : Size, ∀ x : Site L N, ∀ ψ : Hilbert L N,
    siteHamiltonian x ψ = 0 → ∀ e : Bond L N, x ∈ bondSites e → P e ψ = 0

/-- `l:divisibility`, sec3 lines 176–188, specialized to R={x}:
degree-four saturation makes any quotient by all four incident determinants
independent of the center. Nonzero divisor cancellation also handles ψ=0. -/
def IncidentDegreeStatement : Prop :=
  ∀ L N : Size, ∀ x : Site L N, ∀ ψ : Hilbert L N, ∀ χ : SpinorPolynomial L N,
    statePolynomial ψ = incidentProduct x * χ → independentAt x χ

theorem primeProduct : PrimeProductStatement := by
  classical
  intro ι _ R _ _ q hq hNonassoc p hd
  have hfin : ∀ s : Finset ι, (∏ i ∈ s, q i) ∣ p := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s has ih =>
      rw [Finset.prod_insert has]
      obtain ⟨r, hr⟩ := ih
      have hdiv : q a ∣ (∏ i ∈ s, q i) * r := by rw [← hr]; exact hd a
      rcases (hq a).dvd_mul.mp hdiv with hprod | hrest
      · obtain ⟨b, hbs, hab⟩ := ((hq a).dvd_finsetProd_iff q).mp hprod
        exact False.elim (hNonassoc a b (by intro h; subst b; exact has hbs)
          ((hq a).associated_of_dvd (hq b) hab))
      · obtain ⟨k, hk⟩ := hrest
        refine ⟨k, ?_⟩
        rw [hr, hk]
        ring
  exact hfin Finset.univ

end AKLT.Blueprint.Q
