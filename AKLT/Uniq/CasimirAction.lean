module
public import AKLT.Uniq.SpinCoordinates
public import AKLT.Uniq.Casimir

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! The normalized polynomial action of the frozen two-site Casimir. -/

noncomputable section
open AKLT.Challenge

namespace AKLT.Uniq

variable {L N : Size}

theorem pderiv_commute (p : SpinorPolynomial L N) (i j : Site L N × Fin 2) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  ext d
  simp only [MvPolynomial.coeff_pderiv, Finsupp.add_apply]
  by_cases hij : i = j
  · subst j
    rfl
  · rw [show (d + Finsupp.single i 1) + Finsupp.single j 1 =
        (d + Finsupp.single j 1) + Finsupp.single i 1 by abel]
    simp [hij, Ne.symm hij]
    ring

def polyZ (e : Bond L N) (p : SpinorPolynomial L N) : SpinorPolynomial L N :=
  ((2 : ℂ) • p - MvPolynomial.X (e.1, 1) * MvPolynomial.pderiv (e.1, 1) p) +
  ((2 : ℂ) • p - MvPolynomial.X (nextSite e.1 e.2, 1) *
    MvPolynomial.pderiv (nextSite e.1 e.2, 1) p)

def polyPlus (e : Bond L N) (p : SpinorPolynomial L N) : SpinorPolynomial L N :=
  MvPolynomial.X (e.1, 0) * MvPolynomial.pderiv (e.1, 1) p +
  MvPolynomial.X (nextSite e.1 e.2, 0) * MvPolynomial.pderiv (nextSite e.1 e.2, 1) p

def polyMinus (e : Bond L N) (p : SpinorPolynomial L N) : SpinorPolynomial L N :=
  MvPolynomial.X (e.1, 1) * MvPolynomial.pderiv (e.1, 0) p +
  MvPolynomial.X (nextSite e.1 e.2, 1) * MvPolynomial.pderiv (nextSite e.1 e.2, 0) p

theorem encode_onBond_Z (e : Bond L N) (v : Hilbert L N) :
    encode (onBond spinZ e v) = polyZ e (encode v) := by
  simp only [onBond, LinearMap.add_apply, map_add, encode_spinZ, polyZ]

theorem encode_onBond_plus (e : Bond L N) (v : Hilbert L N) :
    encode (onBond spinPlus e v) = polyPlus e (encode v) := by
  simp only [onBond, LinearMap.add_apply, map_add, encode_spinPlus, polyPlus]

theorem encode_onBond_minus (e : Bond L N) (v : Hilbert L N) :
    encode (onBond spinMinus e v) = polyMinus e (encode v) := by
  simp only [onBond, LinearMap.add_apply, map_add, encode_spinMinus, polyMinus]

/-- Node S2: the two-site differential Casimir identity at total degree eight. -/
def PolynomialCasimirStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, ∀ p : SpinorPolynomial L N, IsPhysical p →
    (20 : ℂ) • p - (polyZ e (polyZ e p) + (1 / 2 : ℂ) •
      (polyPlus e (polyMinus e p) + polyMinus e (polyPlus e p))) =
        singlet e * transvectant e p

theorem polynomialCasimir : PolynomialCasimirStatement := by
  intro L N e p hp
  classical
  have hne := nextSite_ne e.1 e.2
  have hX := siteEuler (hp e.1)
  have hY := siteEuler (hp (nextSite e.1 e.2))
  have hEuler : MvPolynomial.X (e.1, 0) * MvPolynomial.pderiv (e.1, 0) p +
      MvPolynomial.X (e.1, 1) * MvPolynomial.pderiv (e.1, 1) p +
      MvPolynomial.X (nextSite e.1 e.2, 0) * MvPolynomial.pderiv (nextSite e.1 e.2, 0) p +
      MvPolynomial.X (nextSite e.1 e.2, 1) * MvPolynomial.pderiv (nextSite e.1 e.2, 1) p =
      (8 : ℂ) • p := by
    simp only [nsmul_eq_mul, MvPolynomial.smul_eq_C_mul, map_ofNat] at hX hY ⊢
    linear_combination hX + hY
  have hB := congrArg (MvPolynomial.pderiv (e.1, 1)) hEuler
  have hD := congrArg (MvPolynomial.pderiv (nextSite e.1 e.2, 1)) hEuler
  have htwo : (2 : ℂ) • ((20 : ℂ) • p -
      (polyZ e (polyZ e p) + (1 / 2 : ℂ) •
        (polyPlus e (polyMinus e p) + polyMinus e (polyPlus e p)))) =
      (2 : ℂ) • (singlet e * transvectant e p) := by
    simp [polyZ, polyPlus, polyMinus, transvectant, singlet, map_add, map_sub,
      Derivation.map_smul, MvPolynomial.pderiv_X,
      Prod.mk.injEq, hne, Ne.symm hne,
      smul_sub, smul_add, smul_smul] at hB hD ⊢
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_ofNat,
      pderiv_commute] at hEuler hB hD ⊢
    linear_combination -hEuler - 2 * MvPolynomial.X (e.1, 1) * hB -
      2 * MvPolynomial.X (nextSite e.1 e.2, 1) * hD
  have h := congrArg (fun r : SpinorPolynomial L N => (1 / 2 : ℂ) • r) htwo
  simpa only [smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] using h

/-- Node E1: exact normalized action of the frozen Casimir, including spectators. -/
def CasimirActionStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, ∀ v : Hilbert L N,
    encode (casimirDefect e v) = singlet e * transvectant e (encode v)

theorem casimirAction : CasimirActionStatement := by
  intro L N e v
  simp only [casimirDefect, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    map_sub, map_smul, bondCasimir, LinearMap.add_apply, Module.End.mul_apply,
    map_add, encode_onBond_Z, encode_onBond_plus, encode_onBond_minus]
  exact polynomialCasimir L N e (encode v) (encode_physical v)

#print axioms pderiv_commute
#print axioms encode_onBond_Z
#print axioms encode_onBond_plus
#print axioms encode_onBond_minus
#print axioms polynomialCasimir
#print axioms casimirAction

end AKLT.Uniq
