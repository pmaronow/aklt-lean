import AKLT.Uniq.Polynomial

/-! Exact site degrees of the VBS product, including periods three. -/

noncomputable section
open scoped BigOperators
open AKLT.Challenge

namespace AKLT.Uniq

variable {L N : Size}

/-- The inverse of positive translation in a fixed coordinate. -/
def previousSite (x : Site L N) (d : Direction) : Site L N :=
  if d = 0 then (x.1 - 1, x.2) else (x.1, x.2 - 1)

def nextSiteEquiv (L N : Size) (d : Direction) : Site L N ≃ Site L N where
  toFun x := nextSite x d
  invFun x := previousSite x d
  left_inv x := by by_cases hd : d = 0 <;> simp [nextSite, previousSite, hd]
  right_inv x := by by_cases hd : d = 0 <;> simp [nextSite, previousSite, hd]

theorem nextSite_eq_iff (x y : Site L N) (d : Direction) :
    nextSite x d = y ↔ x = previousSite y d :=
  (nextSiteEquiv L N d).eq_symm_apply.symm

/-- One degree at each endpoint, and zero at every spectator site. -/
def bondDegree (e : Bond L N) (x : Site L N) : ℕ :=
  (if e.1 = x then 1 else 0) + (if nextSite e.1 e.2 = x then 1 else 0)

theorem sum_bondDegree (x : Site L N) : ∑ e : Bond L N, bondDegree e x = 4 := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [bondDegree, Finset.sum_add_distrib]
  have hstart : (∑ y : Site L N, ∑ _d : Direction, if y = x then 1 else 0) = 2 := by
    simp
  rw [hstart, Finset.sum_comm]
  simp [nextSite_eq_iff]

/-- Node G1: simple torus bonds and the exact four-fold incidence count. -/
def TorusGeometryStatement : Prop :=
  ∀ L N : Size, Function.Injective (@bondSites L N) ∧
    (∀ e : Bond L N, e.1 ≠ nextSite e.1 e.2) ∧
    ∀ x : Site L N, ∑ e : Bond L N, bondDegree e x = 4

theorem torusGeometry : TorusGeometryStatement :=
  fun L N => ⟨bonds_areDistinct L N, fun e => (nextSite_ne e.1 e.2).symm,
    sum_bondDegree⟩

theorem singlet_siteDegrees (e : Bond L N) : HasSiteDegrees (singlet e) (bondDegree e) := by
  intro x
  apply MvPolynomial.IsWeightedHomogeneous.sub
  · exact (MvPolynomial.isWeightedHomogeneous_X ℂ (siteWeight x) (e.1, 0)).mul
      (MvPolynomial.isWeightedHomogeneous_X ℂ (siteWeight x) (nextSite e.1 e.2, 1))
  · exact (MvPolynomial.isWeightedHomogeneous_X ℂ (siteWeight x) (e.1, 1)).mul
      (MvPolynomial.isWeightedHomogeneous_X ℂ (siteWeight x) (nextSite e.1 e.2, 0))

/-- Node G2: the full product lies in the physical polynomial carrier. -/
def VBSHomogeneousStatement : Prop :=
  ∀ L N : Size, IsPhysical (vbsPolynomial L N)

theorem vbsHomogeneous : VBSHomogeneousStatement := by
  intro L N x
  rw [← sum_bondDegree x]
  exact MvPolynomial.IsWeightedHomogeneous.prod Finset.univ singlet
    (fun e => bondDegree e x) (fun e _ => singlet_siteDegrees e x)

theorem encode_B (L N : Size) : encode (B L N) = vbsPolynomial L N :=
  encode_decode (vbsHomogeneous L N)

#print axioms nextSite_eq_iff
#print axioms sum_bondDegree
#print axioms torusGeometry
#print axioms singlet_siteDegrees
#print axioms vbsHomogeneous
#print axioms encode_B

end AKLT.Uniq
