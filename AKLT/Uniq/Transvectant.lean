module
public import AKLT.Uniq.Divisibility

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! The determinant differential operator and its finite polynomial right inverse. -/

noncomputable section
open scoped BigOperators
open AKLT.Challenge

namespace AKLT.Uniq

variable {L N : Size}

/-- The two-site determinant differential operator. -/
def transvectant (e : Bond L N) (p : SpinorPolynomial L N) : SpinorPolynomial L N :=
  MvPolynomial.pderiv (e.1, 0) (MvPolynomial.pderiv (nextSite e.1 e.2, 1) p) -
  MvPolynomial.pderiv (e.1, 1) (MvPolynomial.pderiv (nextSite e.1 e.2, 0) p)

theorem transvectant_add (e : Bond L N) (p q : SpinorPolynomial L N) :
    transvectant e (p + q) = transvectant e p + transvectant e q := by
  simp only [transvectant, map_add]
  ring

theorem transvectant_sub (e : Bond L N) (p q : SpinorPolynomial L N) :
    transvectant e (p - q) = transvectant e p - transvectant e q := by
  simp only [transvectant, map_sub]
  ring

theorem transvectant_smul (e : Bond L N) (c : ℂ) (p : SpinorPolynomial L N) :
    transvectant e (c • p) = c • transvectant e p := by
  simp only [transvectant, MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_C_mul, mul_sub]

theorem siteEuler {p : SpinorPolynomial L N} {x : Site L N} {n : ℕ}
    (hp : p.IsWeightedHomogeneous (siteWeight x) n) :
    MvPolynomial.X (x, 0) * MvPolynomial.pderiv (x, 0) p +
      MvPolynomial.X (x, 1) * MvPolynomial.pderiv (x, 1) p = n • p := by
  have h := hp.sum_weight_X_mul_pderiv
  rw [Fintype.sum_prod_type] at h
  simpa [siteWeight, Fin.sum_univ_two, eq_comm] using h

theorem pderiv_zero_of_site_degree_zero {p : SpinorPolynomial L N} {x : Site L N}
    (hp : p.IsWeightedHomogeneous (siteWeight x) 0) (k : Fin 2) :
    MvPolynomial.pderiv (x, k) p = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hk
  obtain ⟨d, hd, hdk⟩ := (MvPolynomial.mem_vars_iff_mem_support (x, k)).mp hk
  have hweight := hp (MvPolynomial.mem_support_iff.mp hd)
  rw [siteWeight_degree] at hweight
  have hdk' := Finsupp.mem_support_iff.mp hdk
  fin_cases k
  · change d (x, 0) ≠ 0 at hdk'
    omega
  · change d (x, 1) ≠ 0 at hdk'
    omega

/-- Remaining physical degrees after removing `k` copies of one bond determinant. -/
def edgeResidual (e : Bond L N) (k : ℕ) (x : Site L N) : ℕ :=
  4 - k * bondDegree e x

theorem bondDegree_le_one (e : Bond L N) (x : Site L N) : bondDegree e x ≤ 1 := by
  have hne := nextSite_ne e.1 e.2
  by_cases ha : e.1 = x <;> by_cases hb : nextSite e.1 e.2 = x <;>
    simp_all [bondDegree]

theorem edgeResidual_deriv_arithmetic (e : Bond L N) {k : ℕ} (hk : k < 4) (x : Site L N) :
    (edgeResidual e k x - siteWeight x (nextSite e.1 e.2, 1)) +
        siteWeight x (nextSite e.1 e.2, 1) = edgeResidual e k x ∧
    edgeResidual e (k + 1) x + siteWeight x (e.1, 0) =
        edgeResidual e k x - siteWeight x (nextSite e.1 e.2, 1) := by
  have hne := nextSite_ne e.1 e.2
  by_cases ha : e.1 = x <;> by_cases hb : nextSite e.1 e.2 = x <;>
    simp_all [edgeResidual, bondDegree, siteWeight] <;> omega

theorem transvectant_degrees (e : Bond L N) {k : ℕ} {p : SpinorPolynomial L N}
    (hk : k < 4) (hp : HasSiteDegrees p (edgeResidual e k)) :
    HasSiteDegrees (transvectant e p) (edgeResidual e (k + 1)) := by
  intro x
  obtain ⟨hfirst, hlast⟩ := edgeResidual_deriv_arithmetic e hk x
  exact (((hp x).pderiv (i := (nextSite e.1 e.2, 1)) hfirst).pderiv
    (i := (e.1, 0)) hlast).sub
      (((hp x).pderiv (i := (nextSite e.1 e.2, 0)) hfirst).pderiv
        (i := (e.1, 1)) hlast)

theorem singlet_pow_mul_physical (e : Bond L N) {k : ℕ} (hk : k ≤ 4)
    {p : SpinorPolynomial L N} (hp : HasSiteDegrees p (edgeResidual e k)) :
    IsPhysical (singlet e ^ k * p) := by
  intro x
  have h := ((singlet_siteDegrees e x).pow k).mul (hp x)
  convert h using 1
  change 4 = k * bondDegree e x + (4 - k * bondDegree e x)
  have hle := bondDegree_le_one e x
  have : k * bondDegree e x ≤ 4 := by nlinarith
  omega

theorem edgeResidual_endpoint (e : Bond L N) (k : ℕ) :
    edgeResidual e k e.1 = 4 - k ∧
      edgeResidual e k (nextSite e.1 e.2) = 4 - k := by
  have hne := nextSite_ne e.1 e.2
  simp [edgeResidual, bondDegree, hne, Ne.symm hne]

theorem transvectant_degree_four_zero (e : Bond L N) {p : SpinorPolynomial L N}
    (hp : HasSiteDegrees p (edgeResidual e 4)) : transvectant e p = 0 := by
  have hy : p.IsWeightedHomogeneous (siteWeight (nextSite e.1 e.2)) 0 := by
    simpa only [(edgeResidual_endpoint e 4).2] using hp (nextSite e.1 e.2)
  simp only [transvectant, pderiv_zero_of_site_degree_zero hy, map_zero, sub_self]

theorem singlet_endpoint_degrees (e : Bond L N) :
    (singlet e).IsWeightedHomogeneous (siteWeight e.1) 1 ∧
    (singlet e).IsWeightedHomogeneous (siteWeight (nextSite e.1 e.2)) 1 := by
  have hne := nextSite_ne e.1 e.2
  constructor
  · simpa [bondDegree, hne] using singlet_siteDegrees e e.1
  · simpa [bondDegree, Ne.symm hne] using singlet_siteDegrees e (nextSite e.1 e.2)

/-- Determinant/transvectant commutator, the binary Euler identity. -/
theorem transvectant_singlet_mul (e : Bond L N) {p : SpinorPolynomial L N} {n : ℕ}
    (hx : p.IsWeightedHomogeneous (siteWeight e.1) n)
    (hy : p.IsWeightedHomogeneous (siteWeight (nextSite e.1 e.2)) n) :
    transvectant e (singlet e * p) = (2 * n + 2) • p + singlet e * transvectant e p := by
  classical
  have hne := nextSite_ne e.1 e.2
  have hEulerX := siteEuler hx
  have hEulerY := siteEuler hy
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hEulerX hEulerY ⊢
  simp [transvectant, singlet, MvPolynomial.pderiv_X,
    hne, Ne.symm hne, Prod.mk.injEq] at *
  linear_combination hEulerX + hEulerY

theorem transvectant_singlet_pow_mul (e : Bond L N) {p : SpinorPolynomial L N} {n : ℕ}
    (hx : p.IsWeightedHomogeneous (siteWeight e.1) n)
    (hy : p.IsWeightedHomogeneous (siteWeight (nextSite e.1 e.2)) n) (k : ℕ) :
    transvectant e (singlet e ^ (k + 1) * p) =
      ((k + 1) * (2 * n + k + 2)) • (singlet e ^ k * p) +
        singlet e ^ (k + 1) * transvectant e p := by
  induction k with
  | zero => simpa using transvectant_singlet_mul e hx hy
  | succ k ih =>
    have hx' : (singlet e ^ (k + 1) * p).IsWeightedHomogeneous
        (siteWeight e.1) (n + k + 1) := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        ((singlet_endpoint_degrees e).1.pow (k + 1)).mul hx
    have hy' : (singlet e ^ (k + 1) * p).IsWeightedHomogeneous
        (siteWeight (nextSite e.1 e.2)) (n + k + 1) := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        ((singlet_endpoint_degrees e).2.pow (k + 1)).mul hy
    calc
      transvectant e (singlet e ^ (k + 1 + 1) * p) =
          transvectant e (singlet e * (singlet e ^ (k + 1) * p)) := by congr 1; ring
      _ = (2 * (n + k + 1) + 2) • (singlet e ^ (k + 1) * p) +
          singlet e * transvectant e (singlet e ^ (k + 1) * p) :=
        transvectant_singlet_mul e hx' hy'
      _ = _ := by
        rw [ih]
        simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
          pow_succ]
        ring

/-- Four-term right inverse on endpoint degree (3,3). -/
def transvectantRightInverse (e : Bond L N) (p : SpinorPolynomial L N) :
    SpinorPolynomial L N :=
  (1 / 8 : ℂ) • (singlet e * p) -
    (1 / 112 : ℂ) • (singlet e ^ 2 * transvectant e p) +
    (1 / 2016 : ℂ) • (singlet e ^ 3 * transvectant e (transvectant e p)) -
    (1 / 40320 : ℂ) •
      (singlet e ^ 4 * transvectant e (transvectant e (transvectant e p)))

theorem transvectantRightInverse_physical (e : Bond L N) {p : SpinorPolynomial L N}
    (hp : HasSiteDegrees p (edgeResidual e 1)) :
    IsPhysical (transvectantRightInverse e p) := by
  have h1 := transvectant_degrees e (k := 1) (by decide) hp
  have h2 := transvectant_degrees e (k := 2) (by decide) h1
  have h3 := transvectant_degrees e (k := 3) (by decide) h2
  have hp0 := singlet_pow_mul_physical e (k := 1) (by decide) hp
  have hp1 := singlet_pow_mul_physical e (k := 2) (by decide) h1
  have hp2 := singlet_pow_mul_physical e (k := 3) (by decide) h2
  have hp3 := singlet_pow_mul_physical e (k := 4) (by decide) h3
  intro x
  let A := MvPolynomial.weightedHomogeneousSubmodule ℂ (siteWeight x) 4
  exact ((A.smul_mem (1 / 8 : ℂ) (by
    change (singlet e * p).IsWeightedHomogeneous (siteWeight x) 4
    simpa only [pow_one] using hp0 x)).sub
    (A.smul_mem (1 / 112 : ℂ) (hp1 x))).add
      (A.smul_mem (1 / 2016 : ℂ) (hp2 x)) |>.sub
        (A.smul_mem (1 / 40320 : ℂ) (hp3 x))

theorem transvectant_rightInverse (e : Bond L N) {p : SpinorPolynomial L N}
    (hp : HasSiteDegrees p (edgeResidual e 1)) :
    transvectant e (transvectantRightInverse e p) = p := by
  have h1 := transvectant_degrees e (k := 1) (by decide) hp
  have h2 := transvectant_degrees e (k := 2) (by decide) h1
  have h3 := transvectant_degrees e (k := 3) (by decide) h2
  have hx0 : p.IsWeightedHomogeneous (siteWeight e.1) 3 := by
    simpa only [(edgeResidual_endpoint e 1).1] using hp e.1
  have hy0 : p.IsWeightedHomogeneous (siteWeight (nextSite e.1 e.2)) 3 := by
    simpa only [(edgeResidual_endpoint e 1).2] using hp (nextSite e.1 e.2)
  have hx1 : (transvectant e p).IsWeightedHomogeneous (siteWeight e.1) 2 := by
    simpa only [(edgeResidual_endpoint e 2).1] using h1 e.1
  have hy1 : (transvectant e p).IsWeightedHomogeneous (siteWeight (nextSite e.1 e.2)) 2 := by
    simpa only [(edgeResidual_endpoint e 2).2] using h1 (nextSite e.1 e.2)
  have hx2 : (transvectant e (transvectant e p)).IsWeightedHomogeneous (siteWeight e.1) 1 := by
    simpa only [(edgeResidual_endpoint e 3).1] using h2 e.1
  have hy2 : (transvectant e (transvectant e p)).IsWeightedHomogeneous
      (siteWeight (nextSite e.1 e.2)) 1 := by
    simpa only [(edgeResidual_endpoint e 3).2] using h2 (nextSite e.1 e.2)
  have hx3 : (transvectant e (transvectant e (transvectant e p))).IsWeightedHomogeneous
      (siteWeight e.1) 0 := by
    simpa only [(edgeResidual_endpoint e 4).1] using h3 e.1
  have hy3 : (transvectant e (transvectant e (transvectant e p))).IsWeightedHomogeneous
      (siteWeight (nextSite e.1 e.2)) 0 := by
    simpa only [(edgeResidual_endpoint e 4).2] using h3 (nextSite e.1 e.2)
  have hT0 := transvectant_singlet_pow_mul e hx0 hy0 0
  have hT1 := transvectant_singlet_pow_mul e hx1 hy1 1
  have hT2 := transvectant_singlet_pow_mul e hx2 hy2 2
  have hT3 := transvectant_singlet_pow_mul e hx3 hy3 3
  norm_num only [Nat.reduceAdd, Nat.reduceMul, pow_zero, pow_one, one_mul,
    transvectant_degree_four_zero e h3, mul_zero, add_zero] at hT0 hT1 hT2 hT3
  simp only [transvectantRightInverse, transvectant_add, transvectant_sub, transvectant_smul]
  rw [hT0, hT1, hT2, hT3]
  simp only [← Nat.cast_smul_eq_nsmul ℂ, smul_add, smul_smul]
  module

/-- Node E2: surjectivity of the endpoint transvectant, including spectators. -/
def TransvectantSurjectiveStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, ∀ q : SpinorPolynomial L N,
    IsPhysical (singlet e * q) →
    ∃ v : Hilbert L N, transvectant e (encode v) = q

theorem transvectantSurjective : TransvectantSurjectiveStatement := by
  classical
  intro L N e q hq
  have hdegree : HasSiteDegrees q (edgeResidual e 1) := by
    have h := quotientDegrees L N {e} q (by simpa using hq)
    intro x
    simpa [edgeResidual, residualDegree] using h x
  refine ⟨decode (transvectantRightInverse e q), ?_⟩
  rw [encode_decode (transvectantRightInverse_physical e hdegree)]
  exact transvectant_rightInverse e hdegree

#print axioms transvectant_add
#print axioms transvectant_sub
#print axioms transvectant_smul
#print axioms siteEuler
#print axioms pderiv_zero_of_site_degree_zero
#print axioms bondDegree_le_one
#print axioms edgeResidual_deriv_arithmetic
#print axioms transvectant_degrees
#print axioms singlet_pow_mul_physical
#print axioms edgeResidual_endpoint
#print axioms transvectant_degree_four_zero
#print axioms singlet_endpoint_degrees
#print axioms transvectant_singlet_mul
#print axioms transvectant_singlet_pow_mul
#print axioms transvectantRightInverse_physical
#print axioms transvectant_rightInverse
#print axioms transvectantSurjective

end AKLT.Uniq
