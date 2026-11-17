module
public import AKLT.Blueprint.Q.NodesSplits

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Blueprint.Q

namespace AKLT.W.Q028

private def diagExp (n : Fin 9) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (8 - n.val) + Finsupp.single 1 n.val

private def diagMonomial (n : Fin 9) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.monomial (diagExp n) 1

private def diagIndex (j k : Fin 5) : Fin 9 :=
  ⟨j.val + k.val, by omega⟩

private def pairExp (j k : Fin 5) : (Fin 2 × Fin 2) →₀ ℕ :=
  Finsupp.single (0, 0) (4 - j.val) + Finsupp.single (0, 1) j.val +
    Finsupp.single (1, 0) (4 - k.val) + Finsupp.single (1, 1) k.val

private def pairWeight (j k : Fin 5) : ℂ :=
  (Real.sqrt (Nat.choose 4 j.val : ℝ) : ℂ) *
    (Real.sqrt (Nat.choose 4 k.val : ℝ) : ℂ)

private def diagSpace : Submodule ℂ (MvPolynomial (Fin 2) ℂ) :=
  Submodule.span ℂ (Set.range diagMonomial)

private theorem pairExp_mapDomain (j k : Fin 5) :
    Finsupp.mapDomain Prod.snd (pairExp j k) = diagExp (diagIndex j k) := by
  rw [pairExp, Finsupp.mapDomain_add, Finsupp.mapDomain_add, Finsupp.mapDomain_add]
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  ext i
  fin_cases i
  · simp [Finsupp.add_apply, diagExp, diagIndex]
    have hj : j.val ≤ 4 := by omega
    have hk : k.val ≤ 4 := by omega
    omega
  · simp [Finsupp.add_apply, diagExp, diagIndex]

private theorem pairTerm_eq (ψ : PairHilbert) (j k : Fin 5) :
    MvPolynomial.rename (fun z : Fin 2 × Fin 2 => z.2)
      (MvPolynomial.C (ψ (j, k) * pairWeight j k) *
        MvPolynomial.X (0, 0) ^ (4 - j.val) * MvPolynomial.X (0, 1) ^ j.val *
        MvPolynomial.X (1, 0) ^ (4 - k.val) * MvPolynomial.X (1, 1) ^ k.val) =
      MvPolynomial.monomial (diagExp (diagIndex j k)) (ψ (j, k) * pairWeight j k) := by
  have hsource : MvPolynomial.C (ψ (j, k) * pairWeight j k) *
        MvPolynomial.X (0, 0) ^ (4 - j.val) * MvPolynomial.X (0, 1) ^ j.val *
        MvPolynomial.X (1, 0) ^ (4 - k.val) * MvPolynomial.X (1, 1) ^ k.val =
      MvPolynomial.monomial (pairExp j k) (ψ (j, k) * pairWeight j k) := by
        rw [MvPolynomial.C_mul_X_pow_eq_monomial]
        rw [MvPolynomial.X_pow_eq_monomial]
        rw [MvPolynomial.X_pow_eq_monomial]
        rw [MvPolynomial.X_pow_eq_monomial]
        simp only [MvPolynomial.monomial_mul_monomial, pairExp, mul_one]
  calc
    _ = MvPolynomial.rename Prod.snd
        (MvPolynomial.monomial (pairExp j k) (ψ (j, k) * pairWeight j k)) := by rw [← hsource]
    _ = _ := by rw [MvPolynomial.rename_monomial, pairExp_mapDomain]

private theorem pairDiagonal_expansion (ψ : PairHilbert) :
    pairDiagonal ψ = ∑ j : Fin 5, ∑ k : Fin 5,
      MvPolynomial.monomial (diagExp (diagIndex j k)) (ψ (j, k) * pairWeight j k) := by
  change MvPolynomial.rename (fun z : Fin 2 × Fin 2 => z.2) (pairPolynomial ψ) = _
  unfold pairPolynomial
  simp only [map_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  refine Finset.sum_congr rfl ?_
  intro k hk
  simpa [pairWeight, mul_assoc] using pairTerm_eq ψ j k

private theorem diagExp_injective : Function.Injective diagExp := by
  intro a b hab
  have h := congrArg (fun e : Fin 2 →₀ ℕ => e 1) hab
  simp [diagExp] at h
  exact Fin.ext h

private theorem diagMonomial_linearIndependent :
    LinearIndependent ℂ diagMonomial := by
  exact (MvPolynomial.basisMonomials (Fin 2) ℂ).linearIndependent.comp
    diagExp diagExp_injective

private theorem diagSpace_finrank : Module.finrank ℂ diagSpace = 9 := by
  change Module.finrank ℂ (Submodule.span ℂ (Set.range diagMonomial)) = 9
  rw [finrank_span_eq_card diagMonomial_linearIndependent]
  rfl

private theorem pairDiagonal_range_le_diagSpace :
    LinearMap.range pairDiagonal ≤ diagSpace := by
  rintro p ⟨ψ, rfl⟩
  rw [pairDiagonal_expansion]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.sum_mem
  intro k hk
  have hcoeff : MvPolynomial.monomial (diagExp (diagIndex j k))
      (ψ (j, k) * pairWeight j k) =
        (ψ (j, k) * pairWeight j k) • diagMonomial (diagIndex j k) := by
    simp [diagMonomial, MvPolynomial.smul_monomial]
  rw [hcoeff]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨diagIndex j k, rfl⟩)

private def chosenJ (n : Fin 9) : Fin 5 :=
  ⟨n.val - 4, by omega⟩

private def chosenK (n : Fin 9) : Fin 5 :=
  ⟨min n.val 4, by omega⟩

private theorem chosen_sum (n : Fin 9) :
    diagIndex (chosenJ n) (chosenK n) = n := by
  apply Fin.ext
  simp [diagIndex, chosenJ, chosenK]

private theorem pairWeight_ne_zero (j k : Fin 5) : pairWeight j k ≠ 0 := by
  apply mul_ne_zero
  · apply Complex.ofReal_ne_zero.mpr
    apply Real.sqrt_ne_zero'.2
    exact_mod_cast Nat.choose_pos (by omega : j.val ≤ 4)
  · apply Complex.ofReal_ne_zero.mpr
    apply Real.sqrt_ne_zero'.2
    exact_mod_cast Nat.choose_pos (by omega : k.val ≤ 4)

private theorem diagMonomial_mem_range (n : Fin 9) :
    diagMonomial n ∈ LinearMap.range pairDiagonal := by
  let j := chosenJ n
  let k := chosenK n
  have hidx : diagIndex j k = n := chosen_sum n
  have hout : pairDiagonal (EuclideanSpace.single (j, k) (1 : ℂ)) =
      pairWeight j k • diagMonomial n := by
    rw [pairDiagonal_expansion]
    rw [Finset.sum_eq_single j]
    · rw [Finset.sum_eq_single k]
      · rw [hidx]
        simp [j, k, diagMonomial, diagExp, pairWeight, MvPolynomial.smul_monomial]
      · intro b hb hbk
        simp [hbk]
      · simp
    · intro b hb hbneq
      simp [hbneq]
    · simp
  have hw := pairWeight_ne_zero j k
  have hmem : pairDiagonal (EuclideanSpace.single (j, k) (1 : ℂ)) ∈
      LinearMap.range pairDiagonal := ⟨_, rfl⟩
  have hsmul : (pairWeight j k)⁻¹ •
      pairDiagonal (EuclideanSpace.single (j, k) (1 : ℂ)) ∈
      LinearMap.range pairDiagonal := Submodule.smul_mem _ _ hmem
  rw [hout] at hsmul
  simpa [hw] using hsmul

private theorem diagSpace_le_pairDiagonal_range :
    diagSpace ≤ LinearMap.range pairDiagonal := by
  apply Submodule.span_le.2
  rintro p ⟨n, rfl⟩
  exact diagMonomial_mem_range n

private theorem pairDiagonal_range_finrank :
    Module.finrank ℂ (LinearMap.range pairDiagonal) = 9 := by
  have heq : LinearMap.range pairDiagonal = diagSpace :=
    le_antisymm pairDiagonal_range_le_diagSpace diagSpace_le_pairDiagonal_range
  rw [heq]
  exact diagSpace_finrank

theorem main : AKLT.Blueprint.Q.PairDiagonalRankStatement := by
  change Module.finrank ℂ (LinearMap.ker pairDiagonal) = 16
  have hdim := LinearMap.finrank_range_add_finrank_ker pairDiagonal
  rw [pairDiagonal_range_finrank] at hdim
  have htotal : Module.finrank ℂ PairHilbert = 25 := by
    simp [PairHilbert]
  rw [htotal] at hdim
  omega

end AKLT.W.Q028
