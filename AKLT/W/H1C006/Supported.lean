module
public import AKLT.W.H1C006.Completeness

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1C006

def PairStructure (π : PatternData) (r : Representation)
    (O : Module.End ℂ (TensorSpace (reductionVectors π r))) : Prop :=
  ∀ x : reductionGroups π, ∀ hp : groupIsPair π r x.val = true,
    (π.statusAt x.val = .U →
      let P := (1 / 2 : ℂ) • (1 + groupExchange π r x)
      O = P * O * P) ∧
    (π.statusAt x.val = .D → Commute O (groupExchange π r x))

theorem groupStatus (π : PatternData) (x : reductionGroups π) :
    π.statusAt x.val = .U ∨ π.statusAt x.val = .D := by
  have hd := (Finset.mem_filter.mp x.property).2
  change 0 < (π.bonds.filter fun e => e.1 = x.val ∨ e.2 = x.val).card at hd
  obtain ⟨e, he⟩ := Finset.card_pos.mp hd
  obtain ⟨hb, hx⟩ := Finset.mem_filter.mp he
  have hb' := (Finset.mem_filter.mp hb).2
  have hX : π.statusAt x.val ≠ .X := by
    rcases hx with hx | hx
    · exact hx ▸ hb'.1
    · exact hx ▸ hb'.2.1
  cases hs : π.statusAt x.val with
  | U => exact Or.inl rfl
  | D => exact Or.inr rfl
  | X => exact (hX hs).elim

theorem supported_fixes {V : Type*} [AddCommGroup V] [Module ℂ V]
    (X O : Module.End ℂ V) (hX : X * X = 1)
    (hO : O = ((1 / 2 : ℂ) • (1 + X)) * O * ((1 / 2 : ℂ) • (1 + X))) :
    X * O = O ∧ O * X = O := by
  let P := (1 / 2 : ℂ) • (1 + X)
  have hXP : X * P = P := by
    dsimp only [P]
    rw [mul_smul_comm, mul_add, mul_one, hX, add_comm]
  have hPX : P * X = P := by
    dsimp only [P]
    rw [smul_mul_assoc, add_mul, one_mul, hX, add_comm]
  constructor
  · calc
      X * O = X * (P * O * P) := congrArg (X * ·) hO
      _ = P * O * P := by rw [← mul_assoc, ← mul_assoc, hXP]
      _ = O := hO.symm
  · calc
      O * X = (P * O * P) * X := congrArg (· * X) hO
      _ = P * O * P := by rw [mul_assoc, hPX]
      _ = O := hO.symm

theorem groupExchange_single (π : PatternData) (r : Representation)
    (x : reductionGroups π) (hp : groupIsPair π r x.val ≠ true) :
    groupExchange π r x = 1 := by
  have ht : H1M032.secondOrLeader π r x = leaderToken π r x := by
    exact dif_neg hp
  rw [groupExchange, ht]
  ext ψ σ
  change exchangeOperator _ _ _ ψ σ = ψ σ
  rw [exchange_apply]
  apply congrArg ψ
  funext l
  simp only [swapConfiguration, Equiv.swap_self, Equiv.refl_apply]

theorem pairStructure_commute (π : PatternData) (r : Representation)
    (O : Module.End ℂ (TensorSpace (reductionVectors π r))) (h : PairStructure π r O)
    (x : reductionGroups π) : Commute O (groupExchange π r x) := by
  by_cases hp : groupIsPair π r x.val = true
  · rcases groupStatus π x with hu | hd
    · obtain ⟨hXO, hOX⟩ := supported_fixes _ O (groupExchange_involutive π r x) ((h x hp).1 hu)
      exact hOX.trans hXO.symm
    · exact (h x hp).2 hd
  · rw [groupExchange_single π r x hp]
    exact Commute.one_right _

theorem pairStructure_preserves (π : PatternData) (r : Representation)
    (O : Module.End ℂ (TensorSpace (reductionVectors π r))) (h : PairStructure π r O)
    (ε : ExchangeSigns π) : ∀ ψ ∈ exchangeSpace π r ε, O ψ ∈ exchangeSpace π r ε := by
  intro ψ hψ
  apply exchange_complete π r ε
  intro x hp
  have he := exchangeSpace_eigenvectors π r ε ψ hψ x hp
  have hc := pairStructure_commute π r O h x
  calc
    groupExchange π r x (O ψ) = O (groupExchange π r x ψ) :=
      congrArg (fun T : Module.End ℂ (TensorSpace (reductionVectors π r)) => T ψ) hc.eq.symm
    _ = exchangeSign π ε x • O ψ := by rw [he, map_smul]

theorem nonzero_eigenvector_in_sector (π : PatternData) (r : Representation)
    (O : Module.End ℂ (TensorSpace (reductionVectors π r))) (h : PairStructure π r O)
    (μ : ℂ) (hμ : μ ≠ 0) (v : TensorSpace (reductionVectors π r))
    (hv : v ≠ 0) (hOv : O v = μ • v) :
    ∃ ε : ExchangeSigns π, ∃ w ∈ exchangeSpace π r ε, w ≠ 0 ∧ O w = μ • w := by
  obtain ⟨ε, w, hw, hOw, hXw⟩ := common_sign_eigenvector (groupExchange π r) O
    (groupExchange_involutive π r) (groupExchange_commute π r)
    (pairStructure_commute π r O h) μ v hv hOv
  refine ⟨ε, w, exchange_complete π r ε w ?_, hw, hOw⟩
  intro x hp
  rcases groupStatus π x with hu | hd
  · have hXO := (supported_fixes _ O (groupExchange_involutive π r x) ((h x hp).1 hu)).1
    have hfix : groupExchange π r x w = w := by
      apply smul_right_injective _ hμ
      have hval := congrArg
        (fun T : Module.End ℂ (TensorSpace (reductionVectors π r)) => T w) hXO
      change groupExchange π r x (O w) = O w at hval
      simpa only [hOw, map_smul] using hval
    simpa [exchangeSign, hu] using hfix
  · cases he : ε x <;> simpa [exchangeSign, hd, he] using hXw x

/-- Supported positivity permits zero eigenvalues on discarded U directions. -/
theorem posSemidef_of_supported_sectors (π : PatternData) (r : Representation)
    (M : Matrix (reductionVectors π r → Fin 2) (reductionVectors π r → Fin 2) ℂ)
    (hHerm : M.IsHermitian) (hPair : PairStructure π r (Matrix.toEuclideanLin M))
    (hPositive : ∀ ε : ExchangeSigns π,
      PositiveOn (exchangeSpace π r ε) (Matrix.toEuclideanLin M)) : M.PosSemidef := by
  classical
  apply hHerm.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  by_contra hi
  have hneg : hHerm.eigenvalues i < 0 := lt_of_not_ge hi
  let μ : ℂ := (hHerm.eigenvalues i : ℂ)
  have hμ : μ ≠ 0 := by
    intro hzero
    change (hHerm.eigenvalues i : ℂ) = 0 at hzero
    have hz : hHerm.eigenvalues i = 0 := by exact_mod_cast hzero
    linarith
  let v := hHerm.eigenvectorBasis i
  have hv : v ≠ 0 := hHerm.eigenvectorBasis.orthonormal.ne_zero i
  have hOv : Matrix.toEuclideanLin M v = μ • v := by
    apply WithLp.ofLp_injective 2
    change M.mulVec (hHerm.eigenvectorBasis i).ofLp = μ • (hHerm.eigenvectorBasis i).ofLp
    rw [hHerm.mulVec_eigenvectorBasis i]
    ext σ
    simp [μ, Complex.real_smul]
  obtain ⟨ε, w, hwS, hw, hOw⟩ :=
    nonzero_eigenvector_in_sector π r _ hPair μ hμ v hv hOv
  have hp := hPositive ε w hwS hw
  have hquad : (inner ℂ w (Matrix.toEuclideanLin M w)).re = μ.re * ‖w‖ ^ 2 := by
    rw [hOw, inner_smul_right, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
    exact RCLike.re_mul_ofReal μ (‖w‖ ^ 2)
  have hnonneg := sq_nonneg ‖w‖
  rw [hquad] at hp
  have hμre : μ.re = hHerm.eigenvalues i := Complex.ofReal_re _
  rw [hμre] at hp
  nlinarith

theorem positive_pauli_of_central (π : PatternData) (hπ : π.Covered) (r : Representation)
    (I : Finset (Fin 20)) (hI : GroupInversion π r I)
    (c : ℚ) (hc : 0 < c) (hc1 : c < 1)
    (hCentral : ∀ ε : ExchangeSigns π,
      (complexSectorMatrix π r ε (invertPolynomial I (reducedDifference π r c))).PosDef) :
    (pauliOperator (reductionVectors π r) (invertPolynomial I (reducedDifference π r c))).PosSemidef := by
  obtain ⟨hHerm, _, _, hZ, hPlus, hMinus, hPair⟩ := operatorStructure π hπ r I hI c hc hc1
  have hp : PairStructure π r (Matrix.toEuclideanLin
      (pauliOperator (reductionVectors π r) (invertPolynomial I (reducedDifference π r c)))) := by
    intro x hx
    rw [groupExchange_pair π r x hx]
    exact hPair x hx
  apply posSemidef_of_supported_sectors π r _ hHerm hp
  intro ε
  have hInv := pairStructure_preserves π r _ hp ε
  have hSym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hHerm
  have hLadder := sector π r ε _ hInv (fun ψ _ χ _ => hSym ψ χ)
    (fun ψ _ => congrArg (fun T => T ψ) hZ.eq)
    (fun ψ _ => congrArg (fun T => T ψ) hPlus.eq)
    (fun ψ _ => congrArg (fun T => T ψ) hMinus.eq)
  exact hLadder.2.2.mp (central_positive_of_matrix π r ε _ (hCentral ε))

end AKLT.W.H1C006
