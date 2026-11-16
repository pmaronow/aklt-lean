import AKLT.W.H1C006.Coordinates

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1C006

attribute [local instance] Classical.propDecidable

theorem not_localCanonical (pair : Bool) (exterior : Prop) [Decidable exterior]
    (i j : Fin 2) (h : ¬ LocalCanonical pair exterior i j) :
    pair = true ∧ ((i = 1 ∧ j = 0) ∨ (exterior ∧ i = j)) := by
  cases pair <;> by_cases he : exterior <;> fin_cases i <;> fin_cases j
  all_goals simp_all [LocalCanonical]

theorem swapConfiguration_eq_of_equal {J : Finset (Fin 20)} (a b : J)
    (σ : J → Fin 2) (h : σ a = σ b) : swapConfiguration a b σ = σ := by
  classical
  funext j
  by_cases ha : j = a
  · subst j
    simpa only [swapConfiguration, Equiv.swap_apply_left] using h.symm
  · by_cases hb : j = b
    · subst j
      simpa only [swapConfiguration, Equiv.swap_apply_right] using h
    · simp only [swapConfiguration, Equiv.swap_apply_of_ne_of_ne ha hb]

theorem canonical_swap_other (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (σ : reductionVectors π r → Fin 2) (x y : reductionGroups π) (hyx : y ≠ x) :
    CanonicalAt π r ε
        (swapConfiguration (leaderToken π r x) (H1M032.secondOrLeader π r x) σ) y ↔
      CanonicalAt π r ε σ y := by
  have h₁ := H1M032.other_group_tokens_ne π r x y hyx
    (leaderToken π r x) (H1M032.leader_mem_groupSlots π r x)
  have h₂ := H1M032.other_group_tokens_ne π r x y hyx
    (H1M032.secondOrLeader π r x) (H1M032.second_mem_groupSlots π r x)
  simp only [CanonicalAt, swapConfiguration,
    Equiv.swap_apply_of_ne_of_ne h₁.1 h₂.1,
    Equiv.swap_apply_of_ne_of_ne h₁.2 h₂.2]

theorem canonical_swap_self (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (σ : reductionVectors π r → Fin 2) (x : reductionGroups π)
    (hp : groupIsPair π r x.val = true)
    (hi : σ (leaderToken π r x) = 1) (hj : σ (H1M032.secondOrLeader π r x) = 0) :
    CanonicalAt π r ε
      (swapConfiguration (leaderToken π r x) (H1M032.secondOrLeader π r x) σ) x := by
  simp only [CanonicalAt, LocalCanonical, hp, ↓reduceIte, swapConfiguration,
    Equiv.swap_apply_left, Equiv.swap_apply_right, hi, hj]
  split <;> simp

theorem exchangeEigenvectors_coord (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (ψ : TensorSpace (reductionVectors π r))
    (hψ : ExchangeEigenvectors π r ε ψ) (x : reductionGroups π)
    (hp : groupIsPair π r x.val = true) (σ : reductionVectors π r → Fin 2) :
    ψ (swapConfiguration (leaderToken π r x) (H1M032.secondOrLeader π r x) σ) =
      exchangeSign π ε x * ψ σ := by
  have h := congrArg (fun v : TensorSpace (reductionVectors π r) => v σ) (hψ x hp)
  simpa only [groupExchange, exchange_apply, WithLp.ofLp_smul, Pi.smul_apply,
    smul_eq_mul] using h

theorem exchangeSign_ne_zero (π : PatternData) (ε : ExchangeSigns π)
    (x : reductionGroups π) : exchangeSign π ε x ≠ 0 := by
  unfold exchangeSign
  split <;> norm_num

/-- Exchange identities determine all coordinates from the canonical ones.
On exterior pairs, equal spins force the coefficient to be zero. -/
theorem eq_zero_of_canonical_zero (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (ψ : TensorSpace (reductionVectors π r))
    (hψ : ExchangeEigenvectors π r ε ψ)
    (hzero : ∀ σ, (∀ x, CanonicalAt π r ε σ x) → ψ σ = 0) : ψ = 0 := by
  classical
  have hInd (s : Finset (reductionGroups π)) :
      ∀ σ, (∀ x, x ∉ s → CanonicalAt π r ε σ x) → ψ σ = 0 := by
    induction s using Finset.induction_on with
    | empty =>
      intro σ hσ
      exact hzero σ (fun x => hσ x (by simp))
    | @insert x s hx ih =>
      intro σ hσ
      by_cases hcan : CanonicalAt π r ε σ x
      · apply ih σ
        intro y hy
        by_cases hyx : y = x
        · simpa only [hyx] using hcan
        · exact hσ y (by simpa only [Finset.mem_insert, not_or] using And.intro hyx hy)
      · obtain ⟨hp, hcases⟩ := not_localCanonical (groupIsPair π r x.val)
          (π.statusAt x.val = .D ∧ ε x = false) (σ (leaderToken π r x))
          (σ (H1M032.secondOrLeader π r x)) hcan
        rcases hcases with ⟨hi, hj⟩ | ⟨he, hij⟩
        · have hswap : ψ (swapConfiguration (leaderToken π r x)
              (H1M032.secondOrLeader π r x) σ) = 0 := by
            apply ih
            intro y hy
            by_cases hyx : y = x
            · subst y
              exact canonical_swap_self π r ε σ x hp hi hj
            · apply (canonical_swap_other π r ε σ x y hyx).mpr
              exact hσ y (by simpa only [Finset.mem_insert, not_or] using And.intro hyx hy)
          have heq := exchangeEigenvectors_coord π r ε ψ hψ x hp σ
          rw [hswap] at heq
          exact (mul_eq_zero.mp heq.symm).resolve_left (exchangeSign_ne_zero π ε x)
        · have hswap := swapConfiguration_eq_of_equal (leaderToken π r x)
            (H1M032.secondOrLeader π r x) σ hij
          have heq := exchangeEigenvectors_coord π r ε ψ hψ x hp σ
          rw [hswap] at heq
          have hsign : exchangeSign π ε x = -1 := ite_eq_left he
          rw [hsign] at heq
          linear_combination (1 / 2 : ℂ) * heq
  ext σ
  exact hInd Finset.univ σ (fun x hx => (hx (Finset.mem_univ x)).elim)

/-- The explicitly defined sector tensors span the full joint exchange
eigenspace, including the symmetric support required at U pairs. -/
theorem exchange_complete (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (ψ : TensorSpace (reductionVectors π r)) (hψ : ExchangeEigenvectors π r ε ψ) :
    ψ ∈ exchangeSpace π r ε := by
  classical
  let φ : TensorSpace (reductionVectors π r) :=
    ∑ b : ExchangeBasis π r ε,
      ψ (basisConfiguration π r ε b) • sectorVector π r ε b
  have hφ : φ ∈ exchangeSpace π r ε := by
    apply Submodule.sum_mem
    intro b _
    exact (exchangeSpace π r ε).smul_mem _ (Submodule.subset_span ⟨b, rfl⟩)
  have hφe := exchangeSpace_eigenvectors π r ε φ hφ
  have hδ : ExchangeEigenvectors π r ε (ψ - φ) := by
    intro x hp
    rw [map_sub, hψ x hp, hφe x hp, smul_sub]
  have hδzero : ∀ σ, (∀ x, CanonicalAt π r ε σ x) → (ψ - φ) σ = 0 := by
    intro σ hσ
    obtain ⟨b, hb⟩ := canonical_configuration π r ε σ hσ
    have hφb : φ (basisConfiguration π r ε b) = ψ (basisConfiguration π r ε b) := by
      simp only [φ, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
        Pi.smul_apply, smul_eq_mul]
      simp_rw [sectorVector_basisConfiguration]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← hb]
    change ψ (basisConfiguration π r ε b) - φ (basisConfiguration π r ε b) = 0
    exact sub_eq_zero.mpr hφb.symm
  have hEq := eq_zero_of_canonical_zero π r ε (ψ - φ) hδ hδzero
  rwa [sub_eq_zero.mp hEq]

end AKLT.W.H1C006
