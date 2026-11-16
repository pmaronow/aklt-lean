import AKLT.W.H1C006.Central

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1C006

def swapConfiguration {J : Finset (Fin 20)} (j k : J) (σ : J → Fin 2) : J → Fin 2 :=
  fun l => σ (Equiv.swap j k l)

theorem swapConfiguration_involutive {J : Finset (Fin 20)} (j k : J) :
    Function.Involutive (swapConfiguration j k) := by
  intro σ
  funext l
  simp only [swapConfiguration, Equiv.swap_apply_self]

theorem exchange_apply (J : Finset (Fin 20)) (j k : J)
    (ψ : TensorSpace J) (σ : J → Fin 2) :
    exchangeOperator J j k ψ σ = ψ (swapConfiguration j k σ) := by
  classical
  have hi (τ : J → Fin 2) : σ = swapConfiguration j k τ ↔ τ = swapConfiguration j k σ := by
    constructor
    · intro h
      rw [h, swapConfiguration_involutive]
    · intro h
      rw [h, swapConfiguration_involutive]
  simp only [exchangeOperator, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct]
  change (∑ τ, (if σ = swapConfiguration j k τ then (1 : ℂ) else 0) * ψ τ) = _
  simp only [hi, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem exchange_involutive (J : Finset (Fin 20)) (j k : J) :
    exchangeOperator J j k * exchangeOperator J j k = 1 := by
  ext ψ σ
  change exchangeOperator J j k (exchangeOperator J j k ψ) σ = ψ σ
  rw [exchange_apply, exchange_apply, swapConfiguration_involutive]

theorem exchange_symmetric (J : Finset (Fin 20)) (j k : J) :
    (exchangeOperator J j k).IsSymmetric := by
  classical
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  ext σ τ
  have hi : σ = swapConfiguration j k τ ↔ τ = swapConfiguration j k σ := by
    constructor <;> intro h
    · rw [h, swapConfiguration_involutive]
    · rw [h, swapConfiguration_involutive]
  change star (if τ = swapConfiguration j k σ then (1 : ℂ) else 0) =
    if σ = swapConfiguration j k τ then 1 else 0
  by_cases hs : σ = swapConfiguration j k τ
  · have ht := hi.mp hs
    rw [ite_eq_left ht, ite_eq_left hs, star_one]
  · have ht : ¬ τ = swapConfiguration j k σ := fun h => hs (hi.mpr h)
    rw [ite_eq_right ht, ite_eq_right hs, star_zero]

theorem exchange_commute_of_disjoint (J : Finset (Fin 20)) (a b c d : J)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Commute (exchangeOperator J a b) (exchangeOperator J c d) := by
  have hperm (l : J) : Equiv.swap c d (Equiv.swap a b l) =
      Equiv.swap a b (Equiv.swap c d l) := by
    by_cases ha : l = a
    · subst l
      simp only [Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hbc hbd,
        Equiv.swap_apply_of_ne_of_ne hac had]
    · by_cases hb : l = b
      · subst l
        simp only [Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne hac had,
          Equiv.swap_apply_of_ne_of_ne hbc hbd]
      · by_cases hc : l = c
        · subst l
          simp only [Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm,
            Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]
        · by_cases hd : l = d
          · subst l
            simp only [Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm,
              Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
          · simp only [Equiv.swap_apply_of_ne_of_ne ha hb,
              Equiv.swap_apply_of_ne_of_ne hc hd]
  apply LinearMap.ext
  intro ψ
  ext σ
  change exchangeOperator J a b (exchangeOperator J c d ψ) σ =
    exchangeOperator J c d (exchangeOperator J a b ψ) σ
  rw [exchange_apply, exchange_apply, exchange_apply, exchange_apply]
  apply congrArg ψ
  funext l
  exact congrArg σ (hperm l).symm

/-- A totalized group exchange; on a single group it is the identity. -/
def groupExchange (π : PatternData) (r : Representation) (x : reductionGroups π) :
    Module.End ℂ (TensorSpace (reductionVectors π r)) :=
  exchangeOperator (reductionVectors π r) (leaderToken π r x)
    (H1M032.secondOrLeader π r x)

theorem groupExchange_pair (π : PatternData) (r : Representation)
    (x : reductionGroups π) (h : groupIsPair π r x.val = true) :
    groupExchange π r x = exchangeOperator (reductionVectors π r)
      (leaderToken π r x) (secondToken π r x h) := by
  have ht : H1M032.secondOrLeader π r x = secondToken π r x h := by
    simp only [H1M032.secondOrLeader, h, ↓reduceDIte]
  exact congrArg (exchangeOperator (reductionVectors π r) (leaderToken π r x)) ht

theorem groupExchange_involutive (π : PatternData) (r : Representation)
    (x : reductionGroups π) : groupExchange π r x * groupExchange π r x = 1 :=
  exchange_involutive _ _ _

theorem groupExchange_commute (π : PatternData) (r : Representation)
    (x y : reductionGroups π) : Commute (groupExchange π r x) (groupExchange π r y) := by
  classical
  by_cases hxy : x = y
  · subst y
    exact Commute.refl _
  · have h₁ := H1M032.other_group_tokens_ne π r x y (Ne.symm hxy)
      (leaderToken π r x) (H1M032.leader_mem_groupSlots π r x)
    have h₂ := H1M032.other_group_tokens_ne π r x y (Ne.symm hxy)
      (H1M032.secondOrLeader π r x) (H1M032.second_mem_groupSlots π r x)
    exact exchange_commute_of_disjoint _ _ _ _ _
      (Ne.symm h₁.1) (Ne.symm h₁.2) (Ne.symm h₂.1) (Ne.symm h₂.2)

def exchangeSign (π : PatternData) (ε : ExchangeSigns π) (x : reductionGroups π) : ℂ :=
  if π.statusAt x.val = .D ∧ ε x = false then -1 else 1

def ExchangeEigenvectors (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (ψ : TensorSpace (reductionVectors π r)) : Prop :=
  ∀ x : reductionGroups π, groupIsPair π r x.val = true →
    groupExchange π r x ψ = exchangeSign π ε x • ψ

theorem localVector_swap (exterior : Prop) [Decidable exterior] (b : ℕ) (i j : Fin 2) :
    H1M032.localVector true exterior b j i =
      (if exterior then (-1 : ℤ) else 1) * H1M032.localVector true exterior b i j := by
  by_cases he : exterior <;> fin_cases i <;> fin_cases j <;>
    simp [H1M032.localVector, he]

theorem groupVector_swap_self (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (b : ExchangeBasis π r ε) (x : reductionGroups π)
    (hp : groupIsPair π r x.val = true) (σ : reductionVectors π r → Fin 2) :
    H1M032.groupVector π r ε x (b x)
        (swapConfiguration (leaderToken π r x) (H1M032.secondOrLeader π r x) σ) =
      exchangeSign π ε x * H1M032.groupVector π r ε x (b x) σ := by
  simp only [H1M032.groupVector, hp, swapConfiguration,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  have h := localVector_swap (π.statusAt x.val = .D ∧ ε x = false) (b x).val
    (σ (leaderToken π r x)) (σ (H1M032.secondOrLeader π r x))
  change _ = (if π.statusAt x.val = .D ∧ ε x = false then (-1 : ℂ) else 1) * _
  exact_mod_cast h

theorem groupVector_swap_other (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (b : ExchangeBasis π r ε) (x y : reductionGroups π)
    (hyx : y ≠ x) (σ : reductionVectors π r → Fin 2) :
    H1M032.groupVector π r ε y (b y)
        (swapConfiguration (leaderToken π r x) (H1M032.secondOrLeader π r x) σ) =
      H1M032.groupVector π r ε y (b y) σ := by
  have h₁ := H1M032.other_group_tokens_ne π r x y hyx
    (leaderToken π r x) (H1M032.leader_mem_groupSlots π r x)
  have h₂ := H1M032.other_group_tokens_ne π r x y hyx
    (H1M032.secondOrLeader π r x) (H1M032.second_mem_groupSlots π r x)
  simp only [H1M032.groupVector, swapConfiguration,
    Equiv.swap_apply_of_ne_of_ne h₁.1 h₂.1,
    Equiv.swap_apply_of_ne_of_ne h₁.2 h₂.2]

theorem sectorVector_exchange (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (b : ExchangeBasis π r ε) (x : reductionGroups π)
    (hp : groupIsPair π r x.val = true) :
    groupExchange π r x (sectorVector π r ε b) =
      exchangeSign π ε x • sectorVector π r ε b := by
  classical
  ext σ
  rw [groupExchange, exchange_apply]
  rw [H1M032.sectorVector_eq_tensorGenerator]
  change (∏ y, H1M032.groupVector π r ε y (b y)
      (swapConfiguration (leaderToken π r x) (H1M032.secondOrLeader π r x) σ)) =
    exchangeSign π ε x * ∏ y, H1M032.groupVector π r ε y (b y) σ
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x),
    ← Finset.mul_prod_erase Finset.univ (fun y => H1M032.groupVector π r ε y (b y) σ)
      (Finset.mem_univ x), groupVector_swap_self π r ε b x hp σ]
  have hrest : (∏ y ∈ Finset.univ.erase x, H1M032.groupVector π r ε y (b y)
      (swapConfiguration (leaderToken π r x) (H1M032.secondOrLeader π r x) σ)) =
      ∏ y ∈ Finset.univ.erase x, H1M032.groupVector π r ε y (b y) σ := by
    apply Finset.prod_congr rfl
    intro y hy
    exact groupVector_swap_other π r ε b x y (Finset.mem_erase.mp hy).1 σ
  rw [hrest, mul_assoc]

theorem exchangeSpace_eigenvectors (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (ψ : TensorSpace (reductionVectors π r))
    (hψ : ψ ∈ exchangeSpace π r ε) : ExchangeEigenvectors π r ε ψ := by
  intro x hp
  have hspan : exchangeSpace π r ε ≤ (groupExchange π r x).eigenspace (exchangeSign π ε x) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    exact Module.End.mem_eigenspace_iff.mpr (sectorVector_exchange π r ε b x hp)
  exact Module.End.mem_eigenspace_iff.mp (hspan hψ)

/-- A finite commuting family of involutions has a common sign eigenvector
inside each nonzero invariant eigenspace of O. No spectral theorem is needed. -/
theorem common_sign_eigenvector {V G : Type*} [AddCommGroup V] [Module ℂ V]
    [Fintype G] (X : G → Module.End ℂ V) (O : Module.End ℂ V)
    (hXX : ∀ g, X g * X g = 1) (hComm : ∀ g h, Commute (X g) (X h))
    (hOX : ∀ g, Commute O (X g)) (μ : ℂ) (v : V) (hv : v ≠ 0)
    (hOv : O v = μ • v) :
    ∃ ε : G → Bool, ∃ w : V, w ≠ 0 ∧ O w = μ • w ∧
      ∀ g, X g w = (if ε g then (1 : ℂ) else -1) • w := by
  classical
  have hFin (s : Finset G) :
      ∃ ε : G → Bool, ∃ w : V, w ≠ 0 ∧ O w = μ • w ∧
        ∀ g ∈ s, X g w = (if ε g then (1 : ℂ) else -1) • w := by
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => true, v, hv, hOv, by simp⟩
    | @insert g s hg ih =>
      obtain ⟨ε, w, hw, hOw, hXw⟩ := ih
      have hgg : X g (X g w) = w := by
        exact congrArg (fun T : Module.End ℂ V => T w) (hXX g)
      have hOg : O (X g w) = μ • X g w := by
        calc
          O (X g w) = X g (O w) := congrArg (fun T : Module.End ℂ V => T w) (hOX g).eq
          _ = μ • X g w := by rw [hOw, map_smul]
      by_cases hp : w + X g w = 0
      · refine ⟨Function.update ε g false, w, hw, hOw, ?_⟩
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simp only [Function.update_self, Bool.false_eq_true, ↓reduceIte, neg_smul, one_smul]
          exact eq_neg_of_add_eq_zero_right hp
        · have hxg : x ≠ g := fun h => hg (h ▸ hx)
          simpa only [Function.update_of_ne hxg] using hXw x hx
      · refine ⟨Function.update ε g true, w + X g w, hp, ?_, ?_⟩
        · rw [map_add, hOw, hOg, smul_add]
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · simp only [Function.update_self, ↓reduceIte, one_smul, map_add, hgg]
            exact add_comm _ _
          · have hxg : x ≠ g := fun h => hg (h ▸ hx)
            have hcg : X x (X g w) = X g (X x w) :=
              congrArg (fun T : Module.End ℂ V => T w) (hComm x g).eq
            rw [Function.update_of_ne hxg, map_add, hcg, hXw x hx, map_smul, smul_add]
  obtain ⟨ε, w, hw, hOw, hXw⟩ := hFin Finset.univ
  exact ⟨ε, w, hw, hOw, fun g => hXw g (Finset.mem_univ g)⟩

end AKLT.W.H1C006
