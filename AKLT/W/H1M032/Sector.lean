module
public import AKLT.W.H1M032.Local
public import AKLT.W.H1M032.Geometry
public import AKLT.W.H1M032.Tensor

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M032

def groupVector (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (x : reductionGroups π) (b : GroupBasis π r ε x)
    (σ : reductionVectors π r → Fin 2) : ℂ :=
  (localVector (groupIsPair π r x.val) (π.statusAt x.val = .D ∧ ε x = false)
    b.val (σ (leaderToken π r x)) (σ (secondOrLeader π r x)) : ℂ)

def groupActionMatrix (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (x : reductionGroups π)
    (c b : GroupBasis π r ε x) : ℂ :=
  localMatrix (groupIsPair π r x.val) (π.statusAt x.val = .D ∧ ε x = false)
    A c.val b.val

theorem sectorVector_eq_tensorGenerator (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (b : ExchangeBasis π r ε) :
    sectorVector π r ε b = tensorGenerator (groupVector π r ε) b := by
  classical
  ext σ
  change (exchangeBasisVector π r ε b σ : ℂ) = ∏ x, groupVector π r ε x (b x) σ
  rw [exchangeBasisVector, Int.cast_prod]
  apply Finset.prod_congr rfl
  intro x _
  by_cases hp : groupIsPair π r x.val = true
  · simp only [groupVector, localVector, hp, ↓reduceDIte, ↓reduceIte,
      secondOrLeader, leaderToken, secondToken]
  · simp only [groupVector, localVector, hp, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte,
      leaderToken]
    rfl

theorem exchangeSpace_eq_span (π : PatternData) (r : Representation) (ε : ExchangeSigns π) :
    exchangeSpace π r ε = Submodule.span ℂ (Set.range (tensorGenerator (groupVector π r ε))) := by
  change Submodule.span ℂ (Set.range (sectorVector π r ε)) = _
  congr 2
  funext b
  exact sectorVector_eq_tensorGenerator π r ε b

theorem groupVector_local (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (x : reductionGroups π) (j : reductionVectors π r) (hj : j ∈ groupSlots π r x)
    (y : reductionGroups π) (hyx : y ≠ x) (c : GroupBasis π r ε y)
    (a : Fin 2) (σ : reductionVectors π r → Fin 2) :
    groupVector π r ε y c (Function.update σ j a) = groupVector π r ε y c σ := by
  have h := other_group_tokens_ne π r x y hyx j hj
  simp only [groupVector, Function.update_of_ne h.1, Function.update_of_ne h.2]

theorem groupVector_action (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (x : reductionGroups π)
    (b : GroupBasis π r ε x) (σ : reductionVectors π r → Fin 2) :
    (∑ j ∈ groupSlots π r x, ∑ a : Fin 2,
      A (σ j) a * groupVector π r ε x b (Function.update σ j a)) =
      ∑ c : GroupBasis π r ε x, groupActionMatrix π r ε A x c b * groupVector π r ε x c σ := by
  classical
  have h := local_action (groupIsPair π r x.val) (π.statusAt x.val = .D ∧ ε x = false)
    A b.val b.isLt (σ (leaderToken π r x)) (σ (secondOrLeader π r x))
  rw [← Fin.sum_univ_eq_sum_range] at h
  change _ = ∑ c : Fin (localDim (groupIsPair π r x.val)
    (π.statusAt x.val = .D ∧ ε x = false)),
      localMatrix (groupIsPair π r x.val) (π.statusAt x.val = .D ∧ ε x = false) A c.val b.val *
        (localVector (groupIsPair π r x.val) (π.statusAt x.val = .D ∧ ε x = false) c.val
          (σ (leaderToken π r x)) (σ (secondOrLeader π r x)) : ℂ)
  rw [← h]
  by_cases hp : groupIsPair π r x.val = true
  · have hne := pair_tokens_ne π r x hp
    simp only [groupSlots, hp, ↓reduceIte, Finset.sum_pair hne,
      groupVector, Function.update_self, Function.update_of_ne hne,
      Function.update_of_ne hne.symm]
  · simp only [groupSlots, hp, Bool.false_eq_true, ↓reduceIte, Finset.sum_singleton,
      groupVector, localVector, Function.update_self, add_zero]

/-- Every exchange sector is preserved by the sum of any identical one-spin matrix. -/
theorem exchangeSpace_matrix_stable (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ ψ ∈ exchangeSpace π r ε,
      Matrix.toEuclideanLin (∑ j : reductionVectors π r,
        tokenMatrix (reductionVectors π r) j A) ψ ∈ exchangeSpace π r ε := by
  classical
  rw [exchangeSpace_eq_span]
  exact sum_token_stable (groupSlots π r) (groupSlots_cover π r) (groupSlots_disjoint π r)
    (groupVector π r ε) A (groupActionMatrix π r ε A)
    (groupVector_local π r ε) (groupVector_action π r ε A)

end AKLT.W.H1M032
