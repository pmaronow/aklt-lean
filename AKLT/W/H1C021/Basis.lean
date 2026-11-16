import AKLT.W.H1C021.Basic
import AKLT.W.H1C021.Radix
import AKLT.W.H1M032.Main

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

namespace AKLT.W.H1C021

set_option maxHeartbeats 800000

abbrev GroupSlot (π : PatternData) (r : Representation) (x : reductionGroups π) :=
  Fin (if groupIsPair π r x.val then 2 else 1)

def groupSlotZero (π : PatternData) (r : Representation) (x : reductionGroups π) :
    GroupSlot π r x := ⟨0, by cases h : groupIsPair π r x.val <;> simp⟩

def groupSlotToken (π : PatternData) (r : Representation) (x : reductionGroups π)
    (k : GroupSlot π r x) : reductionVectors π r :=
  if k.val = 0 then leaderToken π r x else AKLT.W.H1M032.secondOrLeader π r x

theorem groupSlotToken_mem (π : PatternData) (r : Representation) (x : reductionGroups π)
    (k : GroupSlot π r x) : groupSlotToken π r x k ∈ AKLT.W.H1M032.groupSlots π r x := by
  unfold groupSlotToken
  split
  · exact AKLT.W.H1M032.leader_mem_groupSlots π r x
  · exact AKLT.W.H1M032.second_mem_groupSlots π r x

theorem groupSlotToken_injective (π : PatternData) (r : Representation) :
    Function.Injective (fun xk : Σ x, GroupSlot π r x => groupSlotToken π r xk.1 xk.2) := by
  classical
  intro a b hab
  change groupSlotToken π r a.1 a.2 = groupSlotToken π r b.1 b.2 at hab
  have hx : a.1 = b.1 := by
    by_contra hn
    have hd := AKLT.W.H1M032.groupSlots_disjoint π r
      (Finset.mem_univ a.1) (Finset.mem_univ b.1) hn
    apply Finset.disjoint_left.mp hd (groupSlotToken_mem π r a.1 a.2)
    rw [hab]
    exact groupSlotToken_mem π r b.1 b.2
  rcases a with ⟨x,i⟩
  rcases b with ⟨y,j⟩
  dsimp only at hx
  subst y
  congr 1
  apply Fin.ext
  by_cases hp : groupIsPair π r x.val = true
  · have hi : i.val < 2 := by simpa only [GroupSlot, hp, ↓reduceIte] using i.isLt
    have hj : j.val < 2 := by simpa only [GroupSlot, hp, ↓reduceIte] using j.isLt
    have hn := AKLT.W.H1M032.pair_tokens_ne π r x hp
    unfold groupSlotToken at hab
    dsimp only at hab
    by_cases hi0 : i.val = 0
    · by_cases hj0 : j.val = 0
      · omega
      · exact (hn (by simpa only [hi0, hj0, ↓reduceIte] using hab)).elim
    · by_cases hj0 : j.val = 0
      · exact (hn (by simpa only [hi0, hj0, ↓reduceIte] using hab.symm)).elim
      · omega
  · have hi : i.val < 1 := by simpa only [GroupSlot, hp, Bool.false_eq_true, ↓reduceIte] using i.isLt
    have hj : j.val < 1 := by simpa only [GroupSlot, hp, Bool.false_eq_true, ↓reduceIte] using j.isLt
    omega

theorem groupSlotToken_surjective (π : PatternData) (r : Representation) :
    Function.Surjective (fun xk : Σ x, GroupSlot π r x => groupSlotToken π r xk.1 xk.2) := by
  classical
  intro j
  have hj : j ∈ (Finset.univ.biUnion (AKLT.W.H1M032.groupSlots π r)) := by
    rw [AKLT.W.H1M032.groupSlots_cover]
    exact Finset.mem_univ j
  obtain ⟨x,hx,hj⟩ := Finset.mem_biUnion.mp hj
  by_cases hp : groupIsPair π r x.val = true
  · simp only [AKLT.W.H1M032.groupSlots, hp, ↓reduceIte,
      Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with hj | hj
    · refine ⟨⟨x,groupSlotZero π r x⟩, ?_⟩
      simpa only [groupSlotToken, groupSlotZero, ↓reduceIte] using hj.symm
    · refine ⟨⟨x,⟨1,by simp [hp]⟩⟩, ?_⟩
      simpa only [groupSlotToken, Nat.one_ne_zero, ↓reduceIte] using hj.symm
  · simp only [AKLT.W.H1M032.groupSlots, hp, Bool.false_eq_true, ↓reduceIte,
      Finset.mem_singleton] at hj
    refine ⟨⟨x,groupSlotZero π r x⟩, ?_⟩
    simpa only [groupSlotToken, groupSlotZero, ↓reduceIte] using hj.symm

def groupSlotEquiv (π : PatternData) (r : Representation) :
    (Σ x, GroupSlot π r x) ≃ reductionVectors π r :=
  Equiv.ofBijective (fun xk => groupSlotToken π r xk.1 xk.2)
    ⟨groupSlotToken_injective π r, groupSlotToken_surjective π r⟩

theorem groupSlotEquiv_apply (π : PatternData) (r : Representation)
    (x : reductionGroups π) (k : GroupSlot π r x) :
    groupSlotEquiv π r ⟨x,k⟩ = groupSlotToken π r x k := rfl

def groupConfigEquiv (π : PatternData) (r : Representation) (A : Type*) :
    (reductionVectors π r → A) ≃ ((x : reductionGroups π) → GroupSlot π r x → A) :=
  (Equiv.piCongrLeft (fun _ => A) (groupSlotEquiv π r)).symm |>.trans
    (Equiv.piCurry (fun _ _ => A))

theorem groupConfigEquiv_apply (π : PatternData) (r : Representation) (A : Type*)
    (σ : reductionVectors π r → A) (x : reductionGroups π) (k : GroupSlot π r x) :
    groupConfigEquiv π r A σ x k = σ (groupSlotToken π r x k) := by
  simp only [groupConfigEquiv, Equiv.trans_apply, Equiv.piCurry_apply,
    Sigma.curry, Equiv.piCongrLeft_symm_apply, groupSlotEquiv_apply]

theorem sum_sum_prod {G : Type*} [Fintype G] [DecidableEq G]
    {S : G → Type*} [∀ x, Fintype (S x)]
    (f : (x : G) → S x → S x → ℂ) :
    (∑ σ : (x : G) → S x, ∑ τ : (x : G) → S x, ∏ x, f x (σ x) (τ x)) =
      ∏ x, ∑ s : S x, ∑ t : S x, f x s t := by
  calc
    _ = ∑ σ : (x : G) → S x, ∏ x, ∑ t : S x, f x (σ x) t := by
      apply Finset.sum_congr rfl
      intro σ _
      exact (Fintype.prod_sum (fun x t => f x (σ x) t)).symm
    _ = _ := (Fintype.prod_sum (fun x s => ∑ t : S x, f x s t)).symm

theorem tensor_basis_congruence {G J : Type*} [Fintype G] [Fintype J]
    [DecidableEq G] [DecidableEq J]
    {S : G → Type*} [∀ x, Fintype (S x)] [∀ x, DecidableEq (S x)]
    (e : (Σ x, S x) ≃ J)
    (A B : (x : G) → (S x → Fin 2) → ℂ)
    (P : (x : G) → S x → Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ σ : J → Fin 2, ∑ τ : J → Fin 2,
      (∏ x, A x (fun k => σ (e ⟨x,k⟩))) *
        (∏ j : J, P (e.symm j).1 (e.symm j).2 (σ j) (τ j)) *
        (∏ x, B x (fun k => τ (e ⟨x,k⟩)))) =
      ∏ x, ∑ s : S x → Fin 2, ∑ t : S x → Fin 2,
        A x s * (∏ k, P x k (s k) (t k)) * B x t := by
  classical
  let c : (J → Fin 2) ≃ ((x : G) → S x → Fin 2) :=
    (Equiv.piCongrLeft (fun _ => Fin 2) e).symm |>.trans
      (Equiv.piCurry (fun _ _ => Fin 2))
  have hc (σ : J → Fin 2) (x : G) (k : S x) : c σ x k = σ (e ⟨x,k⟩) := by
    simp only [c, Equiv.trans_apply, Equiv.piCurry_apply, Sigma.curry,
      Equiv.piCongrLeft_symm_apply]
  calc
    _ = ∑ σ : J → Fin 2, ∑ τ : J → Fin 2, ∏ x,
        A x (c σ x) * (∏ k, P x k (c σ x k) (c τ x k)) * B x (c τ x) := by
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro τ _
      simp only [Finset.prod_mul_distrib, hc]
      congr 2
      calc
        _ = ∏ z : Σ x, S x, P z.1 z.2 (σ (e z)) (τ (e z)) :=
          (Fintype.prod_equiv e
            (fun z : Σ x, S x => P z.1 z.2 (σ (e z)) (τ (e z)))
            (fun j : J => P (e.symm j).1 (e.symm j).2 (σ j) (τ j))
            (fun z => congrArg
              (fun w : Σ x, S x => P w.1 w.2 (σ (e z)) (τ (e z)))
              (e.symm_apply_apply z).symm)).symm
        _ = _ := Fintype.prod_sigma (fun z : Σ x, S x =>
          P z.1 z.2 (σ (e z)) (τ (e z)))
    _ = ∑ s : (x : G) → S x → Fin 2, ∑ t : (x : G) → S x → Fin 2, ∏ x,
        A x (s x) * (∏ k, P x k (s x k) (t x k)) * B x (t x) := by
      apply Fintype.sum_equiv c
      intro σ
      apply Fintype.sum_equiv c
      intro τ
      rfl
    _ = _ := sum_sum_prod (G := G) (S := fun x => S x → Fin 2)
      (fun x s t => A x s * (∏ k, P x k (s k) (t k)) * B x t)

def groupSlotLast (π : PatternData) (r : Representation) (x : reductionGroups π) :
    GroupSlot π r x :=
  if h : groupIsPair π r x.val = true then ⟨1,by simp [h]⟩ else groupSlotZero π r x

theorem groupSlotToken_zero (π : PatternData) (r : Representation) (x : reductionGroups π) :
    groupSlotToken π r x (groupSlotZero π r x) = leaderToken π r x := by
  simp only [groupSlotToken, groupSlotZero, ↓reduceIte]

theorem groupSlotToken_last (π : PatternData) (r : Representation) (x : reductionGroups π) :
    groupSlotToken π r x (groupSlotLast π r x) = AKLT.W.H1M032.secondOrLeader π r x := by
  unfold groupSlotLast
  split
  · simp only [groupSlotToken, Nat.one_ne_zero, ↓reduceIte]
  · rename_i h
    rw [groupSlotToken_zero]
    simp only [AKLT.W.H1M032.secondOrLeader, h, Bool.false_eq_true, ↓reduceDIte]

def groupBasisCoeff (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (b : ExchangeBasis π r ε) (x : reductionGroups π) (σ : GroupSlot π r x → Fin 2) : ℤ :=
  AKLT.W.H1M032.localVector (groupIsPair π r x.val) (π.statusAt x.val = .D ∧ ε x = false)
    (b x).val (σ (groupSlotZero π r x)) (σ (groupSlotLast π r x))

theorem exchangeBasisVector_group_product (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (b : ExchangeBasis π r ε) (σ : reductionVectors π r → Fin 2) :
    (exchangeBasisVector π r ε b σ : ℂ) =
      ∏ x, (groupBasisCoeff π r ε b x (fun k => σ (groupSlotToken π r x k)) : ℂ) := by
  classical
  unfold exchangeBasisVector
  rw [Int.cast_prod]
  apply Finset.prod_congr rfl
  intro x _
  simp only [groupBasisCoeff, groupSlotToken_zero, groupSlotToken_last,
    AKLT.W.H1M032.localVector]
  by_cases hp : groupIsPair π r x.val = true
  · simp only [hp, ↓reduceDIte, ↓reduceIte, AKLT.W.H1M032.secondOrLeader,
      leaderToken, secondToken]
  · simp only [hp, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte, leaderToken]
    rfl

/-- The actual Defs exchange basis factors as integer local congruences.
This is valid for arbitrary one-token matrices, including complex entries. -/
theorem sectorTensor_congruence (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (a b : ExchangeBasis π r ε)
    (P : reductionVectors π r → Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ σ : reductionVectors π r → Fin 2, ∑ τ : reductionVectors π r → Fin 2,
      (exchangeBasisVector π r ε a σ : ℂ) * (∏ j, P j (σ j) (τ j)) *
        (exchangeBasisVector π r ε b τ : ℂ)) =
      ∏ x : reductionGroups π, ∑ s : GroupSlot π r x → Fin 2,
        ∑ t : GroupSlot π r x → Fin 2,
          (groupBasisCoeff π r ε a x s : ℂ) *
            (∏ k, P (groupSlotToken π r x k) (s k) (t k)) *
              (groupBasisCoeff π r ε b x t : ℂ) := by
  classical
  simp only [exchangeBasisVector_group_product]
  have h := tensor_basis_congruence (groupSlotEquiv π r)
    (fun x s => (groupBasisCoeff π r ε a x s : ℂ))
    (fun x t => (groupBasisCoeff π r ε b x t : ℂ))
    (fun x k => P (groupSlotToken π r x k))
  simp only [groupSlotEquiv_apply] at h
  have htoken (j : reductionVectors π r) :
      groupSlotToken π r ((groupSlotEquiv π r).symm j).1
        ((groupSlotEquiv π r).symm j).2 = j := by
    rw [← groupSlotEquiv_apply]
    exact (groupSlotEquiv π r).apply_symm_apply j
  simp only [htoken] at h
  exact h

end AKLT.W.H1C021
