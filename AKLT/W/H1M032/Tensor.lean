module
public import AKLT.Blueprint.H1.NodesSector

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M032

theorem token_apply (J : Finset (Fin 20)) (j : J)
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (v : EuclideanSpace ℂ (J → Fin 2)) (σ : J → Fin 2) :
    Matrix.toEuclideanLin (tokenMatrix J j A) v σ =
      ∑ k : Fin 2, A (σ j) k * v (Function.update σ j k) := by
  classical
  change (∑ τ : J → Fin 2,
    (if ∀ y, y ≠ j → σ y = τ y then A (σ j) (τ j) else 0) * v τ) = _
  symm
  apply Fintype.sum_of_injective (Function.update σ j) (Function.update_injective σ j)
  · intro τ hτ
    have hoff : ¬ ∀ y, y ≠ j → σ y = τ y := by
      intro h
      apply hτ
      refine ⟨τ j, ?_⟩
      funext y
      by_cases hy : y = j
      · subst y
        simp
      · simp [Function.update_of_ne hy, h y hy]
    rw [ite_eq_right hoff, zero_mul]
  · intro k
    have hoff : ∀ y, y ≠ j → σ y = Function.update σ j k y := by
      intro y hy
      simp [Function.update_of_ne hy]
    rw [ite_eq_left hoff, Function.update_self]

section Products

variable {G : Type} [Fintype G] [DecidableEq G] {B : G → Type}
variable {J : Finset (Fin 20)}

def tensorGenerator (v : ∀ x, B x → (J → Fin 2) → ℂ) (b : ∀ x, B x) :
    EuclideanSpace ℂ (J → Fin 2) :=
  WithLp.toLp 2 (fun σ => ∏ x, v x (b x) σ)

theorem tensorGenerator_update (v : ∀ x, B x → (J → Fin 2) → ℂ)
    (b : ∀ x, B x) (x : G) (c : B x) (σ : J → Fin 2) :
    tensorGenerator v (Function.update b x c) σ =
      (∏ y ∈ Finset.univ.erase x, v y (b y) σ) * v x c σ := by
  classical
  change (∏ y, v y (Function.update b x c y) σ) = _
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ x)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro y hy
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hy)]

theorem tensorGenerator_config (v : ∀ x, B x → (J → Fin 2) → ℂ)
    (b : ∀ x, B x) (x : G) (j : J) (a : Fin 2) (σ : J → Fin 2)
    (hlocal : ∀ y, y ≠ x → v y (b y) (Function.update σ j a) = v y (b y) σ) :
    tensorGenerator v b (Function.update σ j a) =
      (∏ y ∈ Finset.univ.erase x, v y (b y) σ) * v x (b x) (Function.update σ j a) := by
  classical
  change (∏ y, v y (b y) (Function.update σ j a)) = _
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ x)]
  congr 1
  apply Finset.prod_congr rfl
  intro y hy
  exact hlocal y (Finset.ne_of_mem_erase hy)

variable [∀ x, Fintype (B x)]

theorem product_group_action (slots : G → Finset J)
    (v : ∀ x, B x → (J → Fin 2) → ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (b : ∀ x, B x) (x : G)
    (C : B x → ℂ)
    (hlocal : ∀ j ∈ slots x, ∀ y, y ≠ x → ∀ a σ,
      v y (b y) (Function.update σ j a) = v y (b y) σ)
    (haction : ∀ σ,
      (∑ j ∈ slots x, ∑ a : Fin 2, A (σ j) a * v x (b x) (Function.update σ j a)) =
        ∑ c : B x, C c * v x c σ) :
    (∑ j ∈ slots x, Matrix.toEuclideanLin (tokenMatrix J j A)) (tensorGenerator v b) =
      ∑ c : B x, C c • tensorGenerator v (Function.update b x c) := by
  classical
  ext σ
  simp only [LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, token_apply]
  let P : ℂ := ∏ y ∈ Finset.univ.erase x, v y (b y) σ
  calc
    (∑ j ∈ slots x, ∑ a : Fin 2,
      A (σ j) a * tensorGenerator v b (Function.update σ j a)) =
        P * (∑ j ∈ slots x, ∑ a : Fin 2,
          A (σ j) a * v x (b x) (Function.update σ j a)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro a _
      rw [tensorGenerator_config v b x j a σ (fun y hy => hlocal j hj y hy a σ)]
      change A (σ j) a * (P * _) = _
      ring
    _ = P * ∑ c : B x, C c * v x c σ := by rw [haction]
    _ = ∑ c : B x, C c * tensorGenerator v (Function.update b x c) σ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [tensorGenerator_update]
      change P * (C c * _) = C c * (P * _)
      ring

theorem sum_token_stable (slots : G → Finset J)
    (hcover : Finset.univ.biUnion slots = Finset.univ)
    (hdisjoint : Set.PairwiseDisjoint (↑(Finset.univ : Finset G)) slots)
    (v : ∀ x, B x → (J → Fin 2) → ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (C : ∀ x, B x → B x → ℂ)
    (hlocal : ∀ x, ∀ j ∈ slots x, ∀ y, y ≠ x → ∀ c a σ,
      v y c (Function.update σ j a) = v y c σ)
    (haction : ∀ x b σ,
      (∑ j ∈ slots x, ∑ a : Fin 2, A (σ j) a * v x b (Function.update σ j a)) =
        ∑ c : B x, C x c b * v x c σ) :
    ∀ ψ ∈ Submodule.span ℂ (Set.range (tensorGenerator v)),
      Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j A) ψ ∈
        Submodule.span ℂ (Set.range (tensorGenerator v)) := by
  classical
  let S := Submodule.span ℂ (Set.range (tensorGenerator v))
  let T := Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j A)
  have hg : ∀ b, T (tensorGenerator v b) ∈ S := by
    intro b
    have heq : T (tensorGenerator v b) =
        ∑ x : G, ∑ c : B x, C x c (b x) •
          tensorGenerator v (Function.update b x c) := by
      have hs : (∑ j : J, tokenMatrix J j A) =
          ∑ x : G, ∑ j ∈ slots x, tokenMatrix J j A := by
        rw [← hcover, Finset.sum_biUnion hdisjoint]
      change (Matrix.toEuclideanLin (∑ j : J, tokenMatrix J j A)) (tensorGenerator v b) = _
      rw [hs, map_sum, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro x _
      rw [map_sum]
      exact product_group_action slots v A b x (fun c => C x c (b x))
        (fun j hj y hy a σ => hlocal x j hj y hy (b y) a σ)
        (haction x (b x))
    rw [heq]
    apply Submodule.sum_mem
    intro x _
    apply Submodule.sum_mem
    intro c _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨Function.update b x c, rfl⟩
  intro ψ hψ
  apply Submodule.span_induction (R := ℂ) (M := EuclideanSpace ℂ (J → Fin 2))
    (s := Set.range (tensorGenerator v)) (p := fun z _ => T z ∈ S)
  · rintro z ⟨b, rfl⟩
    exact hg b
  · simpa only [map_zero] using S.zero_mem
  · intro z w hz hw ihz ihw
    simpa only [map_add] using S.add_mem ihz ihw
  · intro a z hz ihz
    simpa only [map_smul] using S.smul_mem a ihz
  · exact hψ

end Products
end AKLT.W.H1M032
