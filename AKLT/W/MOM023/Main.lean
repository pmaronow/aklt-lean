module
public import AKLT.Blueprint.Mom.NodesMean

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.MOM023

private def pad {k : ℕ} (a : Fin k → Vec3) (j : Fin 3) : Vec3 :=
  if h : j.val < k then a ⟨j.val, h⟩ else 0

private def firstUnit : UnitVector :=
  ⟨![1, 0, 0], by norm_num [normSq, dot, Fin.sum_univ_three]⟩

private lemma localProduct_pad {k : ℕ} (hk : k ≤ 3) (a : Fin k → Vec3) (v : Vec3) :
    localProduct a v = localProduct (pad a) v := by
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk' with h | h | h | h <;> subst k <;>
    simp [localProduct, pad, dot, Fin.prod_univ_three, Fin.sum_univ_three]

private lemma firstUnit_zero_split (v : Vec3) :
    1 + dot v (0 : Vec3) =
      (1 / 2 : ℝ) * (1 + dot v firstUnit.val) +
        (1 / 2 : ℝ) * (1 + dot v (-firstUnit.val)) := by
  simp [dot, firstUnit, Fin.sum_univ_three]
  ring

theorem main : AKLT.Blueprint.Mom.ProductMixtureStatement := by
  classical
  intro k hk a hdecomp

  let hpad : ∀ j : Fin 3, ∃ t : ℝ, ∃ u : UnitVector,
      0 ≤ t ∧ t ≤ 1 ∧ ∀ v, 1 + dot v (pad a j) =
        t * (1 + dot v u.val) + (1 - t) * (1 + dot v (-u.val)) := by
    intro j
    by_cases hj : j.val < k
    · rcases hdecomp ⟨j.val, hj⟩ with ⟨t, u, ht0, ht1, hform⟩
      refine ⟨t, u, ht0, ht1, ?_⟩
      simpa [pad, hj] using hform
    · refine ⟨1 / 2, firstUnit, by norm_num, by norm_num, ?_⟩
      intro v
      simp only [pad, dite_eq_right hj]
      rw [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]
      exact firstUnit_zero_split v

  let d : Fin 3 → ℝ := fun j => Classical.choose (hpad j)
  let e : Fin 3 → UnitVector := fun j => Classical.choose (Classical.choose_spec (hpad j))
  have hd : ∀ j, 0 ≤ d j ∧ d j ≤ 1 ∧ ∀ v,
      1 + dot v (pad a j) =
        d j * (1 + dot v (e j).val) + (1 - d j) * (1 + dot v (-(e j).val)) := by
    intro j
    exact Classical.choose_spec (Classical.choose_spec (hpad j))

  let choice := Fin 3 → Fin 2
  have hcard : Fintype.card choice = 8 := by simp [choice]
  let E : choice ≃ Fin 8 := Fintype.equivFinOfCardEq hcard
  let coef (j : Fin 3) (q : Fin 2) : ℝ :=
    if q.val = 0 then d j else 1 - d j
  let atom (j : Fin 3) (q : Fin 2) : Vec3 :=
    if q.val = 0 then (e j).val else -(e j).val
  let atomUnit (j : Fin 3) (q : Fin 2) : UnitVector :=
    ⟨atom j q, by
      fin_cases q
      · simp [atom, (e j).property]
      · have hn : normSq (-(e j).val) = normSq (e j).val := by
          simp [normSq, dot]
        simpa [atom, hn] using (e j).property⟩
  have hcoef_nonneg (j : Fin 3) (q : Fin 2) : 0 ≤ coef j q := by
    fin_cases q <;> simp [coef] <;> linarith [(hd j).1, (hd j).2.1]
  have hcoef_sum (j : Fin 3) : ∑ q : Fin 2, coef j q = 1 := by
    rw [Fin.sum_univ_two]
    simp [coef]
  have hsplit (j : Fin 3) (v : Vec3) :
      1 + dot v (pad a j) =
        ∑ q : Fin 2, coef j q * (1 + dot v (atom j q)) := by
    rw [Fin.sum_univ_two]
    simp [coef, atom]
    exact (hd j).2.2 v

  let weight (θ : choice) : ℝ := ∏ j : Fin 3, coef j (θ j)
  let vectors (θ : choice) : Fin 3 → UnitVector := fun j => atomUnit j (θ j)
  let t : Fin 8 → ℝ := fun η => weight (E.symm η)
  let b : Fin 8 → Fin 3 → UnitVector := fun η => vectors (E.symm η)

  have hweight_nonneg (θ : choice) : 0 ≤ weight θ := by
    apply Finset.prod_nonneg
    intro j hj
    exact hcoef_nonneg j (θ j)
  have htotal : (∑ η : Fin 8, t η) = 1 := by
    calc
      (∑ η : Fin 8, t η) = ∑ θ : choice, weight θ := by
        exact Fintype.sum_equiv E.symm _ _ (by intro η; rfl)
      _ = ∏ j : Fin 3, ∑ q : Fin 2, coef j q := by
        simpa [weight] using (Fintype.prod_sum (fun j : Fin 3 => fun q : Fin 2 => coef j q)).symm
      _ = 1 := by simp [hcoef_sum]
  have ht_nonneg : ∀ η, 0 ≤ t η := by
    intro η
    exact hweight_nonneg (E.symm η)
  have hexpand (v : Vec3) :
      localProduct (pad a) v =
        ∑ η : Fin 8, t η * localProduct (fun j => (b η j).val) v := by
    rw [localProduct]
    calc
      (∏ j : Fin 3, (1 + dot v (pad a j))) =
          ∏ j : Fin 3, ∑ q : Fin 2,
            coef j q * (1 + dot v (atom j q)) := by
              apply Finset.prod_congr rfl
              intro j hj
              exact hsplit j v
      _ = ∑ θ : choice, ∏ j : Fin 3,
            (coef j (θ j) * (1 + dot v (atom j (θ j)))) := by
              exact Fintype.prod_sum _
      _ = ∑ θ : choice, weight θ * localProduct (fun j => (vectors θ j).val) v := by
            apply Finset.sum_congr rfl
            intro θ hθ
            simp [weight, localProduct, vectors, atomUnit, Finset.prod_mul_distrib]
      _ = ∑ η : Fin 8, t η * localProduct (fun j => (b η j).val) v := by
            symm
            exact Fintype.sum_equiv E.symm _ _ (by intro η; rfl)

  refine ⟨t, b, ht_nonneg, htotal, ?_⟩
  intro v
  rw [localProduct_pad hk a v]
  exact hexpand v

end AKLT.W.MOM023
