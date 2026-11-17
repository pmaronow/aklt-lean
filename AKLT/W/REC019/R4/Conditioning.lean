module
public import AKLT.W.REC019.R4.Local

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC019.R4

/-- A product of three one-site densities, after fixing the remaining spins. -/
def fibreDensity (s : Fin 3 → Status) (a : Fin 3 → Fin 3 → SpinLetter)
    (j : Fin 3) (t : SpinLetter) : ℝ :=
  spinWeight (s j) t * localProduct (fun k => spinVector (a j k)) (spinVector t)

def fibreMass (s : Fin 3 → Status) (a : Fin 3 → Fin 3 → SpinLetter) : ℝ :=
  ∏ j, ∑ t, fibreDensity s a j t

def fibreMean (s : Fin 3 → Status) (a : Fin 3 → Fin 3 → SpinLetter)
    (j : Fin 3) : Vec3 :=
  localMean (s j) (fun k => spinVector (a j k))

lemma sum_three {α : Type*} [Fintype α] (f : (Fin 3 → α) → ℝ) :
    (∑ t, f t) = ∑ x, ∑ y, ∑ z, f ![x, y, z] := by
  classical
  let e : (Fin 3 → α) ≃ α × α × α :=
    { toFun := fun t => (t 0, t 1, t 2)
      invFun := fun t => ![t.1, t.2.1, t.2.2]
      left_inv := by intro t; funext i; fin_cases i <;> rfl
      right_inv := by intro t; rfl }
  have h := Fintype.sum_equiv e f (fun t => f ![t.1, t.2.1, t.2.2])
    (fun t => congrArg f (e.symm_apply_apply t).symm)
  simpa [Fintype.sum_prod_type] using h

lemma fibre_mass_eq (s : Fin 3 → Status) (a : Fin 3 → Fin 3 → SpinLetter) :
    (∑ t : Fin 3 → SpinLetter, ∏ j, fibreDensity s a j (t j)) = fibreMass s a := by
  exact (Fintype.prod_sum (fun j t => fibreDensity s a j t)).symm

lemma fibre_density_nonneg (s : Fin 3 → Status) (a : Fin 3 → Fin 3 → SpinLetter)
    (j : Fin 3) (t : SpinLetter) : 0 ≤ fibreDensity s a j t := by
  apply mul_nonneg (spin_weight_nonneg _ _)
  apply Finset.prod_nonneg
  intro k _
  exact one_add_dot_nonneg (spin_ball t) (spin_ball (a j k))

lemma fibre_mass_pos (s : Fin 3 → Status) (hs : ∀ j, s j = .U ∨ s j = .D)
    (a : Fin 3 → Fin 3 → SpinLetter) : 0 < fibreMass s a := by
  apply Finset.prod_pos
  intro j _
  have h := (atom_mean_bound (s j) (hs j) (a j)).1
  change 0 < siteFunctional (s j) (localProduct (fun k => spinVector (a j k)))
  linarith

lemma fibre_mean_bound (s : Fin 3 → Status) (hs : ∀ j, s j = .U ∨ s j = .D)
    (a : Fin 3 → Fin 3 → SpinLetter) (j : Fin 3) :
    normSq (fibreMean s a j) ≤ 9 / 25 := by
  have h := (atom_mean_bound (s j) (hs j) (a j)).2
  norm_num only [show (3 / 5 : ℝ)^2 = 9 / 25 by norm_num] at h
  exact h

set_option maxRecDepth 2048 in
/-- Explicit finite distributivity on a three-spin fibre. -/
lemma fibre_pair_eq (s : Fin 3 → Status) (hs : ∀ j, s j = .U ∨ s j = .D)
    (a : Fin 3 → Fin 3 → SpinLetter) (p q : Fin 3) (hpq : p ≠ q) :
    (∑ t : Fin 3 → SpinLetter, (∏ j, fibreDensity s a j (t j)) *
      dot (spinVector (t p)) (spinVector (t q))) =
    fibreMass s a * dot (fibreMean s a p) (fibreMean s a q) := by
  let A : Fin 3 → ℝ := fun j => ∑ t, fibreDensity s a j t
  let B : Fin 3 → Fin 3 → ℝ := fun j i => ∑ t, fibreDensity s a j t * spinVector t i
  have hA : ∀ j, A j ≠ 0 := by
    intro j
    have h := (atom_mean_bound (s j) (hs j) (a j)).1
    change siteFunctional (s j) (localProduct (fun k => spinVector (a j k))) ≠ 0
    linarith
  have hmean : ∀ j i, fibreMean s a j i = B j i / A j := by
    intro j i
    simp only [fibreMean, localMean, siteFunctional, fibreDensity, A, B]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    ring
  simp only [dot, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [hmean]
  have he : (∑ t : Fin 3 → SpinLetter, (∏ j, fibreDensity s a j (t j)) *
      (spinVector (t p) i * spinVector (t q) i)) =
      ∏ j : Fin 3, ∑ t, fibreDensity s a j t *
        (if j = p then spinVector t i else 1) *
        (if j = q then spinVector t i else 1) := by
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro t _
    fin_cases p <;> fin_cases q <;>
      simp [Fin.prod_univ_three] <;> ring
  rw [he]
  field_simp [hA p, hA q]
  fin_cases p <;> fin_cases q <;> try contradiction
  all_goals
    norm_num only [fibreMass, Fin.prod_univ_three, Fin.ext_iff, Fin.val_zero, Fin.val_one,
      Fin.val_two, Fin.val_mk, reduceIte, mul_one, one_mul, A, B]
    first
    | change (((B 0 i * B 1 i) * A 2) * A 0) * A 1 = (((A 0 * A 1) * A 2) * B 0 i) * B 1 i
    | change (((B 0 i * A 1) * B 2 i) * A 0) * A 2 = (((A 0 * A 1) * A 2) * B 0 i) * B 2 i
    | change (((B 0 i * B 1 i) * A 2) * A 1) * A 0 = (((A 0 * A 1) * A 2) * B 1 i) * B 0 i
    | change (((A 0 * B 1 i) * B 2 i) * A 1) * A 2 = (((A 0 * A 1) * A 2) * B 1 i) * B 2 i
    | change (((B 0 i * A 1) * B 2 i) * A 2) * A 0 = (((A 0 * A 1) * A 2) * B 2 i) * B 0 i
    | change (((A 0 * B 1 i) * B 2 i) * A 2) * A 1 = (((A 0 * A 1) * A 2) * B 2 i) * B 1 i
    ring


end AKLT.W.REC019.R4
