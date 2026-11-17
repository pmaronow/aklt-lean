module
public import AKLT.W.REC014.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC014

/-- Equality may be checked by summing over one coordinate on every fibre. -/
theorem sum_eq_of_fibre {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι) (F H : (ι → SpinLetter) → ℝ)
    (h : ∀ n, (∑ j, F (Function.update n y j)) =
      ∑ j, H (Function.update n y j)) : (∑ n, F n) = ∑ n, H n := by
  let e := Equiv.funSplitAt y SpinLetter
  rw [← e.symm.sum_comp F, ← e.symm.sum_comp H]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun j r => H (e.symm (j,r)))]
  apply Finset.sum_congr rfl
  intro r _
  have he (j) : e.symm (j,r) = Function.update (e.symm (none,r)) y j := by
    funext x
    by_cases hx : x = y
    · subst x; simp [e, Equiv.funSplitAt_symm_apply]
    · simp [e, Equiv.funSplitAt_symm_apply, hx]
  calc
    _ = ∑ j, F (Function.update (e.symm (none,r)) y j) :=
      Finset.sum_congr rfl fun j _ => congrArg F (he j)
    _ = ∑ j, H (Function.update (e.symm (none,r)) y j) := h _
    _ = _ := Finset.sum_congr rfl fun j _ => congrArg H (he j).symm

theorem prod_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → Status) (n : ι → SpinLetter) (y : ι) (j : SpinLetter) :
    (∏ x, spinWeight (s x) ((Function.update n y j) x)) =
      spinWeight (s y) j * ∏ x ∈ Finset.univ.erase y, spinWeight (s x) (n x) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ y)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  rw [Function.update_of_ne (Finset.mem_erase.mp hx).1]

/-- The zero first moment integrates a single U bond to one; the new isolated
D site also has mass one. All other factors are constant on this fibre. -/
theorem integrate_leaf {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → Status) (y o : ι) (hyo : o ≠ y) (hy : s y = .U)
    (H : (ι → SpinLetter) → ℝ)
    (hH : ∀ n j, H (Function.update n y j) = H n) :
    (∑ n, (∏ x, spinWeight (s x) (n x)) * H n *
        (1 + dot (spinVector (n y)) (spinVector (n o)))) =
      ∑ n, (∏ x, spinWeight ((Function.update s y .D) x) (n x)) * H n := by
  apply sum_eq_of_fibre y
  intro n
  simp_rw [prod_update, hH, Function.update_self, Function.update_of_ne hyo, hy]
  have hp : (∏ x ∈ Finset.univ.erase y,
      spinWeight ((Function.update s y .D) x) (n x)) =
      ∏ x ∈ Finset.univ.erase y, spinWeight (s x) (n x) := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.mem_erase.mp hx).1]
  rw [hp]
  calc
    _ = (∑ j, spinWeight .U j * (1 + dot (spinVector j) (spinVector (n o)))) *
        ((∏ x ∈ Finset.univ.erase y, spinWeight (s x) (n x)) * H n) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∏ x ∈ Finset.univ.erase y, spinWeight (s x) (n x)) * H n := by
      rw [weighted_factor_one, one_mul]
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, weight_sum .D (by decide), one_mul]

end AKLT.W.REC014
