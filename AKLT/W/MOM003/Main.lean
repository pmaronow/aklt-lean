import AKLT.Blueprint.Mom.NodesMoments

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.MOM003

private def flipBit (b : Fin 2) : Fin 2 := if b = 0 then 1 else 0

private def flipAt (i : Fin 3) (j : IcoLetter) : IcoLetter :=
  if i = 0 then
    if j.1 = 0 then j
    else if j.1 = 1 then (j.1, flipBit j.2.1, j.2.2)
    else (j.1, j.2.1, flipBit j.2.2)
  else if i = 1 then
    if j.1 = 2 then j
    else if j.1 = 0 then (j.1, flipBit j.2.1, j.2.2)
    else (j.1, j.2.1, flipBit j.2.2)
  else
    if j.1 = 1 then j
    else if j.1 = 0 then (j.1, j.2.1, flipBit j.2.2)
    else (j.1, flipBit j.2.1, j.2.2)

private theorem flipBit_involutive (b : Fin 2) : flipBit (flipBit b) = b := by
  fin_cases b <;> simp [flipBit]

private theorem flipAt_involutive (i : Fin 3) (j : IcoLetter) :
    flipAt i (flipAt i j) = j := by
  rcases j with ⟨a, b, c⟩
  fin_cases i <;> fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [flipAt, flipBit]

private def flipEquiv (i : Fin 3) : IcoLetter ≃ IcoLetter where
  toFun := flipAt i
  invFun := flipAt i
  left_inv := flipAt_involutive i
  right_inv := flipAt_involutive i

private theorem icoVector_flipAt (i : Fin 3) (j : IcoLetter) (k : Fin 3) :
    icoVector (flipAt i j) k = if k = i then -icoVector j k else icoVector j k := by
  rcases j with ⟨a, b, c⟩
  fin_cases i <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases k <;>
    simp [flipAt, flipBit, icoVector, signValue] <;> ring

private theorem neg_pow_of_odd {x : ℝ} {n : ℕ} (hn : Odd n) :
    (-x) ^ n = -(x ^ n) := by
  rcases hn with ⟨k, hk⟩
  subst n
  calc
    (-x) ^ (2 * k + 1) = ((-x) ^ 2) ^ k * (-x) := by
      rw [pow_add, pow_mul]
      simp
    _ = (x ^ 2) ^ k * (-x) := by
      rw [show (-x) ^ 2 = x ^ 2 by ring]
    _ = -((x ^ 2) ^ k * x) := by ring
    _ = -(x ^ (2 * k + 1)) := by
      rw [pow_add, pow_mul]
      simp

private theorem mono_update_odd (i : Fin 3) (m : Fin 3 → ℕ) (hm : Odd (m i))
    (v : Vec3) : AKLT.Blueprint.Mom.mono m (Function.update v i (-v i)) =
      -AKLT.Blueprint.Mom.mono m v := by
  unfold AKLT.Blueprint.Mom.mono
  have hfun : (fun k : Fin 3 => Function.update v i (-v i) k ^ m k) =
      Function.update (fun k : Fin 3 => v k ^ m k) i ((-v i) ^ m i) := by
    funext k
    by_cases hk : k = i
    · subst k
      simp
    · simp [Function.update, hk]
  have hprod : (∏ k : Fin 3, v k ^ m k) =
      (v i ^ m i) * (∏ k ∈ Finset.univ \ {i}, v k ^ m k) := by
    rw [Finset.prod_eq_mul_prod_sdiff_singleton (s := Finset.univ) i
      (fun k : Fin 3 => v k ^ m k) (by simp)]
  rw [hfun]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)
    (fun k : Fin 3 => v k ^ m k) ((-v i) ^ m i)]
  rw [hprod, neg_pow_of_odd hm]
  ring

private theorem mono_flipAt (i : Fin 3) (m : Fin 3 → ℕ) (hm : Odd (m i))
    (j : IcoLetter) :
    AKLT.Blueprint.Mom.mono m (icoVector (flipAt i j)) =
      -AKLT.Blueprint.Mom.mono m (icoVector j) := by
  have hv : icoVector (flipAt i j) = Function.update (icoVector j) i (-icoVector j i) := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [Function.update, icoVector_flipAt]
    · simp [Function.update, hk, icoVector_flipAt]
  rw [hv]
  exact mono_update_odd i m hm (icoVector j)

theorem main : AKLT.Blueprint.Mom.OddMonomialStatement := by
  intro m hm
  obtain ⟨i, hi⟩ := hm
  let S : ℝ := ∑ j : IcoLetter, AKLT.Blueprint.Mom.mono m (icoVector j)
  have hReindex : S = ∑ j : IcoLetter,
      AKLT.Blueprint.Mom.mono m (icoVector (flipAt i j)) := by
    dsimp [S]
    exact (Equiv.sum_comp (flipEquiv i)
      (fun j : IcoLetter => AKLT.Blueprint.Mom.mono m (icoVector j))).symm
  have hNeg : (∑ j : IcoLetter,
      AKLT.Blueprint.Mom.mono m (icoVector (flipAt i j))) = -S := by
    change (∑ j : IcoLetter,
      AKLT.Blueprint.Mom.mono m (icoVector (flipAt i j))) =
      -(∑ j : IcoLetter, AKLT.Blueprint.Mom.mono m (icoVector j))
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact mono_flipAt i m hi j
  have hZero : S = 0 := by linarith
  simp [AKLT.Defs.moment, S, hZero]

end AKLT.W.MOM003
