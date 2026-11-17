module
public import AKLT.Blueprint.Mom.NodesMean

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.MOM025

theorem main : AKLT.Blueprint.Mom.DepletedContractionStatement := by
  intro k a hAUpos
  let Uden : ℝ := siteFunctional .U (localProduct a)
  let Dden : ℝ := siteFunctional .D (localProduct a)
  have hLaw := AKLT.Blueprint.Mom.siteLawDecomposition
  have hzero : localProduct a (0 : Vec3) = 1 := by
    simp [localProduct, dot]
  have hden : Dden = (3 / 5 : ℝ) * Uden + 2 / 5 := by
    dsimp [Dden, Uden]
    calc
      siteFunctional .D (localProduct a) =
          (3 / 5 : ℝ) * moment (localProduct a) + (2 / 5) * localProduct a 0 :=
        hLaw.2 (localProduct a)
      _ = (3 / 5 : ℝ) * siteFunctional .U (localProduct a) + 2 / 5 := by
        rw [← hLaw.1 (localProduct a), hzero]
        ring
  have hUpos' : 0 < Uden := hAUpos
  have hDpos : 0 < Dden := by
    rw [hden]
    positivity
  have hnum (i : Fin 3) :
      siteFunctional .D (fun n => n i * localProduct a n) =
        (3 / 5 : ℝ) * siteFunctional .U (fun n => n i * localProduct a n) := by
    calc
      siteFunctional .D (fun n => n i * localProduct a n) =
          (3 / 5 : ℝ) * moment (fun n => n i * localProduct a n) +
            (2 / 5) * ((0 : Vec3) i * localProduct a 0) :=
        hLaw.2 (fun n => n i * localProduct a n)
      _ = (3 / 5 : ℝ) * siteFunctional .U (fun n => n i * localProduct a n) := by
        rw [← hLaw.1 (fun n => n i * localProduct a n)]
        simp
  let q : ℝ := ((3 / 5 : ℝ) * Uden) / Dden
  have hqpos : 0 < q := by
    dsimp [q]
    exact div_pos (mul_pos (by norm_num) hUpos') hDpos
  have hqle : q ≤ 1 := by
    have hqlt : q < 1 := by
      dsimp [q]
      rw [div_lt_iff₀ hDpos]
      rw [hden]
      norm_num
    exact hqlt.le
  have hqSq : q ^ 2 ≤ 1 := by
    have hmul := mul_le_mul hqle hqle hqpos.le (by norm_num : (0 : ℝ) ≤ 1)
    simpa [pow_two] using hmul
  have hmeanCoord (i : Fin 3) :
      localMean .D a i = q * localMean .U a i := by
    change siteFunctional .D (fun n => n i * localProduct a n) / Dden =
      q * (siteFunctional .U (fun n => n i * localProduct a n) / Uden)
    rw [hnum i]
    dsimp [q]
    field_simp [ne_of_gt hDpos, ne_of_gt hUpos']
  have hmean : localMean .D a = fun i => q * localMean .U a i := by
    funext i
    exact hmeanCoord i
  have hscale (v : Vec3) : normSq (fun i => q * v i) = q ^ 2 * normSq v := by
    simp only [normSq, dot]
    calc
      (∑ i, (q * v i) * (q * v i)) = ∑ i, q ^ 2 * (v i * v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = q ^ 2 * ∑ i, v i * v i := by rw [Finset.mul_sum]
  have hnorm : normSq (localMean .D a) = q ^ 2 * normSq (localMean .U a) := by
    rw [hmean]
    exact hscale (localMean .U a)
  refine ⟨hDpos, ?_⟩
  rw [hnorm]
  calc
    q ^ 2 * normSq (localMean .U a) ≤ 1 * normSq (localMean .U a) :=
      mul_le_mul_of_nonneg_right hqSq (AKLT.Blueprint.Mom.normSq_nonneg _)
    _ = normSq (localMean .U a) := one_mul _

end AKLT.W.MOM025
