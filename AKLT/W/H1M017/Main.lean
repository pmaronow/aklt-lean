module
public import AKLT.Blueprint.H1.NodesPauli

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder Matrix

namespace AKLT.W.H1M017

theorem main : AKLT.Blueprint.H1.BlochPositivityStatement := by
  intro A hA r hr0 hr1 hsq
  let B : Matrix (Fin 2) (Fin 2) ℂ := 1 + A
  have hBB : (Bᴴ * B).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B
  have hscalar : (((1 - r : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).PosSemidef := by
    exact Matrix.PosSemidef.smul Matrix.PosSemidef.one (sub_nonneg.mpr hr1)
  have hsum : (Bᴴ * B + ((1 - r : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).PosSemidef :=
    hBB.add hscalar
  have heq : Bᴴ * B + ((1 - r : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = (2 : ℝ) • B := by
    simp only [B, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hA.eq]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
    rw [hsq]
    module
  have hhalf := hsum.smul (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)
  rw [heq] at hhalf
  have hBpos : B.PosSemidef := by
    simpa [smul_smul] using hhalf
  have hcoef : (0 : ℂ) ≤ (1 / 2 : ℂ) := by
    rw [Complex.nonneg_iff]
    norm_num
  exact hBpos.smul hcoef

end AKLT.W.H1M017
