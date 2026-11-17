module
public import AKLT.Blueprint.H1.NodesV2Structure

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.W.H1M067

 theorem main : AKLT.Blueprint.H1.OperatorStructureLinearCombinationStatementV2 := by
  intro π r A B hA hB a b
  dsimp [AKLT.Blueprint.H1.OperatorStructureAtV2] at hA hB ⊢
  rcases hA with ⟨hAh, hAr, hASU, hAZ, hAplus, hAminus, hApair⟩
  rcases hB with ⟨hBh, hBr, hBSU, hBZ, hBplus, hBminus, hBpair⟩
  have hOlin : Matrix.toEuclideanLin ((a : ℂ) • A + (b : ℂ) • B) =
      (a : ℂ) • Matrix.toEuclideanLin A + (b : ℂ) • Matrix.toEuclideanLin B := by
    rw [Matrix.toEuclideanLin.map_add, Matrix.toEuclideanLin.map_smul,
      Matrix.toEuclideanLin.map_smul]
  have hOlinReal : Matrix.toEuclideanLin (a • A + b • B) =
      a • Matrix.toEuclideanLin A + b • Matrix.toEuclideanLin B := by
    simpa [Complex.real_smul] using hOlin
  have haSelf : IsSelfAdjoint a := by
    change star a = a
    rfl
  have hbSelf : IsSelfAdjoint b := by
    change star b = b
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hAh.smul haSelf).add (hBh.smul hbSelf)
  · intro σ τ
    have hAi := hAr σ τ
    have hBi := hBr σ τ
    change ((a • A σ τ) + (b • B σ τ)).im = 0
    simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, hAi, hBi,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  · intro g hg hd
    exact (Commute.smul_left (hASU g hg hd) a).add_left
      (Commute.smul_left (hBSU g hg hd) b)
  · have hAO : Commute (Matrix.toEuclideanLin A) (totalSpinZ (reductionVectors π r)) := hAZ
    have hBO : Commute (Matrix.toEuclideanLin B) (totalSpinZ (reductionVectors π r)) := hBZ
    rw [hOlinReal]
    exact (Commute.smul_left hAO a).add_left (Commute.smul_left hBO b)
  · have hAO : Commute (Matrix.toEuclideanLin A) (totalSpinPlus (reductionVectors π r)) := hAplus
    have hBO : Commute (Matrix.toEuclideanLin B) (totalSpinPlus (reductionVectors π r)) := hBplus
    rw [hOlinReal]
    exact (Commute.smul_left hAO a).add_left (Commute.smul_left hBO b)
  · have hAO : Commute (Matrix.toEuclideanLin A) (totalSpinMinus (reductionVectors π r)) := hAminus
    have hBO : Commute (Matrix.toEuclideanLin B) (totalSpinMinus (reductionVectors π r)) := hBminus
    rw [hOlinReal]
    exact (Commute.smul_left hAO a).add_left (Commute.smul_left hBO b)
  · intro x hx
    constructor
    · intro hU
      have hAU := hApair x hx |>.1 hU
      have hBU := hBpair x hx |>.1 hU
      rw [hOlinReal]
      calc
        a • Matrix.toEuclideanLin A + b • Matrix.toEuclideanLin B =
            a • (symmetricPairProjection (reductionVectors π r) (leaderToken π r x)
              (secondToken π r x hx) * Matrix.toEuclideanLin A *
              symmetricPairProjection (reductionVectors π r) (leaderToken π r x)
              (secondToken π r x hx)) +
            b • (symmetricPairProjection (reductionVectors π r) (leaderToken π r x)
              (secondToken π r x hx) * Matrix.toEuclideanLin B *
              symmetricPairProjection (reductionVectors π r) (leaderToken π r x)
              (secondToken π r x hx)) := by
          conv_lhs => rw [hAU, hBU]
        _ = symmetricPairProjection (reductionVectors π r) (leaderToken π r x)
              (secondToken π r x hx) *
            (a • Matrix.toEuclideanLin A + b • Matrix.toEuclideanLin B) *
            symmetricPairProjection (reductionVectors π r) (leaderToken π r x)
              (secondToken π r x hx) := by
          simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
    · intro hD
      have hAO := (hApair x hx).2 hD
      have hBO := (hBpair x hx).2 hD
      rw [hOlinReal]
      exact (Commute.smul_left hAO a).add_left (Commute.smul_left hBO b)

end AKLT.W.H1M067
