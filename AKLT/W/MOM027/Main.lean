module
public import AKLT.Blueprint.Mom.NodesMean

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true
noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Mom
private theorem siteU_moment (f : Vec3 → ℝ) : siteFunctional .U f = moment f := by
  simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector, moment, Finset.mul_sum]
private theorem golden : goldenRatio ^ 2 = goldenRatio + 1 := by
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  dsimp [goldenRatio]
  nlinarith
private theorem phiPos : 0 < goldenRatio := by unfold goldenRatio; positivity
private theorem radiusSq : icoRadius ^ 2 = goldenRatio + 2 := by
  unfold icoRadius
  exact Real.sq_sqrt (by linarith [phiPos])
private theorem radiusNe : icoRadius ≠ 0 := by
  exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [phiPos]))
private theorem golden4 : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
  calc
    goldenRatio ^ 4 = (goldenRatio ^ 2) ^ 2 := by ring
    _ = (goldenRatio + 1) ^ 2 := by rw [golden]
    _ = 3 * goldenRatio + 2 := by ring_nf; rw [golden]; ring
private theorem radius4 : icoRadius ^ 4 = 5 * (goldenRatio + 1) := by
  calc
    icoRadius ^ 4 = (icoRadius ^ 2) ^ 2 := by ring
    _ = (goldenRatio + 2) ^ 2 := by rw [radiusSq]
    _ = 5 * (goldenRatio + 1) := by ring_nf; rw [golden]; ring
private theorem cosEnd : Real.cos meanPathEnd = -1 / 2 := by
  have h : meanPathEnd = Real.pi - Real.pi / 3 := by dsimp [meanPathEnd]; ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num
private theorem sinEnd : Real.sin meanPathEnd = Real.sqrt 3 / 2 := by
  have h : meanPathEnd = Real.pi - Real.pi / 3 := by dsimp [meanPathEnd]; ring
  rw [h, Real.sin_pi_sub, Real.sin_pi_div_three]
private theorem prod0 (n : Vec3) : localProduct (meanPath 0) n = (1 + n 0) ^ 3 := by
  simp [localProduct, meanPath, dot, Fin.sum_univ_three, Fin.prod_univ_three]
  ring_nf
private theorem prodEnd (n : Vec3) : localProduct (meanPath meanPathEnd) n =
    (1 + n 0) * ((1 - n 0 / 2) ^ 2 - (3 / 4) * n 1 ^ 2) := by
  rw [localProduct, Fin.prod_univ_three, meanPath, cosEnd, sinEnd]
  simp [dot, Fin.sum_univ_three]
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [hs]
  ring
private theorem meanSiteZeroDen : siteFunctional .U (localProduct (meanPath 0)) = 2 := by
  rw [siteU_moment]
  rw [show localProduct (meanPath 0) = (fun n => (1 + n 0)^3) from funext prod0]
  simp [moment, IcoLetter, Fintype.sum_prod_type, Fin.sum_univ_three,
    icoVector, signValue]
  ring_nf
  field_simp [radiusNe]
  rw [radiusSq, golden]
  ring_nf
private theorem meanSiteZeroNumX : siteFunctional .U (fun n => n 0 * localProduct (meanPath 0) n) = 6 / 5 := by
  rw [siteU_moment]
  rw [show (fun n => n 0 * localProduct (meanPath 0) n) = (fun n => n 0 * (1+n 0)^3) from by funext n; rw [prod0]]
  simp [moment, IcoLetter, Fintype.sum_prod_type, Fin.sum_univ_three,
    icoVector, signValue]
  ring_nf
  field_simp [radiusNe]
  rw [radius4, radiusSq, golden4, golden]
  ring_nf
  nlinarith [golden]
private theorem meanSiteZeroNumY : siteFunctional .U (fun n => n 1 * localProduct (meanPath 0) n) = 0 := by
  rw [siteU_moment]
  rw [show (fun n => n 1 * localProduct (meanPath 0) n) = (fun n => n 1 * (1+n 0)^3) from by funext n; rw [prod0]]
  simp [moment, IcoLetter, Fintype.sum_prod_type, Fin.sum_univ_three,
    icoVector, signValue]
  ring_nf
private theorem meanSiteZeroNumZ : siteFunctional .U (fun n => n 2 * localProduct (meanPath 0) n) = 0 := by
  rw [siteU_moment]
  rw [show (fun n => n 2 * localProduct (meanPath 0) n) = (fun n => n 2 * (1+n 0)^3) from by funext n; rw [prod0]]
  simp [moment, IcoLetter, Fintype.sum_prod_type, Fin.sum_univ_three,
    icoVector, signValue]
  ring_nf
private theorem meanSiteEndDen : siteFunctional .U (localProduct (meanPath meanPathEnd)) = 1 / 2 := by
  rw [siteU_moment]
  rw [show localProduct (meanPath meanPathEnd) = (fun n => (1 + n 0) * ((1 - n 0 / 2)^2 - (3/4)*n 1^2)) from funext prodEnd]
  simp [moment, IcoLetter, Fintype.sum_prod_type, Fin.sum_univ_three,
    icoVector, signValue]
  ring_nf
  field_simp [radiusNe]
  rw [radiusSq, golden]
  ring_nf
private theorem meanSiteEndNumX : siteFunctional .U (fun n => n 0 * localProduct (meanPath meanPathEnd) n) = 0 := by
  rw [siteU_moment]
  rw [show (fun n => n 0 * localProduct (meanPath meanPathEnd) n) = (fun n => n 0 * ((1+n 0) * ((1-n 0/2)^2 - (3/4)*n 1^2))) from by funext n; rw [prodEnd]]
  simp [moment, IcoLetter, Fintype.sum_prod_type, Fin.sum_univ_three,
    icoVector, signValue]
  ring_nf
  field_simp [radiusNe]
  rw [golden4, golden]
  ring_nf
private theorem meanSiteEndNumY : siteFunctional .U (fun n => n 1 * localProduct (meanPath meanPathEnd) n) = 0 := by
  rw [siteU_moment]
  rw [show (fun n => n 1 * localProduct (meanPath meanPathEnd) n) = (fun n => n 1 * ((1+n 0) * ((1-n 0/2)^2 - (3/4)*n 1^2))) from by funext n; rw [prodEnd]]
  simp [moment, IcoLetter, Fintype.sum_prod_type, Fin.sum_univ_three,
    icoVector, signValue]
  ring_nf
private theorem meanSiteEndNumZ : siteFunctional .U (fun n => n 2 * localProduct (meanPath meanPathEnd) n) = 0 := by
  rw [siteU_moment]
  rw [show (fun n => n 2 * localProduct (meanPath meanPathEnd) n) = (fun n => n 2 * ((1+n 0) * ((1-n 0/2)^2 - (3/4)*n 1^2))) from by funext n; rw [prodEnd]]
  simp [moment, IcoLetter, Fintype.sum_prod_type, Fin.sum_univ_three,
    icoVector, signValue]
  ring_nf

namespace AKLT.W.MOM027

theorem main : AKLT.Blueprint.Mom.MeanPathEndpointsStatement := by
  constructor
  · have hmean : localMean .U (meanPath 0) = ![3 / 5, 0, 0] := by
      funext i
      fin_cases i
      · simp [localMean, meanSiteZeroDen, meanSiteZeroNumX]
        norm_num
      · simp [localMean, meanSiteZeroDen, meanSiteZeroNumY]
      · simp [localMean, meanSiteZeroDen, meanSiteZeroNumZ]
    rw [hmean]
    norm_num [normSq, dot, Fin.sum_univ_three]
  · have hmean : localMean .U (meanPath meanPathEnd) = (0 : Vec3) := by
      funext i
      fin_cases i
      · simp [localMean, meanSiteEndDen, meanSiteEndNumX]
      · simp [localMean, meanSiteEndDen, meanSiteEndNumY]
      · simp [localMean, meanSiteEndDen, meanSiteEndNumZ]
    rw [hmean]
    simp [normSq, dot]

end AKLT.W.MOM027
