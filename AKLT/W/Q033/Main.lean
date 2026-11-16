import AKLT.Blueprint.Q.NodesSplits
import AKLT.Uniq.Divisibility

noncomputable section

open AKLT.Challenge
open AKLT.Uniq

namespace AKLT.W.Q033

theorem main : AKLT.Blueprint.Q.CentreDegreeCancellationStatement := by
  intro L N x p χ hp hdegP hdegProd
  have hpHom : p.IsWeightedHomogeneous (siteWeight x) 4 := by
    intro d hd
    rw [siteWeight_degree]
    exact hdegP d (MvPolynomial.mem_support_iff.mpr hd)
  have hprodHom : (p * χ).IsWeightedHomogeneous (siteWeight x) 4 := by
    intro d hd
    rw [siteWeight_degree]
    exact hdegProd d (MvPolynomial.mem_support_iff.mpr hd)
  have hχHom : χ.IsWeightedHomogeneous (siteWeight x) 0 := by
    apply homogeneous_quotient (siteWeight x) hp hpHom
    simpa using hprodHom
  intro d hd
  have hweight := hχHom (MvPolynomial.mem_support_iff.mp hd)
  rw [siteWeight_degree] at hweight
  constructor <;> omega

end AKLT.W.Q033

#print axioms AKLT.W.Q033.main
