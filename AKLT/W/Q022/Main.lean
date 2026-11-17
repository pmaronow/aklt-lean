import AKLT.Blueprint.Q.NodesPolynomial
import AKLT.Uniq.Geometry

noncomputable section
open AKLT.Challenge

namespace AKLT.W.Q022

theorem main : AKLT.Blueprint.Q.VbsHomogeneityStatement := by
  intro L N m hm x
  change m (x, 0) + m (x, 1) = 4
  have hhom := AKLT.Uniq.vbsHomogeneous L N x
  have hmcoeff : (vbsPolynomial L N).coeff m ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  have hw := hhom hmcoeff
  exact (AKLT.Uniq.siteWeight_degree m x).symm.trans hw

end AKLT.W.Q022
