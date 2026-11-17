import AKLT.Blueprint.Win.NodesRemoval
import AKLT.Blueprint.Win.NodesCut

-- Inspection only: no proof declarations or repository modifications.
set_option autoImplicit false
set_option pp.universes true

#check AKLT.Blueprint.Win.RemovedPairResponseStatement
#check AKLT.Blueprint.Win.PairDifferenceStatement
#check AKLT.Blueprint.Win.LogStepIdentityStatement
#check AKLT.Blueprint.Win.LocalLogEstimateStatement
#check AKLT.Blueprint.Win.RemovalTelescopeStatement
#check AKLT.Blueprint.Win.RemovalCostSumStatement
#check AKLT.Blueprint.Win.FrameFibreSumStatement
#check AKLT.Blueprint.Win.ComplementQuadratureStatement

#print AKLT.Blueprint.Win.RemovalEnumeration
#print AKLT.Blueprint.Win.PairDifferenceStatement
#print AKLT.Blueprint.Win.RemovalTelescopeStatement
#print AKLT.Blueprint.Win.RemovalCostSumStatement
#print AKLT.Blueprint.Win.FrameFibreSumStatement
#print AKLT.Blueprint.Win.ComplementQuadratureStatement

#check (fun (X : Finset AKLT.Defs.Plane)
  (e : AKLT.Blueprint.Win.RemovalEnumeration X) => e.site 0)
#check (fun (X : Finset AKLT.Defs.Plane)
  (e : AKLT.Blueprint.Win.RemovalEnumeration X)
  (j : Fin e.last) => e.site j.succ)
#synth Fintype (AKLT.Defs.PlaneConfiguration ∅)
#synth DecidableEq (AKLT.Defs.PlaneConfiguration ∅)
#synth Fintype (AKLT.Defs.originalLegs ∅)
#check ((fun (θ : ℝ) => θ ^ (-3 : ℤ)) : ℝ → ℝ)
#check ((fun (θ : ℝ) (n : ℕ) => θ ^ (n - 3)) : ℝ → ℕ → ℝ)
#eval ENat.toNat ⊤
#eval (Finset.univ : Finset (Fin 0)).card
