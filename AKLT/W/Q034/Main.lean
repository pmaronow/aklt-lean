import AKLT.Blueprint.Q.NodesSplits
import AKLT.Uniq.Divisibility

noncomputable section
open scoped BigOperators
open AKLT.Challenge

namespace AKLT.W.Q034

private def incidentBondsAt {L N : Size} (x : Site L N) : Finset (Bond L N) :=
  AKLT.Uniq.incidentBonds ({x} : Finset (Site L N))

private theorem incidentProduct_eq_filtered {L N : Size} (x : Site L N) :
    AKLT.Blueprint.Q.incidentProduct x =
      ∏ e ∈ incidentBondsAt x, singlet e := by
  classical
  let S : Finset (Bond L N) := Finset.univ.filter (fun e => x ∈ bondSites e)
  have hS : incidentBondsAt x = S := by
    ext e
    simp [S, incidentBondsAt, AKLT.Uniq.incidentBonds]
  calc
    AKLT.Blueprint.Q.incidentProduct x = ∏ e ∈ S, singlet e := by
      rw [AKLT.Blueprint.Q.incidentProduct]
      have hprod := Finset.prod_ite_mem_eq S (singlet : Bond L N → SpinorPolynomial L N)
      simpa [S] using hprod
    _ = ∏ e ∈ incidentBondsAt x, singlet e := by rw [hS]

private theorem incidentProduct_nonzero {L N : Size} (x : Site L N) :
    AKLT.Blueprint.Q.incidentProduct x ≠ 0 := by
  rw [incidentProduct_eq_filtered]
  exact AKLT.Uniq.product_singlet_ne_zero (incidentBondsAt x)

private theorem incidentProduct_degree {L N : Size} (x : Site L N)
    (m : (Site L N × Fin 2) →₀ ℕ)
    (hm : m ∈ (AKLT.Blueprint.Q.incidentProduct x).support) :
    m (x, 0) + m (x, 1) = 4 := by
  have hhom : AKLT.Uniq.HasSiteDegrees (AKLT.Blueprint.Q.incidentProduct x)
      (fun y => ∑ e ∈ incidentBondsAt x, AKLT.Uniq.bondDegree e y) := by
    rw [incidentProduct_eq_filtered]
    exact AKLT.Uniq.product_siteDegrees (incidentBondsAt x)
  have hweight := hhom x (MvPolynomial.mem_support_iff.mp hm)
  rw [AKLT.Uniq.siteWeight_degree] at hweight
  have hcount : (∑ e ∈ incidentBondsAt x, AKLT.Uniq.bondDegree e x) = 4 := by
    exact AKLT.Uniq.incident_degree ({x} : Finset (Site L N)) (by simp)
  change m (x, 0) + m (x, 1) =
    (∑ e ∈ incidentBondsAt x, AKLT.Uniq.bondDegree e x) at hweight
  rw [hcount] at hweight
  exact hweight

theorem main : AKLT.Blueprint.Q.IncidentProductDegreeStatement := by
  intro L N x
  exact ⟨incidentProduct_nonzero x, fun m hm => incidentProduct_degree x m hm⟩

#print axioms main

end AKLT.W.Q034
