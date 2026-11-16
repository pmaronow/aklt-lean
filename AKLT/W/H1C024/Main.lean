import AKLT.Cert.H1.Production.Leaves

namespace AKLT.W.H1C024

open AKLT.Defs
open AKLT.Cert.H1
open AKLT.Cert.H1.Production

private theorem ringSiteEast : ringSites.getD 0 (0, 0) = Compass.east.step := by
  simp only [ringSites, List.getD_cons_zero, Compass.step]

private theorem ringSiteNorth : ringSites.getD 2 (0, 0) = Compass.north.step := by
  simp only [ringSites, List.getD_cons_succ, List.getD_cons_zero, Compass.step]

theorem main : AKLT.Cert.H1.Production.Leaves.metadataFacts := by
  intro c hc
  rcases hc with ⟨_hinput, _hgeometry, _htables, hparameters, hout, hp, hq, _hparity⟩

  have hp' := hparameters
  simp only [parametersCheck, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq] at hp'

  have houtCases : c.out = 0 ∨ c.out = 2 := hp'.1.1.1.1.1.1.1.2
  have hwidth : 0 < c.width := hp'.1.1.1.1.1.1.2
  have hdenominator :
      (c.network.map (fun s => s.spec.totalDen)).prod = c.denominator := hp'.1.1.2

  have hrawCases : c.input.outgoing = 0 ∨ c.input.outgoing = 1 ∨ c.input.outgoing = 2 := by
    rcases houtCases with hout0 | hout2 <;> omega

  refine ⟨?_, hdenominator.symm, hwidth⟩
  change ringSites.getD c.out (0, 0) = (compassAt c.input.outgoing).step
  rcases hrawCases with hraw0 | hraw1 | hraw2
  · have hout0 : c.out = 0 := by omega
    rw [hout0, ringSiteEast, hraw0]
    simp [compassAt, Compass.step]
  · have hout2 : c.out = 2 := by omega
    rw [hout2, ringSiteNorth, hraw1]
    simp [compassAt, Compass.step]
  · rcases houtCases with hout0 | hout2 <;> omega

#print axioms main

end AKLT.W.H1C024
