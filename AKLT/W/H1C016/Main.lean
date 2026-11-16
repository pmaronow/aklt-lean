import AKLT.W.H1C016.Geometry
import AKLT.W.H1C016.Threshold

namespace AKLT.W.H1C016

open AKLT.Cert.H1 AKLT.Cert.H1.Production

theorem main : AKLT.Cert.H1.Production.Leaves.sectorCoefficientBound := by
  intro c hc b hb row col
  rcases hc with ⟨hi,hg,_ht,hparams,ho,_hp,_hq,_hpar⟩
  have hbase := sector_bases_eq c.network b.sector b.block.parity hb.2.1
  have hd := parameters_dimensions c.network c.out c.width c.lanes c.denominator c.p c.q hparams
  have hds : ∀ s ∈ b.sector, 0 < s.base.spec.dim := by
    intro s hs
    apply hd s.base
    rw [← hbase]
    exact List.mem_map_of_mem hs
  have hnonempty : b.sector ≠ [] := by
    intro he
    have hlen := congrArg List.length hbase
    have h8 := (geometry_spec c.input c.network hg).1
    simp only [he, List.map_nil, List.length_nil] at hlen
    omega
  have hprod : (b.sector.map (fun s => tableAbs s.base.table)).prod =
      (c.network.map (fun s => tableAbs s.table)).prod := by
    calc
      _ = ((b.sector.map SectorSite.base).map (fun s => tableAbs s.table)).prod := by
        simp only [List.map_map, Function.comp_def]
      _ = _ := congrArg (fun base : List PackedSite =>
        (base.map (fun s => tableAbs s.table)).prod) hbase
  have hcounts := center_counts c.input c.network c.out hi hg ho
  have hcoef := threshold_bound b.sector c.out c.p c.q row col
    (b.sector.map (fun s => tableAbs s.base.table)).prod
    (fun codes => ring_value_le b.sector hnonempty hds row col codes)
    (by simpa only [hbase] using hcounts.1)
    (by simpa only [hbase] using hcounts.2)
  rw [hprod] at hcoef
  have hchecked : bound c.network c.p c.q < 2^(c.width-1) := by
    simp only [parametersCheck, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hparams
    exact hparams.1.2
  exact hcoef.trans_lt hchecked

#print axioms main

end AKLT.W.H1C016
