module
public import AKLT.W.H1C009.Raw

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C009
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

theorem internal_at (i : Nat) (hi : i < 16) :
    internalTemplateEdges.getD i ((0,0),(0,0)) ∈ internalBonds templateSites := by
  rw [internalBonds_explicit]
  apply List.mem_toFinset.mpr
  have hj : i < internalTemplateEdges.length := by simpa [internalTemplateEdges] using hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem hj

theorem present_internal (π : PatternData) (i : Nat) (hi : i < 16) :
    let e := internalTemplateEdges.getD i ((0,0),(0,0))
    presentBond π e.1 e.2 = decide (e ∈ π.bonds) := by
  let e := internalTemplateEdges.getD i ((0,0),(0,0))
  have hrev : (e.2,e.1) ∉ internalBonds templateSites := by
    rw [internalBonds_explicit]
    dsimp only [e]
    interval_cases i <;> simp [internalTemplateEdges]
  have hn : (e.2,e.1) ∉ π.bonds := fun h => hrev (Finset.mem_filter.mp h).1
  change decide (e ∈ π.bonds ∨ (e.2,e.1) ∈ π.bonds) = decide (e ∈ π.bonds)
  simp only [hn, or_false]

theorem oriented_edge (π : PatternData) (i : Nat) (hi : i < 16) :
    decide (internalTemplateEdges.getD i ((0,0),(0,0)) ∈ π.bonds) =
      presentBond π (templateEdges.getD i ((0,0),(0,0))).1
        (templateEdges.getD i ((0,0),(0,0))).2 := by
  rw [← present_internal π i hi]
  interval_cases i <;> simp [internalTemplateEdges, templateEdges, presentBond, or_comm]

theorem incident_filter (π : PatternData) (x : Plane) :
    (π.bonds.filter fun e => e.1 = x ∨ e.2 = x) =
      (internalTemplateEdges.toFinset.filter fun e => e.1 = x ∨ e.2 = x).filter
        (fun e => e ∈ π.bonds) := by
  ext e
  have hs : e ∈ π.bonds → e ∈ internalTemplateEdges.toFinset := by
    intro h
    rw [← internalBonds_explicit]
    exact (Finset.mem_filter.mp h).1
  simp only [Finset.mem_filter]
  tauto

theorem filter_singleton_card {α : Type} [DecidableEq α] (P : α → Prop)
    [DecidablePred P] (e : α) : (({e} : Finset α).filter P).card = (decide (P e)).toNat := by
  by_cases h : P e <;> simp [Finset.filter_singleton, h]

theorem filter_pair_card {α : Type} [DecidableEq α] (P : α → Prop)
    [DecidablePred P] (e f : α) (hne : e ≠ f) :
    (({e,f} : Finset α).filter P).card = (decide (P e)).toNat + (decide (P f)).toNat := by
  by_cases he : P e <;> by_cases hf : P f <;> simp [Finset.filter_insert, Finset.filter_singleton, he,hf,hne]

def groupDegreeBits (bits : Nat → Bool) (i : Nat) : Nat :=
  if i%2 == 0 then (bits (12+i/2)).toNat
  else (bits (4+i)).toNat + (bits (4+(i+7)%8)).toNat

def groupIncident (i : Nat) : Finset (Plane × Plane) :=
  if i%2 == 0 then {internalTemplateEdges.getD (12+i/2) ((0,0),(0,0))}
  else {internalTemplateEdges.getD (4+i) ((0,0),(0,0)),
    internalTemplateEdges.getD (4+(i+7)%8) ((0,0),(0,0))}

set_option maxRecDepth 2000 in
theorem group_incident (i : Nat) (hi : i < 8) :
    (internalTemplateEdges.toFinset.filter fun e => e.1 = groupPoint i ∨ e.2 = groupPoint i) =
      groupIncident i := by
  interval_cases i <;>
    simp [groupIncident, internalTemplateEdges, groupPoint, ringSites, Finset.filter_insert, Finset.filter_singleton,
      Finset.pair_comm]

theorem degree_group (π : PatternData) (i : Nat) (hi : i < 8) :
    patternDegree π (groupPoint i) =
      groupDegreeBits (fun j => decide (internalTemplateEdges.getD j ((0,0),(0,0)) ∈ π.bonds)) i := by
  unfold patternDegree
  rw [incident_filter, group_incident i hi]
  unfold groupIncident groupDegreeBits
  split_ifs with hp
  · exact filter_singleton_card (fun e => e ∈ π.bonds) _
  · apply filter_pair_card
    interval_cases i <;> simp_all [internalTemplateEdges]

end AKLT.W.H1C009
