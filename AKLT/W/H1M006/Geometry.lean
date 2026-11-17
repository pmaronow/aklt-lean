module
public import AKLT.W.H1M006.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M006

def passageSites : Finset Plane := {(1, 0), (0, 1), (-1, 0)}

def passageEdges : Finset (Plane × Plane) :=
  {((0, 0), (1, 0)), ((0, 0), (0, 1)), ((-1, 0), (0, 0))}

theorem mem_active_iff (π : PatternData) (x : Plane) :
    x ∈ π.active ↔ π.statusAt x ≠ .X := by
  simp only [PatternData.active, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    by_contra hx
    exact h (by simp [PatternData.statusAt, hx])

theorem passage_sites_geometry (x : Plane) (hx : x ∈ passageSites) :
    x ∈ templateSites \ templateTips ∧ Adjacent (0, 0) x ∧ x ≠ (0, 0) := by
  simp only [passageSites, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;>
    norm_num [templateSites, templateTips, square, Adjacent, latticeDist]

theorem origin_not_tip : (0, 0) ∉ templateTips := by decide +kernel

theorem passage_kept (π : PatternData) (hπ : π.Covered) (x : Plane)
    (hx : x ∈ passageSites) (hs : π.statusAt x ≠ .X) :
    (0, 0) ∈ π.keptAt x := by
  rcases hπ with ⟨_, h0, hk0, _, _, _, _, _, _, hrecip⟩
  have hg := passage_sites_geometry x hx
  apply (hrecip (0, 0) (by simp [origin_mem_template, origin_not_tip])
    x hg.1 (by rw [h0]; decide) hs hg.2.1).mp
  simpa only [hk0, passageSites] using hx

theorem template_incident_edges :
    (internalBonds templateSites).filter (fun e => e.1 = (0, 0) ∨ e.2 = (0, 0)) =
      insert ((0, -1), (0, 0)) passageEdges := by
  decide +kernel

theorem passage_edge_internal (e : Plane × Plane) (he : e ∈ passageEdges) :
    e ∈ internalBonds templateSites := by
  have h : e ∈ insert ((0, -1), (0, 0)) passageEdges := Finset.mem_insert_of_mem he
  rw [← template_incident_edges] at h
  exact (Finset.mem_filter.mp h).1

theorem covered_incident_subset (π : PatternData) (hπ : π.Covered)
    (e : Plane × Plane) (he : e ∈ π.bonds) (h : e.1 = (0, 0) ∨ e.2 = (0, 0)) :
    e ∈ passageEdges := by
  obtain ⟨hi, hs1, hs2, hk1, hk2⟩ := Finset.mem_filter.mp he
  have hi' : e ∈ (internalBonds templateSites).filter
      (fun e => e.1 = (0, 0) ∨ e.2 = (0, 0)) := Finset.mem_filter.mpr ⟨hi, h⟩
  rw [template_incident_edges, Finset.mem_insert] at hi'
  rcases hi' with rfl | hi'
  · have hk0 := hπ.2.2.1
    norm_num [origin_not_tip, hk0] at hk2
  · exact hi'

theorem passage_edge_mem_iff (π : PatternData) (hπ : π.Covered)
    (e : Plane × Plane) (he : e ∈ passageEdges) :
    e ∈ π.bonds ↔ π.statusAt e.1 ≠ .X ∧ π.statusAt e.2 ≠ .X := by
  constructor
  · intro h
    exact ⟨(Finset.mem_filter.mp h).2.1, (Finset.mem_filter.mp h).2.2.1⟩
  · rintro ⟨hs1, hs2⟩
    apply Finset.mem_filter.mpr
    refine ⟨passage_edge_internal e he, hs1, hs2, ?_⟩
    have hk0 := hπ.2.2.1
    simp only [passageEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨Or.inr (by simp [hk0]), Or.inr (passage_kept π hπ _ (by simp [passageSites]) hs2)⟩
    · exact ⟨Or.inr (by simp [hk0]), Or.inr (passage_kept π hπ _ (by simp [passageSites]) hs2)⟩
    · exact ⟨Or.inr (passage_kept π hπ _ (by simp [passageSites]) hs1), Or.inr (by simp [hk0])⟩

theorem covered_incident_edges (π : PatternData) (hπ : π.Covered) :
    π.bonds.filter (fun e => e.1 = (0, 0) ∨ e.2 = (0, 0)) =
      passageEdges.filter (fun e => π.statusAt e.1 ≠ .X ∧ π.statusAt e.2 ≠ .X) := by
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, hi⟩
    exact ⟨covered_incident_subset π hπ e he hi,
      (Finset.mem_filter.mp he).2.1, (Finset.mem_filter.mp he).2.2.1⟩
  · rintro ⟨he, hs⟩
    refine ⟨(passage_edge_mem_iff π hπ e he).mpr hs, ?_⟩
    simp only [passageEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> simp

theorem external_not_origin (j : Fin 20) : (externalSlot j).1 ≠ (0, 0) := by
  fin_cases j <;> decide +kernel

end AKLT.W.H1M006
