import AKLT.Blueprint.Rec.NodesClosure

noncomputable section
open AKLT.Defs

namespace AKLT.W.REC049

open AKLT.Blueprint.Rec

private theorem normalizeStart_kept_mem_iff {G : Finset Plane} (D : Network G)
    (u c x y : Plane) (hc : D.status c = .X) (hy : y ∈ D.active) :
    y ∈ (normalizeStart D u c).kept x ↔ y ∈ D.kept x := by
  classical
  have hyc : y ≠ c := by
    intro h
    subst y
    exact (Finset.mem_filter.mp hy).2 hc
  unfold normalizeStart
  by_cases h : x = u ∧ D.status u = .U
  · simp [h, Finset.mem_erase, hyc]
  · simp [h]

private theorem normalizeStart_present_iff {G : Finset Plane} (D : Network G)
    (u c x y : Plane) (hc : D.status c = .X) :
    (normalizeStart D u c).Present x y ↔ D.Present x y := by
  classical
  constructor
  · intro h
    rcases h with ⟨hx, hy, hadj, hyk, hxk⟩
    refine ⟨?_, ?_, hadj, ?_, ?_⟩
    · exact hx
    · exact hy
    · exact (normalizeStart_kept_mem_iff D u c x y hc (by exact hy)).mp hyk
    · exact (normalizeStart_kept_mem_iff D u c y x hc (by exact hx)).mp hxk
  · intro h
    rcases h with ⟨hx, hy, hadj, hyk, hxk⟩
    refine ⟨?_, ?_, hadj, ?_, ?_⟩
    · exact hx
    · exact hy
    · exact (normalizeStart_kept_mem_iff D u c x y hc hy).mpr hyk
    · exact (normalizeStart_kept_mem_iff D u c y x hc hx).mpr hxk

private theorem normalizeStart_bonds_eq {G : Finset Plane} (D : Network G)
    (u c : Plane) (hc : D.status c = .X) :
    (normalizeStart D u c).bonds = D.bonds := by
  classical
  apply Finset.ext
  intro e
  simp only [Network.bonds, Finset.mem_filter]
  rw [normalizeStart_present_iff D u c e.1 e.2 hc]

theorem main : AKLT.Blueprint.Rec.NormalizeStartStatement := by
  intro p
  rcases p.pair with ⟨_, _, _, _, hc, _, _, _, _⟩
  constructor
  · change (normalizeStart p.D p.u p.c).bonds = p.D.bonds
    exact normalizeStart_bonds_eq p.D p.u p.c hc
  · intro b f
    change (normalizeStart p.D p.u p.c).partition p.τ b f = p.D.partition p.τ b f
    unfold Network.partition
    rw [normalizeStart_bonds_eq p.D p.u p.c hc]
    rfl

end AKLT.W.REC049
