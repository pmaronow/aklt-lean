module
public import AKLT.Blueprint.Gap.NodesPeriodic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap

namespace AKLT.W.GAP033

private theorem adjacent_reductions_are_bond {L N : Size} (x y : Plane)
    (hxy : Adjacent x y) :
    ∃ d : Direction,
      reduction L N y = nextSite (reduction L N x) d ∨
        reduction L N x = nextSite (reduction L N y) d := by
  have hdist : (x.1 - y.1).natAbs + (x.2 - y.2).natAbs = 1 := hxy
  rcases Nat.add_eq_one_iff.mp hdist with ⟨hx0, hy1⟩ | ⟨hx1, hy0⟩
  · have hx : x.1 - y.1 = 0 := by
      rcases Int.natAbs_eq_iff.mp hx0 with h | h <;> simpa using h
    have hxEq : x.1 = y.1 := by omega
    rcases Int.natAbs_eq_iff.mp hy1 with hy | hy
    · have hy' : x.2 = y.2 + 1 := by omega
      refine ⟨1, Or.inr ?_⟩
      ext <;> simp [reduction, nextSite, hxEq, hy']
    · have hy' : y.2 = x.2 + 1 := by omega
      refine ⟨1, Or.inl ?_⟩
      ext <;> simp [reduction, nextSite, hxEq, hy']
  · have hy : x.2 - y.2 = 0 := by
      rcases Int.natAbs_eq_iff.mp hy0 with h | h <;> simpa using h
    have hyEq : x.2 = y.2 := by omega
    rcases Int.natAbs_eq_iff.mp hx1 with hx | hx
    · have hx' : x.1 = y.1 + 1 := by omega
      refine ⟨0, Or.inr ?_⟩
      ext <;> simp [reduction, nextSite, hx', hyEq]
    · have hx' : y.1 = x.1 + 1 := by omega
      refine ⟨0, Or.inl ?_⟩
      ext <;> simp [reduction, nextSite, hx', hyEq]

theorem main : AKLT.Blueprint.Gap.PullbackColorStatement := by
  intro L N κ hκ x y hxy
  obtain ⟨d, hbond | hreverse⟩ := adjacent_reductions_are_bond (L := L) (N := N) x y hxy
  · have hcol := hκ (reduction L N x, d)
    simpa [Function.comp, hbond] using hcol
  · have hcol := hκ (reduction L N y, d)
    simpa [Function.comp, hreverse] using hcol.symm

end AKLT.W.GAP033

#print axioms AKLT.W.GAP033.main
