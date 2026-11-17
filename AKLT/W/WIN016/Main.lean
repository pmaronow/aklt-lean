module
public import AKLT.Blueprint.Win.NodesTopology

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN016

theorem main : AKLT.Blueprint.Win.TailSupportStatement := by
  intro c R hR hbox hflux
  classical
  let P : Finset Plane :=
    (Finset.Icc (-R) R).product (Finset.Icc (-R) R)
  refine ⟨P, ?_⟩
  intro p hp
  have hout : p.1 ∉ Finset.Icc (-R) R ∨ p.2 ∉ Finset.Icc (-R) R := by
    by_contra h
    push Not at h
    apply hp
    simp [P, h]
  rcases hout with hi | hj
  · have hzero : ∀ r : ℤ, horizontal c p.1 r = 0 := by
      intro r
      by_contra hne
      have hs : s((p.1, r), (p.1 + 1, r)) ∈ c.support :=
        Finsupp.mem_support_iff.mpr hne
      have hpt : (p.1, r) ∈ s((p.1, r), (p.1 + 1, r)) := by
        rw [Sym2.mem_iff]
        exact Or.inl rfl
      have hb := hbox _ hs _ hpt
      have hmem : p.1 ∈ Finset.Icc (-R) R :=
        Finset.mem_Icc.mpr (abs_le.mp hb.1)
      exact hi hmem
    unfold tailCoefficient
    apply Finset.sum_eq_zero
    intro r hr
    simp [hzero r]
  · have hnot : ¬ (-R ≤ p.2 ∧ p.2 ≤ R) := by
      simpa [Finset.mem_Icc] using hj
    have hsplit : p.2 < -R ∨ R < p.2 := by
      by_contra h
      push Not at h
      exact hnot h
    rcases hsplit with hbelow | habove
    · have hlt : ∀ r ∈ Finset.Icc (-R) R, p.2 < r := by
        intro r hr
        have hr' := Finset.mem_Icc.mp hr
        omega
      unfold tailCoefficient
      calc
        (∑ r ∈ Finset.Icc (-R) R,
            if p.2 < r then horizontal c p.1 r else 0) =
            ∑ r ∈ Finset.Icc (-R) R, horizontal c p.1 r := by
              apply Finset.sum_congr rfl
              intro r hr
              simp [hlt r hr]
        _ = 0 := hflux p.1
    · have habove' : R < p.2 := habove
      unfold tailCoefficient
      apply Finset.sum_eq_zero
      intro r hr
      have hr' := Finset.mem_Icc.mp hr
      have hfalse : ¬ p.2 < r := by omega
      simp [hfalse]

#print axioms main

end AKLT.W.WIN016
