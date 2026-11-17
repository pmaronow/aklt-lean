module
public import AKLT.Blueprint.H1.NodesSector

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder

namespace AKLT.W.H1M034

theorem main : AKLT.Blueprint.H1.SpanWeightLatticeStatement := by
  classical
  intro J β _ v w κ hEigen hLattice ψ hψ hψne m hψeig
  let T : Module.End ℂ (AKLT.Blueprint.H1.TensorSpace J) :=
    AKLT.Defs.totalSpinZ J
  let W : Set ℂ := Set.range fun b : β => (w b : ℂ)
  let S : Submodule ℂ (AKLT.Blueprint.H1.TensorSpace J) :=
    ⨆ a ∈ W, T.eigenspace a
  have hspan : Submodule.span ℂ (Set.range v) ≤ S := by
    apply Submodule.span_le.2
    rintro x ⟨b, rfl⟩
    have hv : v b ∈ T.eigenspace (w b : ℂ) := by
      rw [Module.End.eigenspace_def]
      change T (v b) - (w b : ℂ) • v b = 0
      change AKLT.Defs.totalSpinZ J (v b) - (w b : ℂ) • v b = 0
      rw [hEigen b]
      simp
    have hw : (w b : ℂ) ∈ W := ⟨b, rfl⟩
    exact Submodule.mem_iSup_of_mem (w b : ℂ)
      (Submodule.mem_iSup_of_mem hw hv)
  have hψS : ψ ∈ S := hspan hψ
  have hψE : ψ ∈ T.eigenspace (m : ℂ) := by
    rw [Module.End.eigenspace_def]
    change T ψ - (m : ℂ) • ψ = 0
    change AKLT.Defs.totalSpinZ J ψ - (m : ℂ) • ψ = 0
    rw [hψeig]
    simp
  by_cases hmW : (m : ℂ) ∈ W
  · obtain ⟨b, hb⟩ := hmW
    have hm' : w b = m := by simpa using congrArg Complex.re hb
    have hm : m = w b := hm'.symm
    obtain ⟨z, hz⟩ := hLattice b
    exact ⟨z, hm.trans hz⟩
  · have hdis : Disjoint (T.eigenspace (m : ℂ)) S := by
      simpa only [S] using
        (T.eigenspaces_iSupIndep.disjoint_biSup (x := (m : ℂ)) (y := W) hmW)
    have hzero : ψ = 0 := (Submodule.disjoint_def.mp hdis) ψ hψE hψS
    exact (hψne hzero).elim

end AKLT.W.H1M034

#print axioms AKLT.W.H1M034.main
