module
public import CertData.H3.Bridge.LegacyTargets

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

namespace AKLT.W.H3C055

open AKLT.Defs

private theorem stationaryCoefficient_offCentre {m q : ℕ}
    (Q : MemoryQuotient m q) (X : PairType) (d₀ : Compass)
    (φ : Phase) (a : Fin q) (x : Plane) (d : Compass) (ψ : Phase)
    (hdest : x + d.step ≠ kernelCentre) :
    stationaryCoefficientV2 Q X d₀ φ a x d ψ =
      stationaryCoefficient Q X d₀ φ a x d ψ := by
  simp [stationaryCoefficientV2, stationaryCoefficient, hdest]

private theorem stationaryRow_eq {m q : ℕ}
    (Q : MemoryQuotient m q) (C : StationaryData q) (X : PairType) (d₀ : Compass)
    (hzero : ∀ φ a, C.extended φ a kernelCentre = 0)
    (φ : Phase) (a : Fin q) (x : Plane) :
    (∑ d : Compass, ∑ ψ : Phase,
      coefficientCeiling (stationaryCoefficient Q X d₀ φ a x d ψ) *
        C.extended ψ (Q.successor a d) (x + d.step)) =
    (∑ d : Compass, ∑ ψ : Phase,
      coefficientCeiling (stationaryCoefficientV2 Q X d₀ φ a x d ψ) *
        C.extended ψ (Q.successor a d) (x + d.step)) := by
  classical
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro ψ _
  by_cases hdest : x + d.step = kernelCentre
  · simp [stationaryCoefficient, stationaryCoefficientV2, hdest,
      hzero ψ (Q.successor a d)]
  · rw [stationaryCoefficient_offCentre Q X d₀ φ a x d ψ hdest]

/-- The legacy and corrected stationary predicates impose the same local rows
once their shared checked center value is zero. -/
private theorem passes_iff_passesV2 {m q : ℕ}
    (Q : MemoryQuotient m q) (C : StationaryData q) (X : PairType) (d₀ : Compass) :
    C.Passes Q X d₀ ↔ C.PassesV2 Q X d₀ := by
  constructor
  · intro h
    rcases h with ⟨hcap, hterminalCap, hfree, hbound, hterminal, hrows⟩
    refine ⟨hcap, hterminalCap, hfree, hbound, hterminal, ?_⟩
    intro φ a x hxCentre hxTarget
    simpa only [stationaryRow_eq Q C X d₀ (fun φ a => (hterminal φ a).1) φ a x]
      using hrows φ a x hxCentre hxTarget
  · intro h
    rcases h with ⟨hcap, hterminalCap, hfree, hbound, hterminal, hrows⟩
    refine ⟨hcap, hterminalCap, hfree, hbound, hterminal, ?_⟩
    intro φ a x hxCentre hxTarget
    rw [stationaryRow_eq Q C X d₀ (fun φ a => (hterminal φ a).1) φ a x]
    exact hrows φ a x hxCentre hxTarget

/-- The requested closed equivalence leaf for the retained H3 certificate. -/
theorem main : CertData.H3.Bridge.PassesEquivalenceLeaf := by
  intro Q C X d₀
  exact passes_iff_passesV2 Q C X d₀

#print axioms main

end AKLT.W.H3C055
