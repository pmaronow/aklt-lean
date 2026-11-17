module
public import AKLT.W.H3C026.Routing
public import AKLT.W.H3C024.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Gen.Packed

namespace AKLT.W.H3C026

theorem rowTermsV2_from_leaves
    (hordinary : CertData.H3.Bridge.OrdinaryMaskLeaf)
    (hknown : CertData.H3.Bridge.KnownMaskLeaf)
    (hdead : CertData.H3.Bridge.DeadMaskLeaf)
    (hpull : CertData.H3.Bridge.PullLeaf) : CertData.H3.Bridge.RowTermsV2Leaf := by
  intro G T X d₀ hQ hT hcase φ a s hs hc ht
  calc
    component 80 s (rowTerms G.quotient T.planeFn T.capFn X d₀ φ a) =
        ∑ d : Compass, ∑ ψ : Phase,
          coefficientCeiling (stationaryCoefficient G.quotient X d₀ φ a (gridSite s) d ψ) *
            T.data.extended ψ (G.quotient.successor a d) (gridSite s+d.step) := by
      rw [rowTerms_directions, component_directions]
      apply Finset.sum_congr rfl
      intro d hd
      rw [routed_direction hordinary hknown hdead hpull G T X d₀ hT hcase φ a s hs hc ht d]
      apply scalarDirection_semantics G.quotient hQ X d₀ φ a (gridSite s) d hc ht
      intro hdest ψ
      rw [hdest]
      exact tables_centre T hT ψ (G.quotient.successor a d)
    _ = ∑ d : Compass, ∑ ψ : Phase,
          coefficientCeiling (stationaryCoefficientV2 G.quotient X d₀ φ a (gridSite s) d ψ) *
            T.data.extended ψ (G.quotient.successor a d) (gridSite s+d.step) :=
      AKLT.W.H3C024.main G.quotient T.data X d₀ (tables_centre T hT) φ a (gridSite s)

end AKLT.W.H3C026

#print axioms AKLT.W.H3C026.rowTermsV2_from_leaves
