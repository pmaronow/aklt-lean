module
public import AKLT.W.H3C056.Semantic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

open scoped BigOperators
set_option maxRecDepth 4096

namespace AKLT.W.H3C056

open AKLT.Defs AKLT.Gen.Packed AKLT.Cert.H3
attribute [local irreducible] allMask oneMask ordinaryMask knownMask deadMask pull rowTerms edgeTerms

/-- Packed row identity for the corrected zero-center-edge operator. -/
def RowTermsAgreementV2 : Prop :=
  ∀ (m q : Nat) (Q : MemoryQuotient m q)
    (plane cap : Phase → Fin q → Nat) (X : PairType) (d₀ : Compass)
    (φ : Phase) (a : Fin q),
    Q.Correct → (X,d₀) ∈ stationaryCases →
    (∀ ψ b, cap ψ b < 2^26 ∧ Fits (plane ψ b) 80 19881 ∧
      lane (plane ψ b) 80 (siteIndex kernelCentre) = 0) →
    ∀ s < 19881, gridSite s ≠ kernelCentre → gridSite s ≠ kernelTarget X →
      component 80 s (rowTerms Q plane cap X d₀ φ a) =
        ∑ d : Compass, ∑ ψ : Phase,
          coefficientCeiling (stationaryCoefficientV2 Q X d₀ φ a (gridSite s) d ψ) *
            (if (gridSite s+d.step) ∈ square (0,0) certificateRadius
             then lane (plane ψ (Q.successor a d)) 80
               (siteIndex (gridSite s+d.step))
             else cap ψ (Q.successor a d))

theorem rowTerms_v2 : RowTermsAgreementV2 := by
  classical
  unfold RowTermsAgreementV2
  intro m q Q plane cap X d₀ φ a hQ hcase hdata s hs hc ht
  rw [component_edges]
  apply Finset.sum_congr rfl
  intro d hd
  rw [edge_agreement Q plane cap X d₀ φ a d hQ (case_ne_east X d₀ hcase)
    hdata s hs hc ht]
  apply Finset.sum_congr rfl
  intro ψ hψ
  apply congrArg (fun n => coefficientCeiling
    (stationaryCoefficientV2 Q X d₀ φ a (gridSite s) d ψ) * n)
  unfold valueAt
  split_ifs <;> rfl

/-- Once the corrected row identity is available, the center-zero condition
transfers it to the legacy coefficient used by the frozen statement. -/
theorem legacy_transfer (hV2 : RowTermsAgreementV2) :
    AKLT.Cert.H3.RowTermsAgreement := by
  classical
  intro m q Q plane cap X d₀ φ a hQ hcase hdata s hs hcentre htarget
  have hV2row := hV2 m q Q plane cap X d₀ φ a hQ hcase hdata s hs hcentre htarget
  have hsum :
      (∑ d : Compass, ∑ ψ : Phase,
        coefficientCeiling (stationaryCoefficientV2 Q X d₀ φ a (gridSite s) d ψ) *
          (if (gridSite s+d.step) ∈ square (0,0) certificateRadius then
            lane (plane ψ (Q.successor a d)) 80 (siteIndex (gridSite s+d.step))
          else cap ψ (Q.successor a d))) =
      (∑ d : Compass, ∑ ψ : Phase,
        coefficientCeiling (stationaryCoefficient Q X d₀ φ a (gridSite s) d ψ) *
          (if (gridSite s+d.step) ∈ square (0,0) certificateRadius then
            lane (plane ψ (Q.successor a d)) 80 (siteIndex (gridSite s+d.step))
          else cap ψ (Q.successor a d))) := by
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro ψ hψ
    by_cases hdest : gridSite s + d.step = kernelCentre
    · have hbox : gridSite s + d.step ∈ square (0,0) certificateRadius := by
        rw [hdest]
        simp [square, kernelCentre, certificateRadius]
      have hvalue :
          (if (gridSite s+d.step) ∈ square (0,0) certificateRadius then
            lane (plane ψ (Q.successor a d)) 80 (siteIndex (gridSite s+d.step))
          else cap ψ (Q.successor a d)) = 0 := by
        rw [ite_eq_left hbox, hdest]
        exact (hdata ψ (Q.successor a d)).2.2
      rw [hvalue]
      simp
    · have hcoef :
          stationaryCoefficientV2 Q X d₀ φ a (gridSite s) d ψ =
            stationaryCoefficient Q X d₀ φ a (gridSite s) d ψ := by
        simp [stationaryCoefficientV2, stationaryCoefficient, hdest]
      rw [hcoef]
  exact hV2row.trans hsum

/-- The closed frozen row-agreement leaf. -/
theorem main : AKLT.Cert.H3.RowTermsAgreement := legacy_transfer rowTerms_v2

#print axioms rowTerms_v2
#print axioms legacy_transfer
#print axioms main

end AKLT.W.H3C056
