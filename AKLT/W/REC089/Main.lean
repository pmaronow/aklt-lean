module
public import AKLT.W.REC089.Mixtures
public import AKLT.W.REC089.ActualDisintegration

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

/-- Finite-sum interface proved by `actual_fibre_factorization`: collect the
outside factors, eight corner directions, and each actual tip's three directions. -/
def Residual_ActualFibreFactorization : Prop :=
  ∀ a : AKLT.Blueprint.Rec.Departure, a.D.status a.y = .U →
    ∀ incoming outgoing : Compass, a.o = a.y + outgoing.step →
    ∀ π : PatternData, Matches a incoming outgoing π →
    ∀ ω : ExteriorSpins a incoming,
    ∃ c : Fin 8 → Vec3, ∃ b : Fin 4 → Fin 3 → Vec3, ∃ C : ℝ,
      0 ≤ C ∧ (∀ j, normSq (c j) ≤ 1) ∧ (∀ t j, normSq (b t j) ≤ 1) ∧
      ∀ next : Bool, actualFibre a incoming ω next =
        C * actualReduced π (actualTipStatus a incoming) (actualTipBond a incoming) c b next

/-- Finite-template interface proved by `pattern_tip_factorization`: integrate
the four U tips of a covered pattern with arbitrary ball-slot data. -/
def Residual_PatternTipFactorization : Prop :=
  ∀ π : PatternData, π.Covered → ∀ c : Fin 8 → Vec3,
    ∀ b : Fin 4 → Fin 3 → Vec3, ∀ next : Bool,
      ballPatternFunctional π next (packFields c b) = coveredReduced π c b next

theorem actual_fibre_mixture
    (hActual : Residual_ActualFibreFactorization)
    (hPattern : Residual_PatternTipFactorization)
    (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = .U)
    (incoming outgoing : Compass) (hStep : a.o = a.y + outgoing.step)
    (π : PatternData) (hm : Matches a incoming outgoing π)
    (ω : ExteriorSpins a incoming) :
    ∃ k : ℕ, ∃ ps : Fin k → PatternData, ∃ m : Fin k → Fin 20 → UnitVector,
      ∃ weight : Fin k → ℝ,
      (∀ i, 0 ≤ weight i ∧ (ps i).Covered ∧
        ((ps i).outgoing = .north ↔ outgoing = incoming)) ∧
      actualFibre a incoming ω false = ∑ i, weight i * patternCurrent (ps i) (m i) ∧
      actualFibre a incoming ω true = ∑ i, weight i * patternNext (ps i) (m i) := by
  classical
  obtain ⟨c, b, C, hC, hc, hb, he⟩ := hActual a hU incoming outgoing hStep π hm ω
  obtain ⟨fields, w, hw, hfields, htip⟩ :=
    reduced_tip_mixture π (actualTipStatus a incoming) (actualTipBond a incoming)
      (matches_tip_kept a incoming outgoing π hm) (actual_tip_live a incoming) c b hb
  have hstraight := rotation_straight incoming outgoing π.outgoing hm.2.1
  obtain ⟨F⟩ := ballPatternFamily π hm.1 incoming outgoing hstraight
    (fun η => packFields c (fields η))
    (fun η => packFields_ball c (fields η) hc (hfields η))
  have hmass : ∀ η, 0 ≤ C * w η := fun η => mul_nonneg hC (hw η)
  obtain ⟨k, ps, m, weight, hgood, hcur, hnxt⟩ :=
    flattenConditionalFamily F (fun η => C * w η) hmass
  have hboth (next : Bool) : actualFibre a incoming ω next =
      ∑ η, (C * w η) * ballPatternFunctional π next (packFields c (fields η)) := by
    rw [he next, htip next, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    rw [hPattern π hm.1]
    ring
  exact ⟨k, ps, m, weight, hgood, (hboth false).trans hcur, (hboth true).trans hnxt⟩

/-- Assemble the two finite-sum identities, tip replacements, and independent
slot resolutions. Both interface premises are discharged in `main`. -/
theorem main_of_residuals
    (hActual : Residual_ActualFibreFactorization)
    (hPattern : Residual_PatternTipFactorization) :
    AKLT.Blueprint.Rec.LocalMixtureStatementV2 := by
  classical
  intro a hU incoming outgoing hStep hCover
  obtain ⟨π, hm⟩ := matches_exists a incoming outgoing hCover
  choose k ps m w hw hc hn using
    fun ω => actual_fibre_mixture hActual hPattern a hU incoming outgoing hStep π hm ω
  let F : ConditionalFamily (ExteriorSpins a incoming)
      (fun ω => actualFibre a incoming ω false) (fun ω => actualFibre a incoming ω true)
      incoming outgoing := {
    length := k
    pattern := ps
    slot := m
    coefficient := w
    admissible := hw
    current_eq := hc
    next_eq := hn }
  obtain ⟨N, ps', m', w', hgood, hcur, hnxt⟩ :=
    flattenConditionalFamily F (exteriorMass a incoming) (exteriorMass_nonneg a incoming)
  refine ⟨N, ps', m', w', hgood, ?_, ?_⟩
  · exact (partition_disintegration a hU incoming false).trans hcur
  · exact (partition_disintegration a hU incoming true).trans hnxt

#print axioms actual_fibre_mixture
#print axioms main_of_residuals

/-- The shared internal-bond matcher gives one simultaneous nonnegative
covered-pattern mixture for the current and next partition functions. -/
theorem main : AKLT.Blueprint.Rec.LocalMixtureStatementV2 :=
  main_of_residuals actual_fibre_factorization pattern_tip_factorization

#print axioms main

end AKLT.W.REC089
