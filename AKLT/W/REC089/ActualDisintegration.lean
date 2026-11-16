import AKLT.W.REC089.ActualFactorization

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

attribute [local instance] Classical.propDecidable

/-- The actual conditioned network, with its original pins and actual tip bonds,
is the reduced local template times a common nonnegative exterior factor. -/
theorem actual_fibre_reduced (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = .U)
    (incoming outgoing : Compass) (ho : a.o = a.y + outgoing.step)
    (π : PatternData) (hm : Matches a incoming outgoing π) (ω : ExteriorSpins a incoming)
    (next : Bool) :
    actualFibre a incoming ω next = exteriorFactor a incoming ω *
      actualReduced π (actualTipStatus a incoming) (actualTipBond a incoming)
        (cornerFields a incoming ω) (tipFields a incoming ω) next := by
  let e := interiorSiteEquiv a incoming outgoing π hm
  let w := fun (x : InteriorSite a incoming) (d : SpinLetter) =>
    spinWeight (commonStatus a next x.val.val) d
  let K := patternCoreFactors π next (cornerFields a incoming ω)
  let L := actualTipFactor a incoming π (tipFields a incoming ω)
  have hf := sum_eliminate_leaves e w K L
  have he : actualFibre a incoming ω next = exteriorFactor a incoming ω *
      ∑ η : InteriorSpins a incoming, (∏ x, w x (η x)) *
        K (fun c => η (e.symm (.inl c))) *
        ∏ t, L (fun c => η (e.symm (.inl c))) t (η (e.symm (.inr t))) := by
    unfold actualFibre
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    rw [actual_factors_separate a hU incoming outgoing ho π hm]
    change (∏ x, w x (η x)) * (exteriorFactor a incoming ω *
      K (fun c => η (e.symm (.inl c))) *
      ∏ t, L (fun c => η (e.symm (.inl c))) t (η (e.symm (.inr t)))) = _
    ring
  rw [he, hf]
  congr 1
  unfold actualReduced
  apply Finset.sum_congr rfl
  intro σ _
  have hc : (∏ c : coreSites π, w (e.symm (.inl c)) (σ c)) =
      ∏ c : coreSites π, spinWeight
        (if next ∧ c.val = (0, 0) then .D else π.statusAt c.val) (σ c) := by
    apply Finset.prod_congr rfl
    intro c _
    exact congrArg (fun s => spinWeight s (σ c)) (core_commonStatus a hU incoming outgoing π hm next c)
  have ht (t : ActiveTips a incoming) :
      (∑ d : SpinLetter, w (e.symm (.inr t)) d * L σ t d) =
        tipValue (actualTipStatus a incoming t.val) (actualTipBond a incoming t.val)
          (tipFields a incoming ω t.val) (supportSpins (coreSites π) σ (tipNeighbour t.val)) := by
    unfold tipValue
    rw [ite_eq_right t.property]
    unfold siteFunctional
    apply Finset.sum_congr rfl
    intro d _
    change spinWeight (commonStatus a next (tipInterior a incoming t).val.val) d * _ = _
    rw [tip_commonStatus a incoming next t]
    rfl
  rw [hc]
  simp_rw [ht]
  rw [← prod_activeTips a incoming
    (fun t => tipValue (actualTipStatus a incoming t) (actualTipBond a incoming t)
      (tipFields a incoming ω t) (supportSpins (coreSites π) σ (tipNeighbour t)))
    (fun t hx => by simp [tipValue, hx])]
  dsimp [K, patternCoreFactors, coreKernel, templateBondTerm]
  ring

theorem actual_fibre_factorization :
    ∀ a : AKLT.Blueprint.Rec.Departure, a.D.status a.y = .U →
      ∀ incoming outgoing : Compass, a.o = a.y + outgoing.step →
      ∀ π : PatternData, Matches a incoming outgoing π →
      ∀ ω : ExteriorSpins a incoming,
      ∃ c : Fin 8 → Vec3, ∃ b : Fin 4 → Fin 3 → Vec3, ∃ C : ℝ,
        0 ≤ C ∧ (∀ j, normSq (c j) ≤ 1) ∧ (∀ t j, normSq (b t j) ≤ 1) ∧
        ∀ next : Bool, actualFibre a incoming ω next =
          C * actualReduced π (actualTipStatus a incoming) (actualTipBond a incoming) c b next := by
  intro a hU incoming outgoing ho π hm ω
  exact ⟨cornerFields a incoming ω, tipFields a incoming ω, exteriorFactor a incoming ω,
    exteriorFactor_nonneg a incoming ω,
    (fun j => slotField_ball a incoming ω (cornerIndex j)),
    (fun t j => slotField_ball a incoming ω (tipIndex t j)),
    actual_fibre_reduced a hU incoming outgoing ho π hm ω⟩

#print axioms actual_fibre_reduced
#print axioms actual_fibre_factorization

end AKLT.W.REC089
