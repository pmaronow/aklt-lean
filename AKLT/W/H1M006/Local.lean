module
public import AKLT.W.H1M006.Bonds
public import AKLT.W.H1M006.Split

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M006

def complementWeight (π : PatternData) (m : Fin 20 → UnitVector)
    (n : passageComplement π → SpinLetter) : ℝ :=
  (∏ x : passageComplement π, spinWeight (π.statusAt x.val) (n x)) *
    remainingBondProduct π (supportSpins (passageComplement π) n) *
    slotProduct π m (supportSpins (passageComplement π) n)

theorem erasedSummand_eq (π : PatternData) (m : Fin 20 → UnitVector)
    (F : (Plane → Vec3) → ℝ) (n : passageComplement π → SpinLetter) :
    erasedSummand π m F n =
      complementWeight π m n * F (supportSpins (passageComplement π) n) := by
  unfold erasedSummand complementWeight remainingBondProduct slotProduct
  ring

theorem spins_removed (π : PatternData) (n : π.active → SpinLetter)
    (x : Plane) (hx : π.statusAt x = .X) : π.spins n x = 0 := by
  have ha : x ∉ π.active := by simp [PatternData.active, hx]
  simp [PatternData.spins, ha]

theorem split_remaining_bonds (π : PatternData) (h0 : (0, 0) ∈ π.active)
    (n : passageComplement π → SpinLetter) (p : SpinLetter) :
    remainingBondProduct π (π.spins (splitAssignments π h0 (n, p))) =
      remainingBondProduct π (supportSpins (passageComplement π) n) := by
  unfold remainingBondProduct
  apply Finset.prod_congr rfl
  intro e _
  by_cases hi : e.1 = (0, 0) ∨ e.2 = (0, 0)
  · simp only [hi, ↓reduceIte]
  · simp only [↓reduceIte, split_spins, (not_or.mp hi).1, (not_or.mp hi).2]

theorem split_slots (π : PatternData) (h0 : (0, 0) ∈ π.active)
    (m : Fin 20 → UnitVector) (n : passageComplement π → SpinLetter) (p : SpinLetter) :
    slotProduct π m (π.spins (splitAssignments π h0 (n, p))) =
      slotProduct π m (supportSpins (passageComplement π) n) := by
  unfold slotProduct
  apply Finset.prod_congr rfl
  intro j _
  simp only [split_spins, external_not_origin, ↓reduceIte]

theorem neighbors_not_origin (π : PatternData) (f g : Plane)
    (hn : PassageNeighbors π f g) :
    f ≠ (0, 0) ∧ g ≠ (0, 0) ∧ π.outgoing.step ≠ (0, 0) := by
  have hs : passageSites = {π.outgoing.step, f, g} := hn.1.symm
  exact ⟨(passage_sites_geometry f (by simp [hs])).2.2,
    (passage_sites_geometry g (by simp [hs])).2.2,
    (passage_sites_geometry π.outgoing.step (by simp [hs])).2.2⟩

theorem originalSummand_factorized (π : PatternData) (hπ : π.Covered)
    (next : Bool) (m : Fin 20 → UnitVector) (f g : Plane) (hn : PassageNeighbors π f g)
    (n : passageComplement π → SpinLetter) (p : SpinLetter) :
    originalSummand π next m (splitAssignments π (origin_active π hπ) (n, p)) =
      complementWeight π m n * (spinWeight (if next then .D else .U) p *
        localPassageFactor next (spinVector p)
          (supportSpins (passageComplement π) n f)
          (supportSpins (passageComplement π) n g)
          (supportSpins (passageComplement π) n π.outgoing.step)) := by
  change (_ * bondProduct π next (π.spins _) * slotProduct π m (π.spins _)) = _
  rw [split_weights π hπ next n p, factor_bonds π hπ next _ (spins_removed π _) f g hn,
    split_remaining_bonds, split_slots]
  have hn0 := neighbors_not_origin π f g hn
  simp only [split_spins, ↓reduceIte, hn0.1, hn0.2.1, hn0.2.2]
  unfold complementWeight
  ring

theorem local_fubini
    (hSite : ∀ a b o : Vec3,
      siteFunctional .U (fun z => (1 + dot z a) * (1 + dot z b) * (1 + dot z o)) =
        1 + (dot a b + dot a o + dot b o) / 3 ∧
      siteFunctional .D (fun z => (1 + dot z a) * (1 + dot z b)) = 1 + dot a b / 5)
    (π : PatternData) (hπ : π.Covered) (m : Fin 20 → UnitVector)
    (f g : Plane) (hn : PassageNeighbors π f g) (n : passageComplement π → SpinLetter) :
    (∑ p : SpinLetter,
      originalSummand π false m (splitAssignments π (origin_active π hπ) (n, p))) =
        erasedSummand π m (passageI π.outgoing.step f g) n ∧
    (∑ p : SpinLetter,
      originalSummand π true m (splitAssignments π (origin_active π hπ) (n, p))) =
        erasedSummand π m (passageJ f g) n := by
  let v := supportSpins (passageComplement π) n
  have hU : (∑ p : SpinLetter, spinWeight .U p *
      localPassageFactor false (spinVector p) (v f) (v g) (v π.outgoing.step)) =
      passageI π.outgoing.step f g v := by
    simpa [siteFunctional, localPassageFactor, passageI] using
      (hSite (v f) (v g) (v π.outgoing.step)).1
  have hD : (∑ p : SpinLetter, spinWeight .D p *
      localPassageFactor true (spinVector p) (v f) (v g) (v π.outgoing.step)) =
      passageJ f g v := by
    simpa [siteFunctional, localPassageFactor, passageJ] using
      (hSite (v f) (v g) (v π.outgoing.step)).2
  constructor
  · simp_rw [originalSummand_factorized π hπ false m f g hn n]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← Finset.mul_sum, show supportSpins (passageComplement π) n = v from rfl,
      hU, erasedSummand_eq]
  · simp_rw [originalSummand_factorized π hπ true m f g hn n]
    simp only [↓reduceIte]
    rw [← Finset.mul_sum, show supportSpins (passageComplement π) n = v from rfl,
      hD, erasedSummand_eq]

end AKLT.W.H1M006
