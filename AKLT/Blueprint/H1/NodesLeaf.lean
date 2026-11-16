import AKLT.Blueprint.H1.NodesPassage

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.Blueprint.H1

/-- `l:leaf`, lines 108–149; enumerate the 20 slots at a peripheral site.
Tips have exactly three fields and status U. A nonremoved corner has exactly
two fields and status U or D. The radius is matched in Q before coercion. -/
def CoveredSlotEnumerationStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ m : Fin 20 → UnitVector,
    ∀ x ∈ templateCorners ∪ templateTips, π.statusAt x ≠ .X →
    (∃ a : Fin 3 → UnitVector, π.statusAt x = .U ∧ replacementRadius π x = 3 / 5 ∧
      coveredSiteField m x = localProduct (fun j => (a j).val)) ∨
    (∃ a : Fin 2 → UnitVector, (π.statusAt x = .U ∨ π.statusAt x = .D) ∧
      replacementRadius π x = (if π.statusAt x = .U then 1 / 2 else 1 / 3) ∧
      coveredSiteField m x = localProduct (fun j => (a j).val))

/-- `l:leaf`, lines 136–159; expand the two-slot U/D normalizer and vector mean.
Use t = a.b in [-1,1], |a+b|² = 2+2t, and the displayed square factorizations.
The positivity clause explicitly protects the denominator in `localMean`. -/
def CornerMeanBoundsStatement : Prop :=
  MonomialMoments → ∀ a : Fin 2 → UnitVector, ∀ s : Status, s = .U ∨ s = .D →
    0 < siteFunctional s (localProduct (fun j => (a j).val)) ∧
    normSq (localMean s (fun j => (a j).val)) ≤
      (if s = .U then (1 / 2 : ℝ) else 1 / 3) ^ 2

/-- `l:leaf`, lines 122–132 and 156–162; finite-sum linearity gives A+V.v.
Scale the normalized mean by a positive radius. This lemma needs neither a
nonzero mean nor a nonzero neighbour vector, and handles an empty field list. -/
def NormalizedMeanFactorStatement : Prop :=
  ∀ k : ℕ, ∀ a : Fin k → Vec3, ∀ s : Status, ∀ ρ : ℝ, 0 < ρ →
    0 < siteFunctional s (localProduct a) → normSq (localMean s a) ≤ ρ ^ 2 →
    ∃ A : ℝ, 0 < A ∧ ∃ u : Vec3, normSq u ≤ 1 ∧
      ∀ v : Vec3, normSq v ≤ 1 →
        siteFunctional s (fun n => localProduct a n * (1 + dot n v)) = A * (1 + ρ * dot u v)

end AKLT.Blueprint.H1
