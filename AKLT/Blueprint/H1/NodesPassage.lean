module
public import AKLT.Blueprint.H1.Definitions

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.Blueprint.H1

/-- `l:Iw`, lines 57–63; expand three linear factors using degree ≤ 3 moments.
No unit or nonzero assumption is needed on the three neighbor vectors. -/
def PassageSiteMomentsStatement : Prop :=
  MonomialMoments → ∀ a b o : Vec3,
    siteFunctional .U (fun n => (1 + dot n a) * (1 + dot n b) * (1 + dot n o)) =
      1 + (dot a b + dot a o + dot b o) / 3 ∧
    siteFunctional .D (fun n => (1 + dot n a) * (1 + dot n b)) = 1 + dot a b / 5

/-- `l:Iw`, lines 42–65; split the finite spin assignment at the passage site.
Coveredness supplies exactly the present nonremoved passage bonds; the supplied
one-site identities include zero vectors for removed neighbors. -/
def PassageFubiniStatement : Prop :=
  (∀ a b o : Vec3,
    siteFunctional .U (fun n => (1 + dot n a) * (1 + dot n b) * (1 + dot n o)) =
      1 + (dot a b + dot a o + dot b o) / 3 ∧
    siteFunctional .D (fun n => (1 + dot n a) * (1 + dot n b)) = 1 + dot a b / 5) →
  ∀ π : PatternData, π.Covered → ∀ m : Fin 20 → UnitVector, ∀ f g : Plane,
    PassageNeighbors π f g →
    patternCurrent π m = withoutPassageFunctional π m (passageI π.outgoing.step f g) ∧
    patternNext π m = withoutPassageFunctional π m (passageJ f g)

/-- `l:Iw`, lines 67–76; enumerate the erased template as a valid finite network
with all twenty slot factors, then apply finite-network positivity. -/
def PassageNetworkPositiveStatement : Prop :=
  (∀ n : ℕ, ∀ D : FiniteSpinNetwork n, D.Valid → 0 < D.partition true (fun _ => 1)) →
  ∀ π : PatternData, π.Covered → ∀ m : Fin 20 → UnitVector,
    0 < withoutPassageFunctional π m (fun _ => 1)

/-- `l:Iw`, lines 69–76; every nonzero-weight spin is in the ball and all bond
and slot factors are nonnegative. Bound J pointwise by 4/5 before summing. -/
def PassageNextLowerBoundStatement : Prop :=
  (∀ j : IcoLetter, normSq (icoVector j) = 1) →
  ∀ π : PatternData, π.Covered → ∀ m : Fin 20 → UnitVector, ∀ f g : Plane,
    (4 / 5 : ℝ) * withoutPassageFunctional π m (fun _ => 1) ≤
      withoutPassageFunctional π m (passageJ f g)

/-- `l:Iw`, lines 64–65; the finite weighted functional is real linear. -/
def PassageSubtractionStatement : Prop :=
  ∀ π : PatternData, ∀ m : Fin 20 → UnitVector, ∀ F G : (Plane → Vec3) → ℝ, ∀ c : ℝ,
    withoutPassageFunctional π m F - c * withoutPassageFunctional π m G =
      withoutPassageFunctional π m (fun n => F n - c * G n)

theorem passageSubtraction : PassageSubtractionStatement := by
  intro π m F G c
  unfold withoutPassageFunctional
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- `l:Iw`, lines 78–92; each active spin in the original current/next integrand
has degree at most four, and no monomial uses an omitted spin. -/
def OriginalDegreeStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ next : Bool,
    InternalAdmissible π.active (originalIntegrand π next)

/-- `l:Iw`, lines 78–92; each external slot occurs once and simultaneous rotation
preserves every formal dot product, for arbitrary spin/vector values. -/
def OriginalFactorStructureStatement : Prop :=
  ∀ π : PatternData, ∀ next : Bool,
    LocalVectorAffine (originalIntegrand π next) ∧ IntegrandInvariant (originalIntegrand π next)

/-- `l:Iw`, lines 63–65; polynomial evaluation commutes with the finite products
in the original integrand. The spin coordinates coincide on the active set. -/
def OriginalRawEvaluationStatement : Prop :=
  ∀ π : PatternData, ∀ next : Bool, ∀ m : Fin 20 → UnitVector,
    rawFunctional π.active (nextStatus π next) (originalIntegrand π next) (fun j => (m j).val) =
      if next then patternNext π m else patternCurrent π m

/-- `l:moments` used in `l:Iw`/`c:reduce`, lines 83–92 and 206–214.
Expand monomials; finite-product summation factors into local exact moments.
The support premise prevents silently discarding an internal variable. -/
def MomentContractionStatement : Prop :=
  MonomialMoments → ∀ V : Finset Plane, ∀ s : Plane → Status,
    (∀ x ∈ V, s x = .U ∨ s x = .D) → ∀ p : LocalPolynomial,
    InternalAdmissible V p → ∀ u : Fin 20 → Vec3,
      evaluateReduced (contractSpins V s p) u = rawFunctional V s p u

/-- `l:moments` used in `l:Iw`/`c:reduce`, lines 83–92 and 206–214.
Reindex the finite support by Fin |V|; use separate-degree-four covariance and
integrand invariance. Only polynomial covariance, never atom-law invariance. -/
def MomentCovarianceTransferStatement : Prop :=
  MonomialMoments → ProductMomentCovariance → ∀ V : Finset Plane, ∀ s : Plane → Status,
    (∀ x ∈ V, s x = .U ∨ s x = .D) → ∀ p : LocalPolynomial,
    InternalAdmissible V p → IntegrandInvariant p → OrthogonalInvariant (contractSpins V s p)

/-- `l:Iw`/`c:reduce`, lines 78–80 and 198–201; contraction only deletes internal
exponents and adds terms, so cannot increase a vector's total degree. -/
def ContractionAffineStatement : Prop :=
  ∀ V : Finset Plane, ∀ s : Plane → Status, ∀ p : LocalPolynomial,
    LocalVectorAffine p → VectorAffine (contractSpins V s p)

/-- `d:Pauli`/`l:inversion`, lines 249–270; the same support argument shows that
contraction never creates an external vector token. -/
def ContractionSupportStatement : Prop :=
  ∀ V : Finset Plane, ∀ s : Plane → Status, ∀ p : LocalPolynomial,
    ∀ J : Finset (Fin 20), LocalSupportedVectors J p → SupportedVectors J (contractSpins V s p)

/-- Active current/next laws are U or D. This is valid without coveredness. -/
def ActiveStatusesStatement : Prop :=
  ∀ π : PatternData, ∀ next : Bool, ∀ x ∈ π.active, nextStatus π next x = .U ∨ nextStatus π next x = .D

theorem activeStatuses : ActiveStatusesStatement := by
  intro π next x hx
  have hne : π.statusAt x ≠ .X := (Finset.mem_filter.mp hx).2
  unfold nextStatus
  split
  · exact Or.inr rfl
  · cases h : π.statusAt x <;> simp_all

end AKLT.Blueprint.H1
