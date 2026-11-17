import AKLT.Blueprint.Mom.NodesFinite

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Mom

/-- The sum of the three pairwise field scalar products. -/
def tripleP (a : Fin 3 → Vec3) : ℝ :=
  dot (a 0) (a 1) + dot (a 0) (a 2) + dot (a 1) (a 2)

/-- Fifteen times the unnormalized U numerator of a three-factor mean. -/
def tripleV (a : Fin 3 → Vec3) : Vec3 := fun i =>
  5 * (a 0 i + a 1 i + a 2 i) +
    a 0 i * dot (a 1) (a 2) + a 1 i * dot (a 0) (a 2) +
    a 2 i * dot (a 0) (a 1)

/-- The nonnegative expression in the three-field sum-of-squares identity. -/
def tripleSOS (a : Fin 3 → Vec3) : ℝ :=
  let X := 1 - dot (a 1) (a 2)
  let Y := 1 - dot (a 0) (a 2)
  let Z := 1 - dot (a 0) (a 1)
  4 * ((X - Y)^2 + (X - Z)^2 + (Y - Z)^2) + 6 * X * Y * Z

/-- `l:35`, lines 218–222: the second tensor evaluates the scalar normalizer.
The formula is valid for arbitrary fields, so unit-vector geometry is separate. -/
def TripleNormalizerStatement : Prop :=
  ∀ a : Fin 3 → Vec3, siteFunctional .U (localProduct a) = 1 + tripleP a / 3

/-- `l:35`, lines 223–228: expand the observable together with the factors;
the second and fourth tensors give the vector numerator coordinate by coordinate. -/
def TripleNumeratorStatement : Prop :=
  ∀ a : Fin 3 → Vec3, ∀ i,
    15 * siteFunctional .U (fun v => v i * localProduct a v) = tripleV a i

/-- `l:35`, lines 221–222/229–232: nonnegativity of `|a+b+c|^2` bounds
the denominator, while Cauchy–Schwarz makes all three deficits nonnegative. -/
def TripleGeometryStatement : Prop :=
  ∀ a : Fin 3 → Vec3, (∀ j, normSq (a j) = 1) →
    1 / 2 ≤ 1 + tripleP a / 3 ∧
    0 ≤ 1 - dot (a 1) (a 2) ∧ 0 ≤ 1 - dot (a 0) (a 2) ∧
    0 ≤ 1 - dot (a 0) (a 1)

/-- `l:35`, lines 233–236: expand both sides as polynomials in coordinates,
reduce the three squared lengths to one, and use `ring`. -/
def TripleSOSIdentityStatement : Prop :=
  ∀ a : Fin 3 → Vec3, (∀ j, normSq (a j) = 1) →
    (9 + 3 * tripleP a)^2 - normSq (tripleV a) = tripleSOS a

/-- `l:35`, lines 241–247: split one ball field into opposite unit fields,
treating the zero vector separately before dividing by its length. -/
def BallFieldSplitStatement : Prop :=
  ∀ a : Vec3, normSq a ≤ 1 → ∃ t : ℝ, ∃ e : UnitVector,
    0 ≤ t ∧ t ≤ 1 ∧
    ∀ v : Vec3, 1 + dot v a =
      t * (1 + dot v e.val) + (1 - t) * (1 + dot v (-e.val))

/-- `l:35`, lines 248–253: distribute three two-term convex decompositions.
Missing factors are zero fields, and eight slots permit zero mixture weights.
This is a generic algebraic assembly step from the field-level decompositions. -/
def ProductMixtureStatement : Prop :=
  ∀ k : ℕ, k ≤ 3 → ∀ a : Fin k → Vec3,
    (∀ j, ∃ t : ℝ, ∃ e : UnitVector, 0 ≤ t ∧ t ≤ 1 ∧
      ∀ v : Vec3, 1 + dot v (a j) =
        t * (1 + dot v e.val) + (1 - t) * (1 + dot v (-e.val))) →
    ∃ t : Fin 8 → ℝ, ∃ b : Fin 8 → Fin 3 → UnitVector,
      (∀ η, 0 ≤ t η) ∧ (∑ η, t η) = 1 ∧
      ∀ v, localProduct a v =
        ∑ η, t η * localProduct (fun j => (b η j).val) v

/-- `l:35`, lines 254–258: a generic positive-mixture estimate. Normalize
with weights `t*A`, apply convexity of squared Euclidean norm, and retain the
lower bound on the denominator. Explicit `r ≥ 0` covers zero-radius balls. -/
def PositiveMixtureEstimateStatement : Prop :=
  ∀ (α : Type) [Fintype α], ∀ t A : α → ℝ, ∀ B : α → Vec3, ∀ r : ℝ,
    0 ≤ r → (∀ η, 0 ≤ t η) → (∑ η, t η) = 1 →
    (∀ η, 1 / 2 ≤ A η) →
    (∀ η, normSq (fun i => B η i / A η) ≤ r^2) →
      1 / 2 ≤ ∑ η, t η * A η ∧
      normSq (fun i => (∑ η, t η * B η i) / (∑ η, t η * A η)) ≤ r^2

/-- `l:35`, lines 260–266: `W(0)=1`, the zero atom has zero numerator,
and the D mean is a contraction of the U mean by `(3A)/(3A+2)`. -/
def DepletedContractionStatement : Prop :=
  ∀ k : ℕ, ∀ a : Fin k → Vec3, 0 < siteFunctional .U (localProduct a) →
    0 < siteFunctional .D (localProduct a) ∧
      normSq (localMean .D a) ≤ normSq (localMean .U a)

/-- The explicit path of triples in `l:35`, lines 269–273. -/
def meanPath (t : ℝ) : Fin 3 → Vec3 :=
  ![![1, 0, 0], ![Real.cos t, Real.sin t, 0], ![Real.cos t, -Real.sin t, 0]]

def meanPathEnd : ℝ := 2 * Real.pi / 3

/-- `l:35`, lines 269–273: the trigonometric path consists of unit fields. -/
def MeanPathUnitStatement : Prop :=
  ∀ t : ℝ, ∀ j, normSq (meanPath t j) = 1

theorem meanPathUnit : MeanPathUnitStatement := by
  intro t j
  fin_cases j
  · simp [meanPath, normSq, dot, Fin.sum_univ_three]
  all_goals simpa [meanPath, normSq, dot, Fin.sum_univ_three, pow_two, add_comm]
    using Real.sin_sq_add_cos_sq t

/-- `l:35`, lines 274–275: use the positive normalizer to justify continuity
of the rational mean, and hence of its squared norm, on the closed interval. -/
def MeanPathContinuityStatement : Prop :=
  ContinuousOn (fun t => normSq (localMean .U (meanPath t))) (Set.Icc 0 meanPathEnd)

/-- `l:35`, lines 276–279: evaluate the aligned triple and the zero-sum
120-degree triple. Squared norms make the subsequent IVT use scalar. -/
def MeanPathEndpointsStatement : Prop :=
  normSq (localMean .U (meanPath 0)) = (3 / 5 : ℝ)^2 ∧
    normSq (localMean .U (meanPath meanPathEnd)) = 0

/-- `l:35`, lines 280–288: the degree-three denominator and degree-four
numerator transform covariantly; no invariance of arbitrary functions is used. -/
def MeanCovarianceStatement : Prop :=
  ∀ a : Fin 3 → Vec3, (∀ j, normSq (a j) = 1) →
    ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 →
      localMean .U (fun j => R.mulVec (a j)) = R.mulVec (localMean .U a)

/-- `l:moments`/`l:35`, lines 78–84/280–284: orthogonal matrices preserve
the coordinate sum of squares. Expand the column contractions. -/
def OrthogonalNormStatement : Prop :=
  ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 →
    ∀ v : Vec3, normSq (R.mulVec v) = normSq v

/-- `l:35`, lines 283–285: equal-length vectors are related by an orthogonal
matrix. A Householder reflection works unless the vectors agree; zero is included. -/
def OrthogonalTransportStatement : Prop :=
  ∀ v w : Vec3, normSq v = normSq w →
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 ∧ R.mulVec v = w

end AKLT.Blueprint.Mom
