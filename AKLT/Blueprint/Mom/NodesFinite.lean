import AKLT.Blueprint.Mom.NodesMoments

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Mom

/-- `l:finitefacts`, line 142: finite-dimensional Cauchy–Schwarz bounds each
interaction factor. Expressed with squared norms, including zero vectors. -/
def BallDotBoundsStatement : Prop :=
  ∀ a b : Vec3, normSq a ≤ 1 → normSq b ≤ 1 →
    0 ≤ 1 + dot a b ∧ 1 + dot a b ≤ 2

/-- `l:finitefacts`, lines 148–153: each ball field forbids at most one of
twelve distinct unit atoms; the union of at most four forbidden sets is smaller. -/
def LetterAvoidanceStatement : Prop :=
  ∀ k : ℕ, k ≤ 4 → ∀ b : Fin k → Vec3, (∀ i, normSq (b i) ≤ 1) →
    ∃ j : IcoLetter, ∀ i, 0 < 1 + dot (icoVector j) (b i)

/-- `l:finitefacts`, lines 143–156: a generic greedy extension lemma.
The alphabet is arbitrary; local feasibility is an explicit property of its
vectors, not a hypothesis naming any other blueprint statement. Order `Fin n`,
collect pins and already assigned neighbours, and apply local feasibility. -/
def GreedyAssignmentStatement : Prop :=
  ∀ (α : Type) [Fintype α], ∀ v : α → Vec3, (∀ a, normSq (v a) ≤ 1) →
    (∀ k : ℕ, k ≤ 4 → ∀ b : Fin k → Vec3, (∀ i, normSq (b i) ≤ 1) →
      ∃ a, ∀ i, 0 < 1 + dot (v a) (b i)) →
    ∀ n : ℕ, ∀ D : FiniteSpinNetwork n, D.Valid →
      ∃ σ : Fin n → α,
        (∀ e ∈ D.bonds, 0 < 1 + dot (v (σ e.1)) (v (σ e.2))) ∧
        ∀ x, ∀ j : Fin (D.pinCount x), 0 < 1 + dot (D.pin x j).val (v (σ x))

/-- The formal real scalar product on site coordinates; coincident endpoints
are permitted in observables and contribute twice to the separate degree. -/
def dotPolynomial {n : ℕ} (e : Fin n × Fin n) : MvPolynomial (Fin n × Fin 3) ℝ :=
  ∑ i, MvPolynomial.X (e.1, i) * MvPolynomial.X (e.2, i)

/-- The free bond product with the entire scalar-product observable inserted. -/
def freePolynomial {n : ℕ} (D : FiniteSpinNetwork n)
    (pairs : List (Fin n × Fin n)) : MvPolynomial (Fin n × Fin 3) ℝ :=
  (∏ e ∈ D.bonds, (1 + dotPolynomial e)) * (pairs.map dotPolynomial).prod

/-- `l:finitefacts`, lines 177–180: expanding bonds and scalar products gives
nonnegative real monomial coefficients. No degree restriction is needed for this step. -/
def FreeCoefficientsStatement : Prop :=
  ∀ n : ℕ, ∀ D : FiniteSpinNetwork n, ∀ pairs : List (Fin n × Fin n),
    ∀ m, 0 ≤ (freePolynomial D pairs).coeff m

/-- `l:finitefacts`, lines 181–190: control the support degree of the expanded
polynomial. Bonds have distinct endpoints; an observable loop counts twice. -/
def FreeDegreeStatement : Prop :=
  ∀ n : ℕ, ∀ D : FiniteSpinNetwork n, D.Valid →
    ∀ pairs : List (Fin n × Fin n),
      (∀ x, (D.bonds.filter fun e => e.1 = x ∨ e.2 = x).card +
        (pairs.filter fun e => e.1 = x).length +
        (pairs.filter fun e => e.2 = x).length ≤ 4) →
      SeparateDegreeFour (freePolynomial D pairs)

/-- `l:finitefacts`, lines 177–183: connect the actual free partition sum to
the formal polynomial. Evaluation commutes with finite sums and products. -/
def FreeEvaluationStatement : Prop :=
  ∀ n : ℕ, ∀ D : FiniteSpinNetwork n, ∀ pairs : List (Fin n × Fin n),
    D.partition false (fun a => (pairs.map fun e => dot (a e.1) (a e.2)).prod) =
      productFunctional D.status
        (fun a => MvPolynomial.eval (fun z => a z.1 z.2) (freePolynomial D pairs))

theorem freeEvaluation : FreeEvaluationStatement := by
  intro n D pairs
  simp [FiniteSpinNetwork.partition, FiniteSpinNetwork.weight, productFunctional,
    freePolynomial, dotPolynomial, dot, map_list_prod, List.map_map,
    Function.comp_def, mul_assoc]
  congr 1
  ext
  simp

/-- Agreement outside two sites, exactly the event used in the Top interface. -/
def twoSiteFibre {n : ℕ} (x y : Fin n) (σ τ : Fin n → SpinLetter) : Prop :=
  ∀ z, z ≠ x → z ≠ y → τ z = σ z

/-- `l:finitefacts`, lines 159–168: on a two-site fibre without a retained
bond, allocate all off-site factors to `C` and each incident factor to its site.
Zero site masses and zero off-site factors are allowed. -/
def TwoSiteFactorizationStatement : Prop :=
  ∀ n : ℕ, ∀ D : FiniteSpinNetwork n, D.Valid → ∀ pinned : Bool,
    ∀ x y : Fin n, x ≠ y → (x, y) ∉ D.bonds → (y, x) ∉ D.bonds →
    ∀ σ : Fin n → SpinLetter,
      ∃ C : ℝ, ∃ u v : SpinLetter → ℝ,
        0 ≤ C ∧ (∀ a, 0 ≤ u a) ∧ (∀ b, 0 ≤ v b) ∧
        ∀ τ, twoSiteFibre x y σ τ → D.weight pinned τ = C * u (τ x) * v (τ y)

/-- `l:finitefacts`, lines 169–175: enumerate a two-coordinate fibre, factor
its normalizer, and cancel it only when its normalized event mass is positive.
This generic finite-probability lemma is independent of the spin model. -/
def FactorizedConditioningStatement : Prop :=
  ∀ n : ℕ, ∀ w : (Fin n → SpinLetter) → ℝ, (∀ τ, 0 ≤ w τ) →
    ∀ x y : Fin n, x ≠ y → ∀ σ : Fin n → SpinLetter,
    ∀ C : ℝ, ∀ u v : SpinLetter → ℝ,
    (∀ τ, twoSiteFibre x y σ τ → w τ = C * u (τ x) * v (τ y)) →
    0 < eventMass (normalize w) (twoSiteFibre x y σ) →
    ∀ a b : SpinLetter,
      conditionalProbability (normalize w) (twoSiteFibre x y σ)
        (fun τ => τ x = a ∧ τ y = b) =
      conditionalProbability (normalize w) (twoSiteFibre x y σ) (fun τ => τ x = a) *
        conditionalProbability (normalize w) (twoSiteFibre x y σ) (fun τ => τ y = b)

/-- A squared norm is a sum of real squares; this also covers the zero vector. -/
theorem normSq_nonneg (a : Vec3) : 0 ≤ normSq a := by
  change 0 ≤ ∑ i, a i * a i
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (a i))

/-- `l:finitefacts`, line 157: the actual zero-site network has partition one,
regardless of the pinned flag. Empty products have their single empty configuration. -/
def EmptyPartitionStatement : Prop :=
  ∀ D : FiniteSpinNetwork 0, ∀ pinned : Bool, D.partition pinned (fun _ => 1) = 1

theorem emptyPartition : EmptyPartitionStatement := by
  intro D pinned
  have hb : D.bonds = ∅ := Finset.eq_empty_of_forall_notMem (fun e _ => Fin.elim0 e.1)
  simp [FiniteSpinNetwork.partition, FiniteSpinNetwork.weight, hb]

end AKLT.Blueprint.Mom
