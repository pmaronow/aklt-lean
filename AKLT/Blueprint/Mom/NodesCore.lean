import AKLT.Blueprint.Top.Common

/-! Reusable finite-sum interfaces for Section 2. All unproved nodes are closed
propositions. Parameters in their bodies are ordinary algebraic data and premises,
never other named blueprint propositions. -/

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Mom

/-- A single-site coordinate monomial, including the constant monomial. -/
def mono (m : Fin 3 → ℕ) (v : Vec3) : ℝ := ∏ i, v i ^ m i

/-- A finite quadrature, without any positivity or normalization assumption. -/
def finiteFunctional {α : Type} [Fintype α] (w : α → ℝ) (v : α → Vec3)
    (f : Vec3 → ℝ) : ℝ := ∑ a, w a * f (v a)

/-- A dependent finite product quadrature. Empty alphabets and zero sites are allowed. -/
def productSum {n : ℕ} (α : Fin n → Type) [∀ x, Fintype (α x)]
    (w : (x : Fin n) → α x → ℝ) (v : (x : Fin n) → α x → Vec3)
    (f : (Fin n → Vec3) → ℝ) : ℝ := by
  classical
  exact ∑ a : (x : Fin n) → α x, (∏ x, w x (a x)) * f (fun x => v x (a x))

/-- Isotropic tensors through order four, with positive-degree scale `c`.
No linearity is asserted here; callers supply an actual finite functional. -/
def TensorLaw (L : (Vec3 → ℝ) → ℝ) (c : ℝ) : Prop :=
  L (fun _ => 1) = 1 ∧
  (∀ i, L (fun v => v i) = 0) ∧
  (∀ i j k, L (fun v => v i * v j * v k) = 0) ∧
  (∀ i j : Fin 3, L (fun v => v i * v j) = if i = j then c / 3 else 0) ∧
  ∀ i j k l : Fin 3, L (fun v => v i * v j * v k * v l) =
    c * ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
      (if i = l ∧ j = k then 1 else 0)) / 15

/-- Rational monomial tensor with an arbitrary positive-degree scale. -/
def scaledMoment (c : ℝ) (m : Fin 3 → ℕ) : ℝ :=
  if (∑ i, m i) = 0 then 1 else c * (rationalMoment m : ℝ)

/-- `l:moments`, lines 73–76: reconstruct the indexed tensors from parity and
the three even scalar cases. Reorder coordinate products and classify the indices. -/
def ScalarTensorReconstructionStatement : Prop :=
  ∀ L : (Vec3 → ℝ) → ℝ,
    L (fun _ => 1) = 1 →
    (∀ m : Fin 3 → ℕ, (∃ i, Odd (m i)) → L (mono m) = 0) →
    (∀ i, L (fun v => v i ^ 2) = 1 / 3) →
    (∀ i, L (fun v => v i ^ 4) = 1 / 5) →
    (∀ i j, i ≠ j → L (fun v => v i ^ 2 * v j ^ 2) = 1 / 15) →
    TensorLaw L 1

/-- `l:moments`, lines 73–76: enumerate the exponent triples of total degree
at most four; the tensor formulas determine every such monomial. -/
def TensorMonomialStatement : Prop :=
  ∀ L : (Vec3 → ℝ) → ℝ, ∀ c : ℝ, TensorLaw L c →
    ∀ m : Fin 3 → ℕ, (∑ i, m i) ≤ 4 → L (mono m) = scaledMoment c m

/-- `l:moments`, lines 78–84: expand transformed tensors into finite sums,
then contract matrix rows. Derive row orthogonality from the stated column identity. -/
def OrthogonalTensorStatement : Prop :=
  ∀ (α : Type) [Fintype α], ∀ w : α → ℝ, ∀ v : α → Vec3, ∀ c : ℝ,
    TensorLaw (finiteFunctional w v) c →
    ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 →
      TensorLaw (finiteFunctional w (fun a => R.mulVec (v a))) c

/-- `l:moments`/`l:exact`, lines 90–94/317–320: finite distributivity factors
a product of single-site functions. No degree, mass, or nonempty-support premise. -/
def ProductFactorizationStatement : Prop :=
  ∀ n : ℕ, ∀ (α : Fin n → Type) [∀ x, Fintype (α x)],
    ∀ w : (x : Fin n) → α x → ℝ, ∀ v : (x : Fin n) → α x → Vec3,
    ∀ f : Fin n → Vec3 → ℝ,
      productSum α w v (fun a => ∏ x, f x (a x)) =
        ∏ x, finiteFunctional (w x) (v x) (f x)

theorem productFactorization : ProductFactorizationStatement := by
  intro n α _ w v f
  unfold productSum finiteFunctional
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun x a => w x a * f x (v x a))).symm

/-- `l:moments`/`l:exact`, lines 90–94/311–320: expand a polynomial on its
actual support and commute finite sums. This node does not assume a degree bound. -/
def PolynomialExpansionStatement : Prop :=
  ∀ n : ℕ, ∀ (α : Fin n → Type) [∀ x, Fintype (α x)],
    ∀ w : (x : Fin n) → α x → ℝ, ∀ v : (x : Fin n) → α x → Vec3,
    ∀ p : MvPolynomial (Fin n × Fin 3) ℝ,
      productSum α w v (fun a => MvPolynomial.eval (fun z => a z.1 z.2) p) =
        ∑ m ∈ p.support, p.coeff m *
          productSum α w v (fun a => ∏ x, mono (fun i => m (x, i)) (a x))

/-- `l:moments`, lines 86–89: mixing with evaluation at zero preserves the
constant and rescales all positive tensors. This is immediate scalar algebra. -/
def TensorZeroMixtureStatement : Prop :=
  ∀ L : (Vec3 → ℝ) → ℝ, ∀ c q : ℝ, TensorLaw L c →
    TensorLaw (fun f => q * L f + (1 - q) * f 0) (q * c)

theorem tensorZeroMixture : TensorZeroMixtureStatement := by
  intro L c q h
  rcases h with ⟨h0, h1, h3, h2, h4⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [h0]; ring
  · intro i; simp only [h1, Pi.zero_apply, mul_zero, add_zero]
  · intro i j k; simp only [h3, Pi.zero_apply, mul_zero, add_zero]
  · intro i j
    by_cases h : i = j
    · simp only [h2, h, ite_true, Pi.zero_apply, mul_zero, add_zero]; ring
    · simp only [h2, h, ite_false, Pi.zero_apply, mul_zero, add_zero]
  · intro i j k l
    simp only [h4, Pi.zero_apply, mul_zero, add_zero]
    ring

/-- `l:finitefacts`, lines 181–189: the displayed rational tensors have
nonnegative entries. The degree test is deliberately unnecessary here. -/
theorem rationalStatusMoment_nonneg (s : Status) (m : Fin 3 → ℕ) :
    0 ≤ (rationalStatusMoment s m : ℝ) := by
  unfold rationalStatusMoment rationalMoment
  split_ifs <;> norm_num

end AKLT.Blueprint.Mom
