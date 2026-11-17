module
public import AKLT.Defs.FiniteNetwork
public import AKLT.Defs.Stationary
public import AKLT.Defs.FrameModel

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Top

/-- `l:moments`: twelve distinct antipodal unit atoms, exact tensors, and degree-four
orthogonal covariance, including sitewise U/D products. No arbitrary-function invariance. -/
def MomentsStatement : Prop :=
  Function.Injective icoVector ∧ (∀ j, normSq (icoVector j) = 1) ∧
  (∀ j, ∃ k, icoVector k = -icoVector j) ∧ moment (fun _ => 1) = 1 ∧
  (∀ i, moment (fun n => n i) = 0) ∧
  (∀ i j k, moment (fun n => n i * n j * n k) = 0) ∧
  (∀ i j : Fin 3, moment (fun n => n i * n j) = if i = j then 1 / 3 else 0) ∧
  (∀ i j k l : Fin 3, moment (fun n => n i * n j * n k * n l) =
    ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
      (if i = l ∧ j = k then 1 else 0)) / 15) ∧
  (∀ m : Fin 3 → ℕ, (∑ i, m i) ≤ 4 → ∀ s : Status, s = .U ∨ s = .D →
    siteFunctional s (fun n => ∏ i, n i ^ m i) = (rationalStatusMoment s m : ℝ)) ∧
  ∀ n : ℕ, ∀ s : Fin n → Status, (∀ x, s x = .U ∨ s x = .D) →
    ∀ p : MvPolynomial (Fin n × Fin 3) ℝ, SeparateDegreeFour p →
    ∀ R : Fin n → Matrix (Fin 3) (Fin 3) ℝ, (∀ x, (R x).transpose * R x = 1) →
    productFunctional s (fun a => MvPolynomial.eval (fun v => ((R v.1).mulVec (a v.1)) v.2) p) =
      productFunctional s (fun a => MvPolynomial.eval (fun v => a v.1 v.2) p)

/-- `l:finitefacts`: positivity (also at zero sites), conditional independence,
degree-admissible free scalar-product positivity, and the support norm bound. -/
def FiniteFactsStatement : Prop :=
  (∀ s : Status, s = .U ∨ s = .D → ∀ j : SpinLetter,
    0 < spinWeight s j → normSq (spinVector j) ≤ 1) ∧
  ∀ n : ℕ, ∀ D : FiniteSpinNetwork n, D.Valid →
    0 < D.partition true (fun _ => 1) ∧ 0 < D.partition false (fun _ => 1) ∧
    (∀ pairs : List (Fin n × Fin n),
      (∀ x, (D.bonds.filter fun e => e.1 = x ∨ e.2 = x).card +
        (pairs.filter fun e => e.1 = x).length + (pairs.filter fun e => e.2 = x).length ≤ 4) →
      0 ≤ D.partition false (fun a => (pairs.map fun e => dot (a e.1) (a e.2)).prod)) ∧
    ∀ pinned : Bool, ∀ x y : Fin n, x ≠ y → (x, y) ∉ D.bonds → (y, x) ∉ D.bonds →
      ∀ σ : Fin n → SpinLetter,
      let E := fun τ : Fin n → SpinLetter => ∀ z, z ≠ x → z ≠ y → τ z = σ z
      let p := normalize (D.weight pinned)
      0 < eventMass p E → ∀ a b : SpinLetter,
        conditionalProbability p E (fun τ => τ x = a ∧ τ y = b) =
          conditionalProbability p E (fun τ => τ x = a) *
            conditionalProbability p E (fun τ => τ y = b)

/-- `l:35`: both site laws have the three-factor mean bound; every vector in
the radius-3/5 ball is realized by a triple of unit U fields. Squared norms avoid square roots. -/
def ThreeFactorMeanStatement : Prop :=
  (∀ k : ℕ, k ≤ 3 → ∀ a : Fin k → Vec3, (∀ j, normSq (a j) ≤ 1) →
    ∀ s : Status, s = .U ∨ s = .D →
      0 < siteFunctional s (localProduct a) ∧ normSq (localMean s a) ≤ (3 / 5 : ℝ)^2) ∧
  {b : Vec3 | ∃ a : Fin 3 → UnitVector, localMean .U (fun j => (a j).val) = b} =
    {b : Vec3 | normSq b ≤ (3 / 5 : ℝ)^2}

/-- `l:exact`: finite quadrature for every polynomial of separate degree at most four,
including any selected U-to-D zero-atom mixtures. Atoms may repeat in a weighted law. -/
def ExactStatement : Prop :=
  ∀ n : ℕ, ∀ k : Fin n → ℕ, ∀ F : (x : Fin n) → FrameData (k x),
    (∀ x, MomentLaw (F x)) → ∀ s : Fin n → Status, (∀ x, s x = .U ∨ s x = .D) →
    ∀ p : MvPolynomial (Fin n × Fin 3) ℝ, SeparateDegreeFour p →
    let atom : (x : Fin n) → Option (Fin (k x)) → Vec3 := fun x j =>
      match j with | none => (0 : Vec3) | some i => (F x).point i
    let weight : (x : Fin n) → Option (Fin (k x)) → ℝ := fun x j =>
      match j with
      | none => if s x = .D then (2 / 5 : ℝ) else 0
      | some i => (if s x = .D then (3 / 5 : ℝ) else 1) * (F x).weight i
    (∑ a : (x : Fin n) → Option (Fin (k x)),
      (∏ x, weight x (a x)) * MvPolynomial.eval (fun v => atom v.1 (a v.1) v.2) p) =
      productFunctional s (fun a => MvPolynomial.eval (fun v => a v.1 v.2) p)

end AKLT.Blueprint.Top
