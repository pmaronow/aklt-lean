import AKLT.Defs.FiniteNetwork

noncomputable section
open scoped BigOperators

namespace AKLT.Defs

/-- Spin coordinates on an explicitly finite support, zero only at omitted sites. -/
def supportSpins (V : Finset Plane) (n : V → SpinLetter) (x : Plane) : Vec3 :=
  if h : x ∈ V then spinVector (n ⟨x, h⟩) else 0

/-- `l:Iw`: deletion of the passage site and its factors, keeping all covered slots. -/
def withoutPassageFunctional (π : PatternData) (m : Fin 20 → UnitVector)
    (f : (Plane → Vec3) → ℝ) : ℝ :=
  let V := π.active.erase (0, 0)
  ∑ n : V → SpinLetter,
    (∏ x : V, spinWeight (π.statusAt x.val) (n x)) * f (supportSpins V n) *
    (∏ e ∈ π.bonds, if e.1 = (0, 0) ∨ e.2 = (0, 0) then 1
      else 1 + dot (supportSpins V n e.1) (supportSpins V n e.2)) *
    ∏ j : Fin 20, if π.statusAt (externalSlot j).1 = .X then 1 else
      1 + dot (m j).val (supportSpins V n (externalSlot j).1)

/-- The original rational pattern polynomial, before any leaf deletion. -/
def originalPatternPolynomial (π : PatternData) (next : Bool) : MvPolynomial (Fin 20 × Fin 3) ℚ :=
  contractSpins π.active (fun x => if next ∧ x = (0, 0) then .D else π.statusAt x)
    ((∏ e ∈ π.bonds, if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1
      else 1 + formalDot (fun k => .inl (e.1, k)) (fun k => .inl (e.2, k))) *
    ∏ j : Fin 20, if π.statusAt (externalSlot j).1 = .X then 1
      else 1 + formalDot (fun k => .inl ((externalSlot j).1, k)) (fun k => .inr (j, k)))

/-- `l:leaf`: the local product of every covered slot at one boundary site. -/
def coveredSiteField (m : Fin 20 → UnitVector) (x : Plane) (n : Vec3) : ℝ :=
  ∏ j : Fin 20, if (externalSlot j).1 = x then 1 + dot (m j).val n else 1

/-- A polynomial uses no vector tokens outside its specified finite tensor product. -/
def SupportedVectors (J : Finset (Fin 20)) (p : MvPolynomial (Fin 20 × Fin 3) ℚ) : Prop :=
  ∀ m ∈ p.support, ∀ j : Fin 20, j ∉ J → ∀ k : Fin 3, m (j, k) = 0

/-- The integer-coordinate complex Hermitian form, before any denominator rounding. -/
def complexSectorMatrix (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ) :
    Matrix (CentralBasis π r ε) (CentralBasis π r ε) ℂ :=
  fun a b => ∑ σ, ∑ τ,
    (exchangeBasisVector π r ε a.val σ : ℂ) * pauliOperator (reductionVectors π r) p σ τ *
      (exchangeBasisVector π r ε b.val τ : ℂ)

/-- Reindex by an explicit basis bijection, so certificate data choose their concrete
finite ordering without relying on a noncomputable enumeration. -/
def indexedSectorMatrix (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (I : Finset (Fin 20)) (D₀ p q : ℕ) {t : ℕ} (index : Fin t ≃ CentralBasis π r ε) :
    Matrix (Fin t) (Fin t) ℤ :=
  (thresholdSectorMatrix π r ε I D₀ p q).submatrix index index

/-- The single tensor slot of any group. -/
def leaderToken (π : PatternData) (r : Representation) (x : reductionGroups π) : reductionVectors π r :=
  ⟨groupLeader x.val, by
    apply Finset.mem_biUnion.mpr
    refine ⟨x.val, x.property, ?_⟩
    split <;> simp⟩

/-- The second token of a retained pair. -/
def secondToken (π : PatternData) (r : Representation) (x : reductionGroups π)
    (h : groupIsPair π r x.val = true) : reductionVectors π r :=
  ⟨groupSecond x.val, by
    apply Finset.mem_biUnion.mpr
    exact ⟨x.val, x.property, by simp [h]⟩⟩

/-- Exchange of two tensor factors, as an actual linear map on Hilbert coordinates. -/
def exchangeOperator (J : Finset (Fin 20)) (j k : J) :
    Module.End ℂ (EuclideanSpace ℂ (J → Fin 2)) :=
  Matrix.toEuclideanLin fun σ τ => if σ = fun x => τ (Equiv.swap j k x) then 1 else 0

/-- Symmetric-pair orthogonal projection `(I+exchange)/2`. -/
def symmetricPairProjection (J : Finset (Fin 20)) (j k : J) :
    Module.End ℂ (EuclideanSpace ℂ (J → Fin 2)) :=
  (1 / 2 : ℂ) • (1 + exchangeOperator J j k)

/-- Tensor power of a two-dimensional matrix in the same tensor basis as all operators. -/
def tensorPowerMatrix (J : Finset (Fin 20)) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (J → Fin 2) (J → Fin 2) ℂ := fun σ τ => ∏ j : J, g (σ j) (τ j)

/-- Leading principal minor, including order zero, in exact integer arithmetic. -/
def leadingMinor {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (h : k ≤ n) : ℤ :=
  (M.submatrix (fun i : Fin k => (⟨i.val, by omega⟩ : Fin n))
    (fun i : Fin k => (⟨i.val, by omega⟩ : Fin n))).det

/-- `l:integercheck`: optional Bareiss state, retaining the previous pivot separately. -/
def bareissState {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : ℕ → Matrix (Fin n) (Fin n) ℤ × ℤ
  | 0 => (M, 1)
  | j + 1 =>
    let old := bareissState M j
    if h : j < n then
      let a : Fin n := ⟨j, h⟩
      (fun i l => if j < i.val ∧ j < l.val then
        (old.1 a a * old.1 i l - old.1 i a * old.1 a l) / old.2 else old.1 i l,
        old.1 a a)
    else old

/-- The j-th optional Bareiss pivot. -/
def bareissPivot {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (j : ℕ) : ℤ :=
  if h : j < n then (bareissState M j).1 ⟨j, h⟩ ⟨j, h⟩ else 0

/-- `d:exchange`: canonical signs for an orthogonal sector decomposition.
Unused single/U-pair signs are fixed to true. The original `ExchangeSigns`
type remains unchanged; its unrestricted assignments can repeat a space. -/
def EffectiveExchangeSigns (π : PatternData) (r : Representation) (ε : ExchangeSigns π) : Prop :=
  ∀ x : reductionGroups π, ¬ (groupIsPair π r x.val = true ∧ π.statusAt x.val = .D) → ε x = true

/-- `p:certificate`: actual reconstructed witness existence, separate from soundness. -/
def H1SectorWitnesses (π : PatternData) (r : Representation) (I : Finset (Fin 20))
    (D₀ p q : ℕ) : Prop :=
  ∀ ε : ExchangeSigns π, ∃ t : ℕ, ∃ index : Fin t ≃ CentralBasis π r ε,
    ∃ g d S : ℕ, ∃ L : Matrix (Fin t) (Fin t) ℤ,
      (∀ i j, i < j → L i j = 0) ∧
      GramResidualRows (indexedSectorMatrix π r ε I D₀ p q index) L g d S

/-- `t:H1`: numerator of the threshold assigned to this pattern's type. -/
def h1Numerator (π : PatternData) : ℕ := if π.outgoing = .north then 961 else 187

/-- `t:H1`: positive denominator paired with `h1Numerator`. -/
def h1Denominator (π : PatternData) : ℕ := if π.outgoing = .north then 1000 else 200

end AKLT.Defs
