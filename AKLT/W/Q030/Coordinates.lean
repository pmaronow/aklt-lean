import AKLT.Blueprint.Q.NodesSplits
import AKLT.Uniq.SpinCoordinates

noncomputable section
open scoped BigOperators
open AKLT.Challenge AKLT.Blueprint.Q

namespace AKLT.W.Q030

abbrev PairCoordinates := Fin 5 × Fin 5 → ℂ

/-- The binomial change from orthonormal coordinates to monomial coefficients. -/
def pairScale (p : Fin 5 × Fin 5) : ℂ :=
  AKLT.Uniq.singleScale p.1 * AKLT.Uniq.singleScale p.2

theorem pairScale_ne_zero (p : Fin 5 × Fin 5) : pairScale p ≠ 0 := by
  rcases p with ⟨i, j⟩
  have hs : ∀ k : Fin 5, AKLT.Uniq.singleScale k ≠ 0 := by
    intro k
    fin_cases k <;> norm_num [AKLT.Uniq.singleScale, Nat.choose]
  exact mul_ne_zero (hs i) (hs j)

def coordinates : PairHilbert ≃ₗ[ℂ] PairCoordinates where
  toFun v p := pairScale p * v p
  invFun v := WithLp.toLp 2 (fun p => v p / pairScale p)
  left_inv v := by
    ext p
    change pairScale p * v p / pairScale p = v p
    exact mul_div_cancel_left₀ _ (pairScale_ne_zero p)
  right_inv v := by
    funext p
    change pairScale p * (v p / pairScale p) = v p
    exact mul_div_cancel₀ _ (pairScale_ne_zero p)
  map_add' v w := by
    funext p
    change pairScale p * (v p + w p) = _
    exact mul_add _ _ _
  map_smul' c v := by
    funext p
    change pairScale p * (c * v p) = c * (pairScale p * v p)
    ring

theorem pairAt_zero_apply (A : Matrix (Fin 5) (Fin 5) ℂ)
    (v : PairHilbert) (i j : Fin 5) :
    pairAt A 0 v (i, j) = ∑ k : Fin 5, A i k * v (k, j) := by
  change (∑ p : Fin 5 × Fin 5,
    (if (0 : Fin 2) = 0 then (if j = p.2 then A i p.1 else 0)
      else (if i = p.1 then A j p.2 else 0)) * v p) = _
  simp [Fintype.sum_prod_type, ite_mul]

theorem pairAt_one_apply (A : Matrix (Fin 5) (Fin 5) ℂ)
    (v : PairHilbert) (i j : Fin 5) :
    pairAt A 1 v (i, j) = ∑ k : Fin 5, A j k * v (i, k) := by
  change (∑ p : Fin 5 × Fin 5,
    (if (1 : Fin 2) = 0 then (if j = p.2 then A i p.1 else 0)
      else (if i = p.1 then A j p.2 else 0)) * v p) = _
  simp [Fintype.sum_prod_type, ite_mul]

def integerPlus (i k : Fin 5) : ℂ :=
  if i.val + 1 = k.val then (k.val : ℂ) else 0

def integerMinus (i k : Fin 5) : ℂ :=
  if k.val + 1 = i.val then (4 - k.val : ℂ) else 0

def coordZ (v : PairCoordinates) (p : Fin 5 × Fin 5) : ℂ :=
  (4 - (p.1.val : ℂ) - (p.2.val : ℂ)) * v p

def coordPlus (v : PairCoordinates) (p : Fin 5 × Fin 5) : ℂ :=
  (∑ k : Fin 5, integerPlus p.1 k * v (k, p.2)) +
    ∑ k : Fin 5, integerPlus p.2 k * v (p.1, k)

def coordMinus (v : PairCoordinates) (p : Fin 5 × Fin 5) : ℂ :=
  (∑ k : Fin 5, integerMinus p.1 k * v (k, p.2)) +
    ∑ k : Fin 5, integerMinus p.2 k * v (p.1, k)

theorem scale_spinZ (i k : Fin 5) :
    AKLT.Uniq.singleScale i * spinZ i k =
      spinZ i k * AKLT.Uniq.singleScale k := by
  by_cases h : i = k
  · subst k; exact mul_comm _ _
  · simp [spinZ, h]

theorem scale_spinPlus (i k : Fin 5) :
    AKLT.Uniq.singleScale i * spinPlus i k =
      integerPlus i k * AKLT.Uniq.singleScale k := by
  simpa [integerPlus, ite_mul] using AKLT.Uniq.plus_normalization i k

theorem scale_spinMinus (i k : Fin 5) :
    AKLT.Uniq.singleScale i * spinMinus i k =
      integerMinus i k * AKLT.Uniq.singleScale k := by
  simpa [integerMinus, ite_mul] using AKLT.Uniq.minus_normalization i k

theorem coordinates_pairAt_zero
    (A B : Matrix (Fin 5) (Fin 5) ℂ)
    (h : ∀ i k, AKLT.Uniq.singleScale i * A i k =
      B i k * AKLT.Uniq.singleScale k)
    (v : PairHilbert) (i j : Fin 5) :
    coordinates (pairAt A 0 v) (i, j) =
      ∑ k : Fin 5, B i k * coordinates v (k, j) := by
  change pairScale (i, j) * (pairAt A 0 v (i, j)) = _
  rw [pairAt_zero_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  change (AKLT.Uniq.singleScale i * AKLT.Uniq.singleScale j) *
    (A i k * v (k, j)) =
      B i k * ((AKLT.Uniq.singleScale k * AKLT.Uniq.singleScale j) * v (k, j))
  calc
    _ = (AKLT.Uniq.singleScale i * A i k) *
        AKLT.Uniq.singleScale j * v (k, j) := by ring
    _ = _ := by rw [h]; ring

theorem coordinates_pairAt_one
    (A B : Matrix (Fin 5) (Fin 5) ℂ)
    (h : ∀ i k, AKLT.Uniq.singleScale i * A i k =
      B i k * AKLT.Uniq.singleScale k)
    (v : PairHilbert) (i j : Fin 5) :
    coordinates (pairAt A 1 v) (i, j) =
      ∑ k : Fin 5, B j k * coordinates v (i, k) := by
  change pairScale (i, j) * (pairAt A 1 v (i, j)) = _
  rw [pairAt_one_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  change (AKLT.Uniq.singleScale i * AKLT.Uniq.singleScale j) *
    (A j k * v (i, k)) =
      B j k * ((AKLT.Uniq.singleScale i * AKLT.Uniq.singleScale k) * v (i, k))
  calc
    _ = (AKLT.Uniq.singleScale j * A j k) *
        AKLT.Uniq.singleScale i * v (i, k) := by ring
    _ = _ := by rw [h]; ring

theorem coordinates_Z (v : PairHilbert) :
    coordinates ((pairAt spinZ 0 + pairAt spinZ 1) v) = coordZ (coordinates v) := by
  funext p
  rcases p with ⟨i, j⟩
  simp only [LinearMap.add_apply, map_add, Pi.add_apply]
  rw [coordinates_pairAt_zero spinZ spinZ scale_spinZ,
    coordinates_pairAt_one spinZ spinZ scale_spinZ]
  simp [spinZ, ite_mul, coordZ]
  ring

theorem coordinates_plus (v : PairHilbert) :
    coordinates ((pairAt spinPlus 0 + pairAt spinPlus 1) v) =
      coordPlus (coordinates v) := by
  funext p
  rcases p with ⟨i, j⟩
  simp only [LinearMap.add_apply, map_add, Pi.add_apply]
  rw [coordinates_pairAt_zero spinPlus integerPlus scale_spinPlus,
    coordinates_pairAt_one spinPlus integerPlus scale_spinPlus]
  rfl

theorem coordinates_minus (v : PairHilbert) :
    coordinates ((pairAt spinMinus 0 + pairAt spinMinus 1) v) =
      coordMinus (coordinates v) := by
  funext p
  rcases p with ⟨i, j⟩
  simp only [LinearMap.add_apply, map_add, Pi.add_apply]
  rw [coordinates_pairAt_zero spinMinus integerMinus scale_spinMinus,
    coordinates_pairAt_one spinMinus integerMinus scale_spinMinus]
  rfl

def coordCasimir (v : PairCoordinates) : PairCoordinates :=
  coordZ (coordZ v) + (1 / 2 : ℂ) •
    (coordPlus (coordMinus v) + coordMinus (coordPlus v))

theorem coordinates_casimir (v : PairHilbert) :
    coordinates (pairCasimir v) = coordCasimir (coordinates v) := by
  change coordinates
    ((pairAt spinZ 0 + pairAt spinZ 1) ((pairAt spinZ 0 + pairAt spinZ 1) v) +
      (1 / 2 : ℂ) •
        ((pairAt spinPlus 0 + pairAt spinPlus 1)
            ((pairAt spinMinus 0 + pairAt spinMinus 1) v) +
          (pairAt spinMinus 0 + pairAt spinMinus 1)
            ((pairAt spinPlus 0 + pairAt spinPlus 1) v))) = _
  simp only [map_add, map_smul, coordinates_Z, coordinates_plus,
    coordinates_minus, coordCasimir]

end AKLT.W.Q030
