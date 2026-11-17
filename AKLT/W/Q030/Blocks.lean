module
public import AKLT.W.Q030.Coordinates

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Blueprint.Q

namespace AKLT.W.Q030

/-- The integer Casimir, arranged in the nine anti-diagonal weight blocks. -/
def blockCasimir (v : PairCoordinates) : PairCoordinates := fun p =>
  ( ![
    ![20 * v (0, 0), 16 * v (0, 1) + 4 * v (1, 0), 12 * v (0, 2) + 3 * v (1, 1), 8 * v (0, 3) + 2 * v (1, 2), 4 * v (0, 4) + 1 * v (1, 3)],
    ![16 * v (1, 0) + 4 * v (0, 1), 14 * v (1, 1) + 8 * v (0, 2) + 8 * v (2, 0), 12 * v (1, 2) + 12 * v (0, 3) + 6 * v (2, 1), 10 * v (1, 3) + 16 * v (0, 4) + 4 * v (2, 2), 8 * v (1, 4) + 2 * v (2, 3)],
    ![12 * v (2, 0) + 3 * v (1, 1), 12 * v (2, 1) + 6 * v (1, 2) + 12 * v (3, 0), 12 * v (2, 2) + 9 * v (1, 3) + 9 * v (3, 1), 12 * v (2, 3) + 12 * v (1, 4) + 6 * v (3, 2), 12 * v (2, 4) + 3 * v (3, 3)],
    ![8 * v (3, 0) + 2 * v (2, 1), 10 * v (3, 1) + 4 * v (2, 2) + 16 * v (4, 0), 12 * v (3, 2) + 6 * v (2, 3) + 12 * v (4, 1), 14 * v (3, 3) + 8 * v (2, 4) + 8 * v (4, 2), 16 * v (3, 4) + 4 * v (4, 3)],
    ![4 * v (4, 0) + 1 * v (3, 1), 8 * v (4, 1) + 2 * v (3, 2), 12 * v (4, 2) + 3 * v (3, 3), 16 * v (4, 3) + 4 * v (3, 4), 20 * v (4, 4)] ] : Fin 5 → Fin 5 → ℂ) p.1 p.2

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 3000 in
theorem coordCasimir_eq (v : PairCoordinates) : coordCasimir v = blockCasimir v := by
  funext p
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [coordCasimir, coordZ, coordPlus, coordMinus, integerPlus,
      integerMinus, Fin.sum_univ_succ, blockCasimir] <;> ring

/-- The free coefficient for each total weight. -/
def parameters : PairCoordinates →ₗ[ℂ] (Fin 9 → ℂ) where
  toFun v := ![v (0, 0), v (0, 1) / 4, v (0, 2) / 6, v (0, 3) / 4,
    v (0, 4), v (1, 4) / 4, v (2, 4) / 6, v (3, 4) / 4, v (4, 4)]
  map_add' v w := by
    funext r
    fin_cases r <;> simp [add_div]
  map_smul' c v := by
    funext r
    fin_cases r <;> simp [smul_eq_mul, mul_div_assoc]

/-- The total-weight index, ranging from zero through eight. -/
def totalWeight (p : Fin 5 × Fin 5) : Fin 9 :=
  ⟨p.1.val + p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩

/-- One vector in each weight block, with binomial-product coefficients. -/
def topCoordinates : (Fin 9 → ℂ) →ₗ[ℂ] PairCoordinates where
  toFun c p := ((Nat.choose 4 p.1.val : ℂ) * (Nat.choose 4 p.2.val : ℂ)) *
    c (totalWeight p)
  map_add' c d := by
    funext p
    exact mul_add _ _ _
  map_smul' a c := by
    funext p
    change _ * (a * _) = a * (_ * _)
    ring

theorem parameters_topCoordinates (c : Fin 9 → ℂ) :
    parameters (topCoordinates c) = c := by
  funext r
  fin_cases r <;> norm_num [parameters, topCoordinates, totalWeight, Nat.choose]

theorem blockCasimir_topCoordinates (c : Fin 9 → ℂ) :
    blockCasimir (topCoordinates c) = (20 : ℂ) • topCoordinates c := by
  funext p
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [blockCasimir, topCoordinates, totalWeight, Nat.choose] <;> ring

/-- The first n-1 equations of each n-dimensional tridiagonal block force
all its coordinates to be binomial multiples of the first coordinate. -/
theorem reconstruct_eigenvector (v : PairCoordinates)
    (h : blockCasimir v = (20 : ℂ) • v) :
    topCoordinates (parameters v) = v := by
  have h01 := congrFun h (0, 1)
  change 16 * v (0, 1) + 4 * v (1, 0) = 20 * v (0, 1) at h01
  have h02 := congrFun h (0, 2)
  change 12 * v (0, 2) + 3 * v (1, 1) = 20 * v (0, 2) at h02
  have h11 := congrFun h (1, 1)
  change 14 * v (1, 1) + 8 * v (0, 2) + 8 * v (2, 0) = 20 * v (1, 1) at h11
  have h03 := congrFun h (0, 3)
  change 8 * v (0, 3) + 2 * v (1, 2) = 20 * v (0, 3) at h03
  have h12 := congrFun h (1, 2)
  change 12 * v (1, 2) + 12 * v (0, 3) + 6 * v (2, 1) = 20 * v (1, 2) at h12
  have h21 := congrFun h (2, 1)
  change 12 * v (2, 1) + 6 * v (1, 2) + 12 * v (3, 0) = 20 * v (2, 1) at h21
  have h04 := congrFun h (0, 4)
  change 4 * v (0, 4) + 1 * v (1, 3) = 20 * v (0, 4) at h04
  have h13 := congrFun h (1, 3)
  change 10 * v (1, 3) + 16 * v (0, 4) + 4 * v (2, 2) = 20 * v (1, 3) at h13
  have h22 := congrFun h (2, 2)
  change 12 * v (2, 2) + 9 * v (1, 3) + 9 * v (3, 1) = 20 * v (2, 2) at h22
  have h31 := congrFun h (3, 1)
  change 10 * v (3, 1) + 4 * v (2, 2) + 16 * v (4, 0) = 20 * v (3, 1) at h31
  have h14 := congrFun h (1, 4)
  change 8 * v (1, 4) + 2 * v (2, 3) = 20 * v (1, 4) at h14
  have h23 := congrFun h (2, 3)
  change 12 * v (2, 3) + 12 * v (1, 4) + 6 * v (3, 2) = 20 * v (2, 3) at h23
  have h32 := congrFun h (3, 2)
  change 12 * v (3, 2) + 6 * v (2, 3) + 12 * v (4, 1) = 20 * v (3, 2) at h32
  have h24 := congrFun h (2, 4)
  change 12 * v (2, 4) + 3 * v (3, 3) = 20 * v (2, 4) at h24
  have h33 := congrFun h (3, 3)
  change 14 * v (3, 3) + 8 * v (2, 4) + 8 * v (4, 2) = 20 * v (3, 3) at h33
  have h34 := congrFun h (3, 4)
  change 16 * v (3, 4) + 4 * v (4, 3) = 20 * v (3, 4) at h34
  funext p
  rcases p with ⟨i, j⟩
  fin_cases i <;> fin_cases j
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    ring
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    ring
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    ring
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    linear_combination (-1 / 4 : ℂ) * h01
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    linear_combination (-1 / 3 : ℂ) * h02
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    linear_combination (-1 / 2 : ℂ) * h03
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    linear_combination (-1 / 1 : ℂ) * h04
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    ring
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    linear_combination (-1 / 4 : ℂ) * h02 + (-1 / 8 : ℂ) * h11
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    linear_combination (-2 / 3 : ℂ) * h03 + (-1 / 6 : ℂ) * h12
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    linear_combination (-5 / 2 : ℂ) * h04 + (-1 / 4 : ℂ) * h13
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    linear_combination (-1 / 2 : ℂ) * h14
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    ring
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    linear_combination (-7 / 36 : ℂ) * h03 + (-1 / 9 : ℂ) * h12 + (-1 / 12 : ℂ) * h21
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    linear_combination (-11 / 9 : ℂ) * h04 + (-2 / 9 : ℂ) * h13 + (-1 / 9 : ℂ) * h22
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    linear_combination (-2 / 3 : ℂ) * h14 + (-1 / 6 : ℂ) * h23
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    linear_combination (-1 / 3 : ℂ) * h24
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    ring
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    linear_combination (-5 / 36 : ℂ) * h04 + (-11 / 144 : ℂ) * h13 + (-5 / 72 : ℂ) * h22 + (-1 / 16 : ℂ) * h31
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    linear_combination (-7 / 36 : ℂ) * h14 + (-1 / 9 : ℂ) * h23 + (-1 / 12 : ℂ) * h32
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    linear_combination (-1 / 4 : ℂ) * h24 + (-1 / 8 : ℂ) * h33
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]
    linear_combination (-1 / 4 : ℂ) * h34
  · norm_num [topCoordinates, parameters, totalWeight, Nat.choose]

end AKLT.W.Q030
