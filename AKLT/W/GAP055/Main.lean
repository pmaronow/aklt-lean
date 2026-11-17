import AKLT.Blueprint.Gap.NodesShell

noncomputable section

open AKLT.Defs AKLT.Challenge
open scoped BigOperators

namespace AKLT.W.GAP055

private theorem centeredIntIntervalCard (c : ℤ) (r : ℕ) :
    (Finset.Icc (c - (r : ℤ)) (c + (r : ℤ))).card = 2 * r + 1 := by
  have hz :
      ((Finset.Icc (c - (r : ℤ)) (c + (r : ℤ))).card : ℤ) = 2 * (r : ℤ) + 1 := by
    rw [Int.card_Icc_of_le _ _ (by omega)]
    ring
  exact_mod_cast hz

private theorem loosePowerBound (x : ℝ) (hx : 1 ≤ x) :
    (2 * x + 1) ^ 2 ≤ 25 * x ^ 2 := by
  have hbase : 2 * x + 1 ≤ 3 * x := by linarith
  have hnonneg : 0 ≤ 2 * x + 1 := by positivity
  have hnonneg' : 0 ≤ 3 * x := by positivity
  calc
    (2 * x + 1) ^ 2 ≤ (3 * x) ^ 2 :=
      (sq_le_sq₀ hnonneg hnonneg').2 hbase
    _ = 9 * x ^ 2 := by ring
    _ ≤ 25 * x ^ 2 := by nlinarith [sq_nonneg x]

private theorem nearCardinalityBound (a y : Plane) (n : ℕ) (hn : 1 ≤ n) :
    ((Finset.univ \ AKLT.Blueprint.Gap.farSites a y (n ^ 8) ((n : ℝ) ^ 3)).card : ℝ)
      ≤ 25 * (n : ℝ) ^ 6 := by
  classical
  let near : Finset (square a (n ^ 8)) :=
    Finset.univ \ AKLT.Blueprint.Gap.farSites a y (n ^ 8) ((n : ℝ) ^ 3)
  let box : Finset Plane :=
    (Finset.Icc (y.1 - ((n ^ 3 : ℕ) : ℤ)) (y.1 + ((n ^ 3 : ℕ) : ℤ))).product
      (Finset.Icc (y.2 - ((n ^ 3 : ℕ) : ℤ)) (y.2 + ((n ^ 3 : ℕ) : ℤ)))
  have himage : (near.image Subtype.val).card = near.card := by
    exact Finset.card_image_of_injective _ (fun _ _ h => Subtype.ext h)
  have hsubset : near.image Subtype.val ⊆ box := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    have hxnot : x ∉ AKLT.Blueprint.Gap.farSites a y (n ^ 8) ((n : ℝ) ^ 3) :=
      (Finset.mem_sdiff.mp hx).2
    simp only [AKLT.Blueprint.Gap.farSites, Finset.mem_filter,
      Finset.mem_univ, true_and] at hxnot
    have hdistR : (supDist x.val y : ℝ) ≤ (n : ℝ) ^ 3 := le_of_not_gt hxnot
    have hdist : supDist x.val y ≤ n ^ 3 := by exact_mod_cast hdistR
    have hfirst : (x.val.1 - y.1).natAbs ≤ n ^ 3 :=
      le_trans (Nat.le_max_left _ _) hdist
    have hsecond : (x.val.2 - y.2).natAbs ≤ n ^ 3 :=
      le_trans (Nat.le_max_right _ _) hdist
    have hfirstAbs : |x.val.1 - y.1| ≤ ((n ^ 3 : ℕ) : ℤ) := by
      have hcast : ((x.val.1 - y.1).natAbs : ℤ) ≤ ((n ^ 3 : ℕ) : ℤ) := by
        exact_mod_cast hfirst
      simpa only [Int.natCast_natAbs] using hcast
    have hsecondAbs : |x.val.2 - y.2| ≤ ((n ^ 3 : ℕ) : ℤ) := by
      have hcast : ((x.val.2 - y.2).natAbs : ℤ) ≤ ((n ^ 3 : ℕ) : ℤ) := by
        exact_mod_cast hsecond
      simpa only [Int.natCast_natAbs] using hcast
    have hfirstBounds := abs_le.mp hfirstAbs
    have hsecondBounds := abs_le.mp hsecondAbs
    change x.val ∈
      (Finset.Icc (y.1 - ((n ^ 3 : ℕ) : ℤ)) (y.1 + ((n ^ 3 : ℕ) : ℤ))).product
        (Finset.Icc (y.2 - ((n ^ 3 : ℕ) : ℤ)) (y.2 + ((n ^ 3 : ℕ) : ℤ)))
    rw [Finset.product_eq_sprod]
    simp only [Finset.mem_product, Finset.mem_Icc]
    constructor <;> constructor <;> omega
  have hnearNat : near.card ≤ (2 * n ^ 3 + 1) ^ 2 := by
    calc
      near.card = (near.image Subtype.val).card := himage.symm
      _ ≤ box.card := Finset.card_le_card hsubset
      _ = (2 * n ^ 3 + 1) ^ 2 := by
        simp only [box, Finset.product_eq_sprod, Finset.card_product,
          centeredIntIntervalCard]
        ring
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hnR
  have hbound := loosePowerBound ((n : ℝ) ^ 3) hpow
  have hcast : (near.card : ℝ) ≤ ((2 * n ^ 3 + 1) ^ 2 : ℕ) := by
    exact_mod_cast hnearNat
  have hpower2 : (n : ℝ) ^ 6 = ((n : ℝ) ^ 3) ^ 2 := by
    rw [show 6 = 3 * 2 by norm_num, pow_mul]
  calc
    (near.card : ℝ) ≤ ((2 * n ^ 3 + 1) ^ 2 : ℕ) := hcast
    _ = (2 * (n : ℝ) ^ 3 + 1) ^ 2 := by
      norm_cast
    _ ≤ 25 * ((n : ℝ) ^ 3) ^ 2 := hbound
    _ = 25 * (n : ℝ) ^ 6 := by rw [← hpower2]

theorem main : AKLT.Blueprint.Gap.HammingCardinalityStatement := by
  classical
  intro a y n hn
  constructor
  · exact nearCardinalityBound a y n hn
  · have hcard : Fintype.card (square a (n ^ 8)) = (2 * n ^ 8 + 1) ^ 2 := by
      rw [Fintype.card_coe, square, Finset.product_eq_sprod, Finset.card_product,
        centeredIntIntervalCard, centeredIntIntervalCard]
      ring
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpow : (1 : ℝ) ≤ (n : ℝ) ^ 8 := one_le_pow₀ hnR
    have hbound := loosePowerBound ((n : ℝ) ^ 8) hpow
    have hpower2 : (n : ℝ) ^ 16 = ((n : ℝ) ^ 8) ^ 2 := by
      rw [show 16 = 8 * 2 by norm_num, pow_mul]
    have hcardR : (Fintype.card (square a (n ^ 8)) : ℝ) =
        (2 * (n : ℝ) ^ 8 + 1) ^ 2 := by
      rw [hcard]
      norm_cast
    rw [hcardR]
    calc
      (2 * (n : ℝ) ^ 8 + 1) ^ 2 ≤ 25 * ((n : ℝ) ^ 8) ^ 2 := hbound
      _ = 25 * (n : ℝ) ^ 16 := by rw [← hpower2]

end AKLT.W.GAP055

#print axioms AKLT.W.GAP055.main
