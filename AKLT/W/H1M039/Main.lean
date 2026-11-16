import AKLT.Blueprint.H1.NodesSector

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M039

private def lowerIter (J : Finset (Fin 20)) : Nat → TensorSpace J → TensorSpace J
  | 0, v => v
  | n + 1, v => totalSpinMinus J (lowerIter J n v)

private def raiseIter (J : Finset (Fin 20)) : Nat → TensorSpace J → TensorSpace J
  | 0, v => v
  | n + 1, v => totalSpinPlus J (raiseIter J n v)

private def lowerWeight : Nat → ℝ → ℝ
  | 0, m => m
  | n + 1, m => lowerWeight n m - 1

private def raiseWeight : Nat → ℝ → ℝ
  | 0, m => m
  | n + 1, m => raiseWeight n m + 1

private theorem lowerWeight_eq_sub (n : ℕ) (m : ℝ) :
    lowerWeight n m = m - (n : ℝ) := by
  induction n with
  | zero => simp [lowerWeight]
  | succ n ih =>
      rw [lowerWeight, ih]
      simp [Nat.cast_succ]
      ring

private theorem raiseWeight_eq_add (n : ℕ) (m : ℝ) :
    raiseWeight n m = m + (n : ℝ) := by
  induction n with
  | zero => simp [raiseWeight]
  | succ n ih =>
      rw [raiseWeight, ih]
      simp [Nat.cast_succ]
      ring

private theorem lowerIter_spec (J : Finset (Fin 20)) (S : Submodule ℂ (TensorSpace J))
    (O : Module.End ℂ (TensorSpace J)) (μ : ℂ) (m : ℝ) (v : TensorSpace J)
    (n : ℕ)
    (hS : ∀ ψ ∈ S, totalSpinMinus J ψ ∈ S)
    (hcomm : ∀ ψ ∈ S, O (totalSpinMinus J ψ) = totalSpinMinus J (O ψ))
    (hL : WeightLadder J)
    (hsteps : ∀ i, i < n → 0 < lowerWeight i m)
    (hvS : v ∈ S) (hv0 : v ≠ 0) (hOv : O v = μ • v)
    (hZv : totalSpinZ J v = (m : ℂ) • v) :
    lowerIter J n v ∈ S ∧ lowerIter J n v ≠ 0 ∧
      O (lowerIter J n v) = μ • lowerIter J n v ∧
      totalSpinZ J (lowerIter J n v) = (lowerWeight n m : ℂ) • lowerIter J n v := by
  induction n with
  | zero =>
      simpa [lowerIter, lowerWeight] using And.intro hvS (And.intro hv0 (And.intro hOv hZv))
  | succ n ih =>
      have hsteps' : ∀ i, i < n → 0 < lowerWeight i m := by
        intro i hi
        exact hsteps i (Nat.lt_trans hi (Nat.lt_succ_self n))
      have hu := ih hsteps'
      rcases hu with ⟨huS, hu0, huO, huZ⟩
      have hstep := hsteps n (Nat.lt_succ_self n)
      have hlad := hL (lowerIter J n v) (lowerWeight n m) huZ
      rcases hlad with ⟨_, hminusZ, hminusNZ, _⟩
      have hnext0 : totalSpinMinus J (lowerIter J n v) ≠ 0 := hminusNZ hu0 hstep
      have hnextS : totalSpinMinus J (lowerIter J n v) ∈ S := hS _ huS
      have hnextO : O (totalSpinMinus J (lowerIter J n v)) =
          μ • totalSpinMinus J (lowerIter J n v) := by
        rw [hcomm _ huS, huO]
        simp
      have hnextZ : totalSpinZ J (totalSpinMinus J (lowerIter J n v)) =
          (lowerWeight (n + 1) m : ℂ) • totalSpinMinus J (lowerIter J n v) := by
        simpa [lowerWeight] using hminusZ
      simpa [lowerIter] using And.intro hnextS
        (And.intro hnext0 (And.intro hnextO hnextZ))

private theorem raiseIter_spec (J : Finset (Fin 20)) (S : Submodule ℂ (TensorSpace J))
    (O : Module.End ℂ (TensorSpace J)) (μ : ℂ) (m : ℝ) (v : TensorSpace J)
    (n : ℕ)
    (hS : ∀ ψ ∈ S, totalSpinPlus J ψ ∈ S)
    (hcomm : ∀ ψ ∈ S, O (totalSpinPlus J ψ) = totalSpinPlus J (O ψ))
    (hL : WeightLadder J)
    (hsteps : ∀ i, i < n → raiseWeight i m < 0)
    (hvS : v ∈ S) (hv0 : v ≠ 0) (hOv : O v = μ • v)
    (hZv : totalSpinZ J v = (m : ℂ) • v) :
    raiseIter J n v ∈ S ∧ raiseIter J n v ≠ 0 ∧
      O (raiseIter J n v) = μ • raiseIter J n v ∧
      totalSpinZ J (raiseIter J n v) = (raiseWeight n m : ℂ) • raiseIter J n v := by
  induction n with
  | zero =>
      simpa [raiseIter, raiseWeight] using And.intro hvS (And.intro hv0 (And.intro hOv hZv))
  | succ n ih =>
      have hsteps' : ∀ i, i < n → raiseWeight i m < 0 := by
        intro i hi
        exact hsteps i (Nat.lt_trans hi (Nat.lt_succ_self n))
      have hu := ih hsteps'
      rcases hu with ⟨huS, hu0, huO, huZ⟩
      have hstep := hsteps n (Nat.lt_succ_self n)
      have hlad := hL (raiseIter J n v) (raiseWeight n m) huZ
      rcases hlad with ⟨hplusZ, _, _, hplusNZ⟩
      have hnext0 : totalSpinPlus J (raiseIter J n v) ≠ 0 := hplusNZ hu0 hstep
      have hnextS : totalSpinPlus J (raiseIter J n v) ∈ S := hS _ huS
      have hnextO : O (totalSpinPlus J (raiseIter J n v)) =
          μ • totalSpinPlus J (raiseIter J n v) := by
        rw [hcomm _ huS, huO]
        simp
      have hnextZ : totalSpinZ J (totalSpinPlus J (raiseIter J n v)) =
          (raiseWeight (n + 1) m : ℂ) • totalSpinPlus J (raiseIter J n v) := by
        simpa [raiseWeight] using hplusZ
      simpa [raiseIter] using And.intro hnextS
        (And.intro hnext0 (And.intro hnextO hnextZ))

theorem main : AKLT.Blueprint.H1.LadderWalkStatement := by
  intro J S κ hκ hstable hL O hcommPlus hcommMinus μ v hvS hv0 hOv m hZv hz
  rcases hz with ⟨z, hz⟩
  rcases hstable with ⟨_, hstablePlus, hstableMinus⟩
  have hκnonneg : 0 ≤ κ := by
    rcases hκ with h | h
    · simp [h]
    · rw [h]
      norm_num
  have hκle : κ ≤ 1 / 2 := by
    rcases hκ with h | h
    · norm_num [h]
    · exact le_of_eq h
  by_cases hzNonneg : 0 ≤ z
  · let n : ℕ := z.toNat
    have hzCast : (n : ℤ) = z := by
      simpa [n] using Int.toNat_of_nonneg hzNonneg
    have hm' : m = κ + (n : ℝ) := by
      calc
        m = κ + (z : ℝ) := hz
        _ = κ + (n : ℝ) := by rw [← hzCast]; simp
    have hsteps : ∀ i, i < n → 0 < lowerWeight i m := by
      intro i hi
      have hiReal : (i : ℝ) < (n : ℝ) := by exact_mod_cast hi
      rw [lowerWeight_eq_sub, hm']
      linarith
    have hwalk := lowerIter_spec J S O μ m v n hstableMinus hcommMinus hL hsteps
      hvS hv0 hOv hZv
    have hfinish : lowerWeight n m = κ := by
      rw [lowerWeight_eq_sub, hm']
      ring
    refine ⟨lowerIter J n v, hwalk.1, hwalk.2.1, hwalk.2.2.1, ?_⟩
    calc
      totalSpinZ J (lowerIter J n v) = (lowerWeight n m : ℂ) • lowerIter J n v := hwalk.2.2.2
      _ = (κ : ℂ) • lowerIter J n v := by
        rw [hfinish]
  · have hzNeg : z < 0 := lt_of_not_ge hzNonneg
    let n : ℕ := (-z).toNat
    have hnegCast : (n : ℤ) = -z := by
      simpa [n] using Int.toNat_of_nonneg (le_of_lt (neg_pos.mpr hzNeg))
    have hzCast : z = -(n : ℤ) := by omega
    have hm' : m = κ - (n : ℝ) := by
      calc
        m = κ + (z : ℝ) := hz
        _ = κ - (n : ℝ) := by
          rw [hzCast]
          simp only [Int.cast_neg, Int.cast_natCast]
          ring
    have hsteps : ∀ i, i < n → raiseWeight i m < 0 := by
      intro i hi
      have hiReal : (i : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt hi)
      rw [raiseWeight_eq_add, hm']
      linarith
    have hwalk := raiseIter_spec J S O μ m v n hstablePlus hcommPlus hL hsteps
      hvS hv0 hOv hZv
    have hfinish : raiseWeight n m = κ := by
      rw [raiseWeight_eq_add, hm']
      ring
    refine ⟨raiseIter J n v, hwalk.1, hwalk.2.1, hwalk.2.2.1, ?_⟩
    calc
      totalSpinZ J (raiseIter J n v) = (raiseWeight n m : ℂ) • raiseIter J n v := hwalk.2.2.2
      _ = (κ : ℂ) • raiseIter J n v := by
        rw [hfinish]

end AKLT.W.H1M039

