module
public import AKLT.Blueprint.Rec.NodesResponse

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC012

/-- Squared norm expansion for the scalar product used by the local estimates. -/
theorem normSq_add (u v : Vec3) :
    normSq (fun i => u i + v i) = normSq u + 2 * dot u v + normSq v := by
  unfold normSq dot
  calc
    (∑ i, (u i + v i) * (u i + v i)) =
        ∑ i, (u i * u i + 2 * (u i * v i) + v i * v i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i, u i * u i) + 2 * (∑ i, u i * v i) + (∑ i, v i * v i) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.mul_sum]

theorem normSq_sub (u v : Vec3) :
    normSq (fun i => u i - v i) = normSq u - 2 * dot u v + normSq v := by
  unfold normSq dot
  calc
    (∑ i, (u i - v i) * (u i - v i)) =
        ∑ i, (u i * u i - 2 * (u i * v i) + v i * v i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i, u i * u i) - 2 * (∑ i, u i * v i) + (∑ i, v i * v i) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp only [Finset.mul_sum]

theorem normSq_nonneg' (u : Vec3) : 0 ≤ normSq u := by
  unfold normSq dot
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))

theorem dot_add_left (u v w : Vec3) :
    dot (fun i => u i + v i) w = dot u w + dot v w := by
  unfold dot
  calc
    (∑ i, (u i + v i) * w i) = ∑ i, (u i * w i + v i * w i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i, u i * w i) + (∑ i, v i * w i) := Finset.sum_add_distrib

theorem dot_abs_le_one {u v : Vec3} (hu : normSq u ≤ 1) (hv : normSq v ≤ 1) :
    -1 ≤ dot u v ∧ dot u v ≤ 1 := by
  have hp := normSq_nonneg' (fun i => u i + v i)
  have hm := normSq_nonneg' (fun i => u i - v i)
  rw [normSq_add] at hp
  rw [normSq_sub] at hm
  constructor <;> nlinarith

/-- The pointwise three-neighbor comparison in §6: integrated U factor is
at least one half, while the post-step D factor is at most six fifths. -/
theorem threeNeighborLocalBounds (a b c : Vec3)
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) (hc : normSq c ≤ 1) :
    1 / 2 ≤ 1 + (dot a b + dot a c + dot b c) / 3 ∧
      1 + dot b c / 5 ≤ 6 / 5 := by
  have hsum : normSq (fun i => a i + b i + c i) =
      normSq a + normSq b + normSq c +
        2 * (dot a b + dot a c + dot b c) := by
    calc
      normSq (fun i => a i + b i + c i) =
          normSq (fun i => a i + b i) +
            2 * dot (fun i => a i + b i) c + normSq c := normSq_add _ _
      _ = _ := by rw [normSq_add, dot_add_left]; ring
  have hn := normSq_nonneg' (fun i => a i + b i + c i)
  have hab := (dot_abs_le_one ha hb)
  have hac := (dot_abs_le_one ha hc)
  have hbc := (dot_abs_le_one hb hc)
  constructor
  · rw [hsum] at hn
    nlinarith
  · nlinarith

theorem threeNeighborScalarComparison (a b c : Vec3)
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) (hc : normSq c ≤ 1) :
    1 + dot b c / 5 ≤
      (12 / 5 : ℝ) * (1 + (dot a b + dot a c + dot b c) / 3) := by
  have h := threeNeighborLocalBounds a b c ha hb hc
  nlinarith

/-- The two-neighbor version of the same pointwise estimate. -/
theorem twoNeighborLocalBound (a b : Vec3)
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    2 / 3 ≤ 1 + dot a b / 3 := by
  have h := dot_abs_le_one ha hb
  nlinarith

theorem twoNeighborScalarComparison (a b : Vec3)
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    1 ≤ (12 / 5 : ℝ) * (1 + dot a b / 3) := by
  have h := twoNeighborLocalBound a b ha hb
  nlinarith

theorem goldenRatio_sq :
    AKLT.Defs.goldenRatio ^ 2 = AKLT.Defs.goldenRatio + 1 := by
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  dsimp [AKLT.Defs.goldenRatio]
  nlinarith

theorem icoRadius_sq :
    AKLT.Defs.icoRadius ^ 2 = AKLT.Defs.goldenRatio + 2 := by
  dsimp [AKLT.Defs.icoRadius]
  have hphi : 0 ≤ AKLT.Defs.goldenRatio := by
    dsimp [AKLT.Defs.goldenRatio]
    positivity
  exact Real.sq_sqrt (by linarith)

theorem icoVector_normSq (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨a, b, c⟩
  have hphi : 0 ≤ AKLT.Defs.goldenRatio := by
    dsimp [AKLT.Defs.goldenRatio]
    positivity
  have hrpos : 0 < icoRadius := Real.sqrt_pos.2 (by linarith)
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [normSq, dot, icoVector, signValue, Fin.sum_univ_three] <;>
    field_simp [ne_of_gt hrpos] <;>
    nlinarith [goldenRatio_sq, icoRadius_sq]

theorem spinVector_normSq_le_one (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => simpa [spinVector] using le_of_eq (icoVector_normSq j)

theorem networkSpin_normSq_le_one {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) (x : Plane) :
    normSq (D.spins n x) ≤ 1 := by
  by_cases hx : x ∈ D.active
  · simp [Network.spins, hx, spinVector_normSq_le_one]
  · simp [Network.spins, hx, normSq, dot]

theorem network_partition_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (pinned : Bool) :
    0 ≤ D.partition τ pinned (fun _ => 1) := by
  classical
  unfold Network.partition
  simp only [mul_one]
  apply Finset.sum_nonneg
  intro n hn
  apply mul_nonneg
  · apply mul_nonneg
    · apply Finset.prod_nonneg
      intro x hx
      have hs : D.status x.val = .U ∨ D.status x.val = .D := by
        have hactive := x.property
        dsimp [Network.active] at hactive
        have hne : D.status x.val ≠ .X := (Finset.mem_filter.mp hactive).2
        cases hsx : D.status x.val with
        | U => exact Or.inl rfl
        | D => exact Or.inr rfl
        | X => exact (hne hsx).elim
      cases hs with
      | inl hU => cases n x with
        | none => simp [spinWeight, hU]
        | some _ => norm_num [spinWeight, hU]
      | inr hD => cases n x with
        | none => norm_num [spinWeight, hD]
        | some _ => norm_num [spinWeight, hD]
    · apply Finset.prod_nonneg
      intro e he
      have h := (dot_abs_le_one
        (networkSpin_normSq_le_one D n e.1)
        (networkSpin_normSq_le_one D n e.2)).1
      linarith
  · apply Finset.prod_nonneg
    intro e he
    by_cases hp : pinned = true ∧ e.val.1 ∈ D.active
    · simp only [ite_eq_left hp]
      have h := (dot_abs_le_one (le_of_eq (τ e).property)
        (networkSpin_normSq_le_one D n e.val.1)).1
      linarith
    · simp [hp]

end AKLT.W.REC012

end
