module
public import AKLT.Blueprint.Win.NodesTaper

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN045

private theorem decay_le_natpow_of_depth_le_one
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (d : ℕ∞) (n : ℕ)
    (hn : n ≤ d.toNat) : decay θ d ≤ θ ^ n := by
  by_cases htop : d = ⊤
  · simp [decay, htop]
    positivity
  · simp only [decay, htop]
    rw [← Real.rpow_natCast θ d.toNat, ← Real.rpow_natCast θ n]
    have hn' : (n : ℝ) ≤ (d.toNat : ℝ) := by exact_mod_cast hn
    exact Real.rpow_le_rpow_of_exponent_ge hθ hθ1.le hn'

private theorem natpow_le_rpow_of_depth_ge
    (θ T : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (d : ℕ∞)
    (hdepth : T - 1 ≤ (d.toNat : ℝ)) :
    decay θ d ≤ θ ^ (T - 1) := by
  by_cases htop : d = ⊤
  · simp [decay, htop]
    positivity
  · simp only [decay, htop]
    rw [← Real.rpow_natCast θ d.toNat]
    exact Real.rpow_le_rpow_of_exponent_ge hθ hθ1.le hdepth

private theorem card_square_eq (a : Plane) (u : ℕ) :
    (square a u).card = (2 * u + 1) ^ 2 := by
  change (Finset.Icc (a.1 - (u : ℤ)) (a.1 + u) ×ˢ
    Finset.Icc (a.2 - (u : ℤ)) (a.2 + u)).card = _
  rw [Finset.card_product]
  have h₁ : (Finset.Icc (a.1 - (u : ℤ)) (a.1 + u)).card = 2 * u + 1 := by
    rw [Int.card_Icc]
    omega
  have h₂ : (Finset.Icc (a.2 - (u : ℤ)) (a.2 + u)).card = 2 * u + 1 := by
    rw [Int.card_Icc]
    omega
  rw [h₁, h₂]
  ring

theorem main : AKLT.Blueprint.Win.RawWeightSumStatement := by
  classical
  intro a y u i hsetup hcontain hdepth hfiber θ hθ hθ1 hseries hnearCost
  let R := cutRaw a y u i
  let off : Plane → ℕ := radialOffset y u i
  let T : ℝ := shellSpacing u / 12
  let near := R.filter fun x => (off x : ℝ) ≤ T
  let far := R.filter fun x => ¬ (off x : ℝ) ≤ T
  have hnear_point : ∀ x ∈ near,
      decay θ (boundaryDepth (cutVolume a y u i) x) ≤ θ ^ (max (off x) 16 - 2) := by
    intro x hx
    have hxR : x ∈ R := (Finset.mem_filter.mp hx).1
    have hxNear : (off x : ℝ) ≤ T := (Finset.mem_filter.mp hx).2
    exact decay_le_natpow_of_depth_le_one θ hθ hθ1
      (boundaryDepth (cutVolume a y u i) x) (max (off x) 16 - 2)
      ((hdepth x hxR).1 (by simpa [R, off, T] using hxNear))
  have hfar_point : ∀ x ∈ far,
      decay θ (boundaryDepth (cutVolume a y u i) x) ≤ θ ^ (T - 1) := by
    intro x hx
    have hxR : x ∈ R := (Finset.mem_filter.mp hx).1
    have hxFar : ¬ (off x : ℝ) ≤ T := (Finset.mem_filter.mp hx).2
    exact natpow_le_rpow_of_depth_ge θ T hθ hθ1
      (boundaryDepth (cutVolume a y u i) x)
      ((hdepth x hxR).2 (lt_of_not_ge hxFar))

  have hnear_sum :
      (∑ x ∈ near, decay θ (boundaryDepth (cutVolume a y u i) x)) ≤
        48 * (∑' j : ℕ, θ ^ (max j 16 - 2)) := by
    calc
      _ ≤ ∑ x ∈ near, θ ^ (max (off x) 16 - 2) :=
        Finset.sum_le_sum (fun x hx => hnear_point x hx)
      _ = ∑ j ∈ near.image off, ∑ x ∈ near with off x = j,
            θ ^ (max j 16 - 2) := by
          calc
            _ = ∑ j ∈ near.image off, ∑ x ∈ near with off x = j,
                  θ ^ (max (off x) 16 - 2) := by
                symm
                exact Finset.sum_fiberwise_of_maps_to
                  (s := near) (t := near.image off) (g := off)
                  (fun _ hx => Finset.mem_image_of_mem off hx)
                  (fun x => θ ^ (max (off x) 16 - 2))
            _ = ∑ j ∈ near.image off, ∑ x ∈ near with off x = j,
                  θ ^ (max j 16 - 2) := by
                apply Finset.sum_congr rfl
                intro j hj
                apply Finset.sum_congr rfl
                intro x hx
                rw [(Finset.mem_filter.mp hx).2]
      _ ≤ ∑ j ∈ near.image off, 48 * θ ^ (max j 16 - 2) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjT : (j : ℝ) ≤ T := by
            rcases Finset.mem_image.mp hj with ⟨x, hx, rfl⟩
            exact (Finset.mem_filter.mp hx).2
          have hcard : (near.filter fun x => off x = j).card ≤ 48 := by
            calc
              (near.filter fun x => off x = j).card ≤
                  (R.filter fun x => off x = j).card := Finset.card_le_card (by
                    intro x hx
                    have hx' := Finset.mem_filter.mp hx
                    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx'.1).1, hx'.2⟩)
              _ ≤ 48 := hfiber j (by simpa [T] using hjT)
          rw [show (∑ x ∈ near with off x = j, θ ^ (max j 16 - 2)) =
              ((near.filter fun x => off x = j).card : ℝ) *
                θ ^ (max j 16 - 2) by simp]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
            (by positivity)
      _ = 48 * (∑ j ∈ near.image off, θ ^ (max j 16 - 2)) := by
          rw [Finset.mul_sum]
      _ ≤ 48 * (∑' j : ℕ, θ ^ (max j 16 - 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact hseries.sum_le_tsum (near.image off) (by
            intro j hj
            positivity)

  have hfar_sum :
      (∑ x ∈ far, decay θ (boundaryDepth (cutVolume a y u i) x)) ≤ tailCost θ u := by
    calc
      _ ≤ ∑ x ∈ far, θ ^ (T - 1) :=
        Finset.sum_le_sum (fun x hx => hfar_point x hx)
      _ = (far.card : ℝ) * θ ^ (T - 1) := by simp
      _ ≤ ((square a u).card : ℝ) * θ ^ (T - 1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Finset.card_le_card (by
          intro x hx
          exact hcontain ((Finset.mem_filter.mp hx).1))
      _ ≤ 4 * (2 * (u : ℝ) + 1) ^ 2 * θ ^ (T - 1) := by
        rw [card_square_eq]
        have hu : 0 ≤ (2 * (u : ℝ) + 1) ^ 2 := by positivity
        have hfactor : ((2 * u + 1 : ℕ) : ℝ) ^ 2 ≤
            4 * (2 * (u : ℝ) + 1) ^ 2 := by
          push_cast
          nlinarith [sq_nonneg (2 * (u : ℝ) + 1)]
        exact mul_le_mul_of_nonneg_right (by simpa only [Nat.cast_pow] using hfactor)
          (by positivity)
      _ = tailCost θ u := by
        simp [tailCost, T]

  have hsplit :
      (∑ x ∈ R, decay θ (boundaryDepth (cutVolume a y u i) x)) =
        (∑ x ∈ near, decay θ (boundaryDepth (cutVolume a y u i) x)) +
        (∑ x ∈ far, decay θ (boundaryDepth (cutVolume a y u i) x)) := by
    simpa only [near, far, R] using
      (Finset.sum_filter_add_sum_filter_not (s := R)
        (p := fun x => (off x : ℝ) ≤ T)
        (f := fun x => decay θ (boundaryDepth (cutVolume a y u i) x))).symm
  calc
    (∑ x ∈ cutRaw a y u i, decay θ (boundaryDepth (cutVolume a y u i) x))
        ≤ 48 * (∑' j : ℕ, θ ^ (max j 16 - 2)) + tailCost θ u := by
          calc
            _ = (∑ x ∈ near, decay θ (boundaryDepth (cutVolume a y u i) x)) +
                (∑ x ∈ far, decay θ (boundaryDepth (cutVolume a y u i) x)) := by
                  simpa [R] using hsplit
            _ ≤ 48 * (∑' j : ℕ, θ ^ (max j 16 - 2)) + tailCost θ u :=
                  add_le_add hnear_sum hfar_sum
    _ ≤ nearCost θ + tailCost θ u := add_le_add hnearCost le_rfl

end AKLT.W.WIN045

#print axioms AKLT.W.WIN045.main
