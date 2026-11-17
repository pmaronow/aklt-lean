module
public import AKLT.Blueprint.Gap.NodesPeriodic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

open AKLT.Defs AKLT.Challenge
open AKLT.Blueprint.Gap

namespace AKLT.W.GAP028

private theorem reduction_injective_on_square (L N : Size) (M : ℕ)
    (hL : 2 * M + 3 ≤ L.val) (hN : 2 * M + 3 ≤ N.val) :
    Set.InjOn (reduction L N) (↑(square (0, 0) M) : Set Plane) := by
  intro z hz w hw h
  change z ∈ square (0, 0) M at hz
  change w ∈ square (0, 0) M at hw
  simp only [square, Finset.product_eq_sprod, Finset.mem_product] at hz hw
  rcases Finset.mem_Icc.mp hz.1 with ⟨hzlo1, hzhi1⟩
  rcases Finset.mem_Icc.mp hz.2 with ⟨hzlo2, hzhi2⟩
  rcases Finset.mem_Icc.mp hw.1 with ⟨hwlo1, hwhi1⟩
  rcases Finset.mem_Icc.mp hw.2 with ⟨hwlo2, hwhi2⟩
  have h1 : (z.1 : ZMod L.val) = (w.1 : ZMod L.val) := by
    exact congrArg Prod.fst h
  have h2 : (z.2 : ZMod N.val) = (w.2 : ZMod N.val) := by
    exact congrArg Prod.snd h
  have hdiv1 : (L.val : ℤ) ∣ w.1 - z.1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h1
  have hdiv2 : (N.val : ℤ) ∣ w.2 - z.2 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h2
  have hb1 : |w.1 - z.1| < (L.val : ℤ) := by
    have hsize : (2 * (M : ℤ)) < (L.val : ℤ) := by
      exact_mod_cast (show 2 * M < L.val by omega)
    apply abs_lt.mpr
    constructor <;> omega
  have hb2 : |w.2 - z.2| < (N.val : ℤ) := by
    have hsize : (2 * (M : ℤ)) < (N.val : ℤ) := by
      exact_mod_cast (show 2 * M < N.val by omega)
    apply abs_lt.mpr
    constructor <;> omega
  have hz1 : z.1 = w.1 := by
    have he := Int.eq_zero_of_abs_lt_dvd hdiv1 hb1
    omega
  have hz2 : z.2 = w.2 := by
    have he := Int.eq_zero_of_abs_lt_dvd hdiv2 hb2
    omega
  exact Prod.ext hz1 hz2

private theorem square_card (M : ℕ) : (square (0, 0) M).card = (2 * M + 1)^2 := by
  simp only [square, Int.zero_sub, Int.zero_add, Finset.product_eq_sprod]
  have hc : (Finset.Icc (-(M : ℤ)) (M : ℤ)).card = 2 * M + 1 := by
    have h := Int.card_Icc_of_le (a := -(M : ℤ)) (b := (M : ℤ)) (by omega)
    norm_cast at h ⊢
    omega
  rw [Finset.card_product]
  rw [hc]
  ring

theorem main : AKLT.Blueprint.Gap.ContainingBlockCountStatement := by
  intro L N M hM hL hN x
  let f : Plane → Site L N := fun z => x - reduction L N z
  have hf : Set.InjOn f (↑(square (0, 0) M) : Set Plane) := by
    intro z hz w hw hzw
    change x - reduction L N z = x - reduction L N w at hzw
    have hred : reduction L N z = reduction L N w := by
      calc
        reduction L N z = x - (x - reduction L N z) := by abel
        _ = x - (x - reduction L N w) := by rw [hzw]
        _ = reduction L N w := by abel
    exact reduction_injective_on_square L N M hL hN hz hw hred
  have hcenters :
      (Finset.univ.filter fun a : Site L N => x ∈ torusSquare L N M a) =
        (square (0, 0) M).image f := by
    classical
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      torusSquare]
    constructor
    · rintro ⟨z, hz, hx⟩
      refine ⟨z, hz, ?_⟩
      calc
        x - reduction L N z = (a + reduction L N z) - reduction L N z := by rw [hx]
        _ = a := by abel
    · rintro ⟨z, hz, ha⟩
      change x - reduction L N z = a at ha
      refine ⟨z, hz, ?_⟩
      calc
        a + reduction L N z = (x - reduction L N z) + reduction L N z := by rw [ha]
        _ = x := by simp
  rw [hcenters, Finset.card_image_of_injOn hf]
  rw [square_card, AKLT.Blueprint.Gap.volumeCount]

end AKLT.W.GAP028
