module
public import AKLT.Blueprint.Gap.NodesPeriodic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

open AKLT.Defs AKLT.Challenge
open AKLT.Blueprint.Gap
namespace AKLT.W.GAP029

private def centreOf {L N : Size} (x : Site L N) (z : Plane) : Site L N :=
  x - reduction L N z

private theorem offsetSquare_card (r : ℕ) :
    (square (0, 0) r).card = (2 * r + 1)^2 := by
  simp only [square, Finset.product_eq_sprod, Finset.card_product, Int.card_Icc]
  have htn : (0 + (r : ℤ) + 1 - (0 - (r : ℤ))).toNat = 2*r+1 := by
    rw [show 0 + (r : ℤ) + 1 - (0 - (r : ℤ)) = (↑(2*r+1) : ℤ) by
      push_cast
      ring]
    rw [Int.toNat_natCast]
  rw [htn]
  ring

private theorem centreOf_injOn {L N : Size} (M : ℕ) (x : Site L N)
    (hL : 2*M+3 ≤ L.val) (hN : 2*M+3 ≤ N.val) :
    Set.InjOn (centreOf (L := L) (N := N) x)
      (↑(square (0, 0) (M+1)) : Set Plane) := by
  intro z hz w hw hzw
  have hred : reduction L N z = reduction L N w := by
    have h := congrArg (fun y : Site L N => x - y) hzw
    simpa [centreOf, sub_sub_cancel] using h
  have hfst : (z.1 : ZMod L.val) = (w.1 : ZMod L.val) := congrArg Prod.fst hred
  have hsnd : (z.2 : ZMod N.val) = (w.2 : ZMod N.val) := congrArg Prod.snd hred
  have hzprod := Finset.mem_product.mp hz
  have hwprod := Finset.mem_product.mp hw
  have hz1 := Finset.mem_Icc.mp hzprod.1
  have hz2 := Finset.mem_Icc.mp hzprod.2
  have hw1 := Finset.mem_Icc.mp hwprod.1
  have hw2 := Finset.mem_Icc.mp hwprod.2
  have hLmod : z.1 ≡ w.1 [ZMOD (L.val : ℤ)] := by
    exact (ZMod.intCast_eq_intCast_iff z.1 w.1 L.val).mp hfst
  have hNmod : z.2 ≡ w.2 [ZMOD (N.val : ℤ)] := by
    exact (ZMod.intCast_eq_intCast_iff z.2 w.2 N.val).mp hsnd
  have hLdiv : (L.val : ℤ) ∣ z.1 - w.1 := Int.modEq_iff_dvd.mp hLmod.symm
  have hNdiv : (N.val : ℤ) ∣ z.2 - w.2 := Int.modEq_iff_dvd.mp hNmod.symm
  have hLlarge : (2 * ((M+1 : ℕ) : ℤ)) < (L.val : ℤ) := by omega
  have hNlarge : (2 * ((M+1 : ℕ) : ℤ)) < (N.val : ℤ) := by omega
  have hz1zero : z.1 - w.1 = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hLdiv
    rw [abs_lt]
    constructor <;> omega
  have hz2zero : z.2 - w.2 = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hNdiv
    rw [abs_lt]
    constructor <;> omega
  exact Prod.ext (sub_eq_zero.mp hz1zero) (sub_eq_zero.mp hz2zero)

private theorem centres_filter_eq_image {L N : Size} (x : Site L N) (r : ℕ) :
    (Finset.univ.filter fun a : Site L N => x ∈ torusSquare L N r a) =
      (square (0, 0) r).image (centreOf (L := L) (N := N) x) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hxa
    change x ∈ (square (0, 0) r).image (fun z => a + reduction L N z) at hxa
    rw [Finset.mem_image] at hxa
    rcases hxa with ⟨z, hz, hzx⟩
    apply Finset.mem_image.mpr
    refine ⟨z, hz, ?_⟩
    dsimp [centreOf]
    exact ((eq_sub_iff_add_eq).2 hzx).symm
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨z, hz, hza⟩
    change x ∈ (square (0, 0) r).image (fun z => a + reduction L N z)
    apply Finset.mem_image.mpr
    refine ⟨z, hz, ?_⟩
    rw [← hza]
    simp [centreOf]

private theorem exterior_filter_eq_image_sdiff {L N : Size} (x : Site L N) (M : ℕ) :
    (Finset.univ.filter fun a : Site L N =>
      x ∈ torusHalo L N M a \ torusSquare L N M a) =
      (square (0, 0) (M+1)).image (centreOf (L := L) (N := N) x) \
        (square (0, 0) M).image (centreOf (L := L) (N := N) x) := by
  have hH := centres_filter_eq_image (L := L) (N := N) x (M+1)
  have hQ := centres_filter_eq_image (L := L) (N := N) x M
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  change (x ∈ torusSquare L N (M+1) a ∧ ¬ x ∈ torusSquare L N M a) ↔ _
  rw [← hH, ← hQ]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem main : AKLT.Blueprint.Gap.ExteriorBlockCountStatement := by
  intro L N M hM hL hN x
  have hinj := centreOf_injOn (L := L) (N := N) M x hL hN
  have hsub : square (0, 0) M ⊆ square (0, 0) (M+1) := by
    change Finset.Icc (0 - (M : ℤ)) (0 + M) ×ˢ Finset.Icc (0 - (M : ℤ)) (0 + M) ⊆
      Finset.Icc (0 - ((M+1 : ℕ) : ℤ)) (0 + (M+1 : ℤ)) ×ˢ
        Finset.Icc (0 - ((M+1 : ℕ) : ℤ)) (0 + (M+1 : ℤ))
    apply Finset.product_subset_product
    · intro z hz
      simp only [Finset.mem_Icc] at hz ⊢
      constructor <;> omega
    · intro z hz
      simp only [Finset.mem_Icc] at hz ⊢
      constructor <;> omega
  rw [exterior_filter_eq_image_sdiff (L := L) (N := N) x M]
  rw [← Finset.image_sdiff_of_injOn (s := square (0, 0) (M+1))
    (t := square (0, 0) M) hinj hsub]
  have hinjAnn : Set.InjOn (centreOf (L := L) (N := N) x)
      (↑(square (0, 0) (M+1) \ square (0, 0) M) : Set Plane) :=
    Set.InjOn.mono (Finset.coe_subset.mpr Finset.sdiff_subset) hinj
  rw [Finset.card_image_iff.mpr hinjAnn]
  rw [Finset.card_sdiff_of_subset hsub, offsetSquare_card, offsetSquare_card]
  unfold AKLT.Blueprint.Gap.haloCount
  have hsquare : (2 * (M+1) + 1)^2 = (2*M+1)^2 + (8*M+8) := by ring
  omega

#print axioms main

end AKLT.W.GAP029
