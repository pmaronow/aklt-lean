module
public import AKLT.Blueprint.Win.NodesTaper

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Win

namespace AKLT.W.WIN043

private lemma eq_of_supDist_eq_zero {x c : Plane} (h : supDist x c = 0) : x = c := by
  unfold supDist at h
  have hc := (Nat.max_eq_zero_iff.mp h)
  apply Prod.ext <;> omega

private lemma sphere_card_le_one_of_nonpos (c : Plane) {r : ℤ} (hr : r ≤ 0) :
    (sphere c r).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  change x ∈ (square c r.toNat).filter (fun z => (supDist z c : ℤ) = r) at hx
  change y ∈ (square c r.toNat).filter (fun z => (supDist z c : ℤ) = r) at hy
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  have hr0 : r = 0 := by
    have hnonneg : 0 ≤ (supDist x c : ℤ) := by positivity
    omega
  have hx0 : supDist x c = 0 := by exact_mod_cast hx'.trans hr0
  have hy0 : supDist y c = 0 := by exact_mod_cast hy'.trans hr0
  exact (eq_of_supDist_eq_zero hx0).trans (eq_of_supDist_eq_zero hy0).symm

private lemma mem_sphere_of_supDist_eq {x c : Plane} {r : ℤ}
    (hr : 0 ≤ r) (hd : (supDist x c : ℤ) = r) : x ∈ sphere c r := by
  classical
  have hrt : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr
  have hsup : supDist x c = r.toNat := by
    exact_mod_cast hd.trans hrt.symm
  have h1n : (x.1 - c.1).natAbs ≤ r.toNat := by
    unfold supDist at hsup
    exact (Nat.le_max_left _ _).trans_eq hsup
  have h2n : (x.2 - c.2).natAbs ≤ r.toNat := by
    unfold supDist at hsup
    exact (Nat.le_max_right _ _).trans_eq hsup
  have h1i : ((x.1 - c.1).natAbs : ℤ) ≤ r := by
    have h := (Int.ofNat_le).2 h1n
    simpa [hrt, Int.natCast_natAbs] using h
  have h2i : ((x.2 - c.2).natAbs : ℤ) ≤ r := by
    have h := (Int.ofNat_le).2 h2n
    simpa [hrt, Int.natCast_natAbs] using h
  have h1abs : |x.1 - c.1| ≤ r := by simpa [Int.natCast_natAbs] using h1i
  have h2abs : |x.2 - c.2| ≤ r := by simpa [Int.natCast_natAbs] using h2i
  change x ∈ (square c r.toNat).filter (fun z => (supDist z c : ℤ) = r)
  apply Finset.mem_filter.mpr
  refine ⟨?_, hd⟩
  change x ∈ Finset.Icc (c.1 - (r.toNat : ℤ)) (c.1 + r.toNat) ×ˢ
    Finset.Icc (c.2 - (r.toNat : ℤ)) (c.2 + r.toNat)
  simp only [Finset.mem_product, Finset.mem_Icc]
  constructor
  · constructor <;> omega
  · constructor <;> omega

theorem main : AKLT.Blueprint.Win.RawLayerCountStatement := by
  classical
  intro a y u i hsetup hNoCoinc hRawRange hSquareIntersection j hj
  let k : ℤ := shellRadius u i
  let jz : ℤ := j
  let radii : Finset ℤ := {k - jz, k + jz}
  let levels : Finset ℤ := {30 + jz, 31 + jz}
  let cover : Finset Plane := radii.biUnion fun r =>
    levels.biUnion fun h => sphere y r ∩ sphere a ((u : ℤ) + 1 - h)

  have hRadiiCard : radii.card ≤ 2 := by
    dsimp [radii]
    calc
      (insert (k - jz) {k + jz} : Finset ℤ).card ≤ ({k + jz} : Finset ℤ).card + 1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp
  have hLevelsCard : levels.card ≤ 2 := by
    dsimp [levels]
    calc
      (insert (30 + jz) {31 + jz} : Finset ℤ).card ≤ ({31 + jz} : Finset ℤ).card + 1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp

  have hIntersection : ∀ r ∈ radii, ∀ h ∈ levels,
      (sphere y r ∩ sphere a ((u : ℤ) + 1 - h)).card ≤ 8 := by
    intro r hr h hh
    by_cases hrpos : 0 < r
    · by_cases hRpos : 0 < (u : ℤ) + 1 - h
      · have hrchoice : r = k - jz ∨ r = k + jz := by
          simpa [radii] using hr
        have hhchoice : h = 30 + jz ∨ h = 31 + jz := by
          simpa [levels] using hh
        have hlevel : 30 + (j : ℤ) ≤ h ∧ h < 32 + (j : ℤ) := by
          rcases hhchoice with hEq | hEq <;> omega
        have hradChoice : r = shellRadius u i - (j : ℤ) ∨
            r = shellRadius u i + (j : ℤ) := by
          simpa [k, jz] using hrchoice
        have hnc : ∀ axis : Fin 2, ∀ ε δ : ℤ, SignedUnit ε → SignedUnit δ →
            coord axis y + ε * r ≠ coord axis a + δ * ((u : ℤ) + 1 - h) := by
          intro axis ε δ hε hδ
          exact hNoCoinc j hj h hlevel.1 hlevel.2 r hradChoice axis ε δ hε hδ
        exact hSquareIntersection a y r ((u : ℤ) + 1 - h) hrpos hRpos hnc
      · have hcard := Finset.card_le_card
          (Finset.inter_subset_right : sphere y r ∩ sphere a ((u : ℤ) + 1 - h) ⊆
            sphere a ((u : ℤ) + 1 - h))
        have hone := sphere_card_le_one_of_nonpos a (le_of_not_gt hRpos)
        omega
    · have hcard := Finset.card_le_card
        (Finset.inter_subset_left : sphere y r ∩ sphere a ((u : ℤ) + 1 - h) ⊆ sphere y r)
      have hone := sphere_card_le_one_of_nonpos y (le_of_not_gt hrpos)
      omega

  have hInner : ∀ r ∈ radii,
      (levels.biUnion fun h => sphere y r ∩ sphere a ((u : ℤ) + 1 - h)).card ≤ 16 := by
    intro r hr
    calc
      (levels.biUnion fun h => sphere y r ∩ sphere a ((u : ℤ) + 1 - h)).card ≤
          ∑ h ∈ levels, (sphere y r ∩ sphere a ((u : ℤ) + 1 - h)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _h ∈ levels, 8 := by
        apply Finset.sum_le_sum
        intro h hh
        exact hIntersection r hr h hh
      _ = levels.card * 8 := by simp [Finset.sum_const]
      _ ≤ 2 * 8 := Nat.mul_le_mul_right 8 hLevelsCard
      _ = 16 := by norm_num

  have hCoverCard : cover.card ≤ 32 := by
    calc
      cover.card ≤ ∑ r ∈ radii,
          (levels.biUnion fun h => sphere y r ∩ sphere a ((u : ℤ) + 1 - h)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ radii, 16 := by
        apply Finset.sum_le_sum
        intro r hr
        exact hInner r hr
      _ = radii.card * 16 := by simp [Finset.sum_const]
      _ ≤ 2 * 16 := Nat.mul_le_mul_right 16 hRadiiCard
      _ = 32 := by norm_num

  have hSubset :
      (cutRaw a y u i).filter (fun x => radialOffset y u i x = j) ⊆ cover := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxRaw, hxj⟩
    have hjNear : (radialOffset y u i x : ℝ) ≤ shellSpacing u / 12 := by
      simpa [hxj] using hj
    obtain ⟨hlo, hhi⟩ := hRawRange x hxRaw hjNear
    let h : ℤ := squareDepth a u x
    have hhRange : 30 + jz ≤ h ∧ h < 32 + jz := by
      simpa [h, jz, hxj] using And.intro hlo hhi
    have hLevelCase : h = 30 + jz ∨ h = 31 + jz := by omega

    have hradNat : radialOffset y u i x = j := hxj
    have hradAbs : ((supDist x y : ℤ) - k).natAbs = j := by
      simpa [radialOffset, k] using hradNat
    have hradCase : (supDist x y : ℤ) = k - jz ∨
        (supDist x y : ℤ) = k + jz := by
      rcases (Int.natAbs_eq_iff.mp hradAbs) with hpos | hneg
      · right
        dsimp [jz]
        omega
      · left
        dsimp [jz]
        omega

    have hDepthMax : max 0 ((u : ℤ) + 1 - (supDist x a : ℤ)) = h := by
      change squareDepth a u x = h
      rfl
    have hDepthPos : 0 < h := by omega
    have hInnerPos : 0 < (u : ℤ) + 1 - (supDist x a : ℤ) := by
      by_contra hn
      have hzero : max 0 ((u : ℤ) + 1 - (supDist x a : ℤ)) = 0 :=
        max_eq_left (le_of_not_gt hn)
      rw [hzero] at hDepthMax
      omega
    have hDepthEq : (supDist x a : ℤ) = (u : ℤ) + 1 - h := by
      rw [max_eq_right (le_of_lt hInnerPos)] at hDepthMax
      omega
    rcases hradCase with hrminus | hrplus
    · rcases hLevelCase with hlow | hhigh
      · have hRadNonneg : 0 ≤ k - jz := by rw [← hrminus]; positivity
        have hxSphereY : x ∈ sphere y (k - jz) :=
          mem_sphere_of_supDist_eq hRadNonneg hrminus
        have hxSphereA : x ∈ sphere a ((u : ℤ) + 1 - (30 + jz)) := by
          rw [hlow] at hDepthEq
          exact mem_sphere_of_supDist_eq (by omega) hDepthEq
        change x ∈ radii.biUnion (fun r => levels.biUnion fun h =>
          sphere y r ∩ sphere a ((u : ℤ) + 1 - h))
        apply Finset.mem_biUnion.mpr
        refine ⟨k - jz, ?_, Finset.mem_biUnion.mpr ⟨30 + jz, ?_, ?_⟩⟩
        · simp [radii]
        · simp [levels]
        · exact Finset.mem_inter.mpr ⟨hxSphereY, hxSphereA⟩
      · have hRadNonneg : 0 ≤ k - jz := by rw [← hrminus]; positivity
        have hxSphereY : x ∈ sphere y (k - jz) :=
          mem_sphere_of_supDist_eq hRadNonneg hrminus
        have hxSphereA : x ∈ sphere a ((u : ℤ) + 1 - (31 + jz)) := by
          rw [hhigh] at hDepthEq
          exact mem_sphere_of_supDist_eq (by omega) hDepthEq
        change x ∈ radii.biUnion (fun r => levels.biUnion fun h =>
          sphere y r ∩ sphere a ((u : ℤ) + 1 - h))
        apply Finset.mem_biUnion.mpr
        refine ⟨k - jz, ?_, Finset.mem_biUnion.mpr ⟨31 + jz, ?_, ?_⟩⟩
        · simp [radii]
        · simp [levels]
        · exact Finset.mem_inter.mpr ⟨hxSphereY, hxSphereA⟩
    · rcases hLevelCase with hlow | hhigh
      · have hRadNonneg : 0 ≤ k + jz := by rw [← hrplus]; positivity
        have hxSphereY : x ∈ sphere y (k + jz) :=
          mem_sphere_of_supDist_eq hRadNonneg hrplus
        have hxSphereA : x ∈ sphere a ((u : ℤ) + 1 - (30 + jz)) := by
          rw [hlow] at hDepthEq
          exact mem_sphere_of_supDist_eq (by omega) hDepthEq
        change x ∈ radii.biUnion (fun r => levels.biUnion fun h =>
          sphere y r ∩ sphere a ((u : ℤ) + 1 - h))
        apply Finset.mem_biUnion.mpr
        refine ⟨k + jz, ?_, Finset.mem_biUnion.mpr ⟨30 + jz, ?_, ?_⟩⟩
        · simp [radii]
        · simp [levels]
        · exact Finset.mem_inter.mpr ⟨hxSphereY, hxSphereA⟩
      · have hRadNonneg : 0 ≤ k + jz := by rw [← hrplus]; positivity
        have hxSphereY : x ∈ sphere y (k + jz) :=
          mem_sphere_of_supDist_eq hRadNonneg hrplus
        have hxSphereA : x ∈ sphere a ((u : ℤ) + 1 - (31 + jz)) := by
          rw [hhigh] at hDepthEq
          exact mem_sphere_of_supDist_eq (by omega) hDepthEq
        change x ∈ radii.biUnion (fun r => levels.biUnion fun h =>
          sphere y r ∩ sphere a ((u : ℤ) + 1 - h))
        apply Finset.mem_biUnion.mpr
        refine ⟨k + jz, ?_, Finset.mem_biUnion.mpr ⟨31 + jz, ?_, ?_⟩⟩
        · simp [radii]
        · simp [levels]
        · exact Finset.mem_inter.mpr ⟨hxSphereY, hxSphereA⟩

  exact (Finset.card_le_card hSubset).trans (by omega)

end AKLT.W.WIN043

end
