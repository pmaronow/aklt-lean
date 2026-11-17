module
public import AKLT.Blueprint.Gap.NodesPeriodic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap

namespace AKLT.W.GAP035

private theorem adjacent_cases (x y : Plane) (h : Adjacent x y) :
    y = (x.1 + 1, x.2) ∨ y = (x.1 - 1, x.2) ∨
    y = (x.1, x.2 + 1) ∨ y = (x.1, x.2 - 1) := by
  simp only [Adjacent, latticeDist] at h
  have hx : (x.1 - y.1).natAbs ≤ 1 := by omega
  have hy : (x.2 - y.2).natAbs ≤ 1 := by omega
  have hx' : (x.1 - y.1) ^ 2 ≤ 1 := by
    simpa using (Int.natAbs_le_iff_sq_le (a := x.1 - y.1) (b := (1 : ℤ))).mp hx
  have hy' : (x.2 - y.2) ^ 2 ≤ 1 := by
    simpa using (Int.natAbs_le_iff_sq_le (a := x.2 - y.2) (b := (1 : ℤ))).mp hy
  have hb₁ : -1 ≤ x.1 - y.1 ∧ x.1 - y.1 ≤ 1 := by
    constructor <;> nlinarith
  have hb₂ : -1 ≤ x.2 - y.2 ∧ x.2 - y.2 ≤ 1 := by
    constructor <;> nlinarith
  have hc : (x.1 - y.1).natAbs = 0 ∨ (x.2 - y.2).natAbs = 0 := by
    by_cases hzero : (x.1 - y.1).natAbs = 0
    · exact Or.inl hzero
    · right
      have hpos : 0 < (x.1 - y.1).natAbs := Nat.pos_of_ne_zero hzero
      omega
  rcases hc with hzero | hzero
  · have hz : x.1 - y.1 = 0 := Int.natAbs_eq_zero.mp hzero
    have hone : (x.2 - y.2).natAbs = 1 := by omega
    have hnz : x.2 - y.2 ≠ 0 := by
      intro hh
      rw [hh] at hone
      norm_num at hone
    have hsign : x.2 - y.2 = 1 ∨ x.2 - y.2 = -1 := by omega
    rcases hsign with hs | hs
    · right; right; right; apply Prod.ext <;> dsimp <;> omega
    · right; right; left; apply Prod.ext <;> dsimp <;> omega
  · have hz : x.2 - y.2 = 0 := Int.natAbs_eq_zero.mp hzero
    have hone : (x.1 - y.1).natAbs = 1 := by omega
    have hnz : x.1 - y.1 ≠ 0 := by
      intro hh
      rw [hh] at hone
      norm_num at hone
    have hsign : x.1 - y.1 = 1 ∨ x.1 - y.1 = -1 := by omega
    rcases hsign with hs | hs
    · right; left; apply Prod.ext <;> dsimp <;> omega
    · left; apply Prod.ext <;> dsimp <;> omega

private theorem square_mem (a x : Plane) (M : ℕ) :
    x ∈ square a M ↔
      a.1 - (M : ℤ) ≤ x.1 ∧ x.1 ≤ a.1 + M ∧
      a.2 - (M : ℤ) ≤ x.2 ∧ x.2 ≤ a.2 + M := by
  change ((x.1, x.2) ∈
    (Finset.Icc (a.1 - (M : ℤ)) (a.1 + M)).product
      (Finset.Icc (a.2 - (M : ℤ)) (a.2 + M))) ↔ _
  simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨h₁, h₃⟩
    rcases h₁ with ⟨h₁, h₂⟩
    rcases h₃ with ⟨h₃, h₄⟩
    exact ⟨by omega, h₂, h₃, h₄⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨by omega, h₂⟩, ⟨by omega, h₄⟩⟩

private theorem square_subset_succ (a : Plane) (M : ℕ) :
    square a M ⊆ square a (M + 1) := by
  intro x hx
  rw [square_mem] at hx ⊢
  simp only [Nat.cast_add, Nat.cast_one] at hx ⊢
  rcases hx with ⟨h₁, h₂, h₃, h₄⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

private theorem square_step_succ (a x : Plane) (M : ℕ) (hx : x ∈ square a M) :
    (x.1 + 1, x.2) ∈ square a (M + 1) ∧
    (x.1 - 1, x.2) ∈ square a (M + 1) ∧
    (x.1, x.2 + 1) ∈ square a (M + 1) ∧
    (x.1, x.2 - 1) ∈ square a (M + 1) := by
  simp_rw [square_mem] at hx ⊢
  simp only [Nat.cast_add, Nat.cast_one] at hx ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals omega

private theorem reduction_inj_on_halo {L N : Size} {M : ℕ} {a : Plane}
    (hinj : Set.InjOn (reduction L N) (↑(square a (M + 1)) : Set Plane))
    {x y : Plane} (hx : x ∈ square a (M + 1)) (hy : y ∈ square a (M + 1))
    (hxy : reduction L N x = reduction L N y) : x = y := by
  exact hinj (by simpa using hx) (by simpa using hy) hxy

private theorem reduction_image_iff {L N : Size} {M : ℕ} {a : Plane}
    (hinj : Set.InjOn (reduction L N) (↑(square a (M + 1)) : Set Plane))
    {x : Plane} (hx : x ∈ square a (M + 1)) :
    reduction L N x ∈ (square a M).image (reduction L N) ↔ x ∈ square a M := by
  constructor
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨y, hy, hred⟩
    have hy' : y ∈ square a (M + 1) := square_subset_succ a M hy
    have hxy : x = y := reduction_inj_on_halo hinj hx hy' hred.symm
    simpa [hxy] using hy
  · intro hmem
    exact Finset.mem_image.mpr ⟨x, hmem, rfl⟩

private theorem pair_eq_orient {α : Type} [DecidableEq α] (u v p q : α)
    (h : ({u, v} : Finset α) = {p, q}) :
    (u = p ∧ v = q) ∨ (u = q ∧ v = p) := by
  have hu : u = p ∨ u = q := by
    have hm : u ∈ ({p, q} : Finset α) := by rw [← h]; simp
    simpa using hm
  have hv : v = p ∨ v = q := by
    have hm : v ∈ ({p, q} : Finset α) := by rw [← h]; simp
    simpa using hm
  have hp : p = u ∨ p = v := by
    have hm : p ∈ ({u, v} : Finset α) := by rw [h]; simp
    simpa using hm
  have hq : q = u ∨ q = v := by
    have hm : q ∈ ({u, v} : Finset α) := by rw [h]; simp
    simpa using hm
  grind

private theorem nextSite_ne {L N : Size} (e : Bond L N) :
    e.1 ≠ nextSite e.1 e.2 := by
  by_cases hd : e.2 = 0
  · intro h
    have hone : (1 : ZMod L.val) = 0 := by
      have hcoord := congrArg Prod.fst h
      have hsub := congrArg (fun z : ZMod L.val => z - e.1.1) hcoord
      simpa [nextSite, hd] using hsub.symm
    have hone' : (↑(1 : ℕ) : ZMod L.val) = 0 := by simpa using hone
    have hdiv : L.val ∣ 1 := (ZMod.natCast_eq_zero_iff 1 L.val).mp hone'
    have : L.val = 1 := Nat.dvd_one.mp hdiv
    omega
  · intro h
    have hone : (1 : ZMod N.val) = 0 := by
      have hcoord := congrArg Prod.snd h
      have hsub := congrArg (fun z : ZMod N.val => z - e.1.2) hcoord
      simpa [nextSite, hd] using hsub.symm
    have hone' : (↑(1 : ℕ) : ZMod N.val) = 0 := by simpa using hone
    have hdiv : N.val ∣ 1 := (ZMod.natCast_eq_zero_iff 1 N.val).mp hone'
    have : N.val = 1 := Nat.dvd_one.mp hdiv
    omega

private theorem adjacent_of_positive_bond {L N : Size} {M : ℕ} {a : Plane}
    (hinj : Set.InjOn (reduction L N) (↑(square a (M + 1)) : Set Plane))
    {x y : Plane} (hx : x ∈ square a M) (hy : y ∈ square a M)
    (e : Bond L N) (hstart : e.1 = reduction L N x)
    (hend : nextSite e.1 e.2 = reduction L N y) : Adjacent x y := by
  have hhalo := square_step_succ a x M hx
  by_cases hd : e.2 = 0
  · rw [hd] at hend
    have hz : (x.1 + 1, x.2) ∈ square a (M + 1) := hhalo.1
    have hstep : reduction L N (x.1 + 1, x.2) = nextSite (reduction L N x) 0 := by
      simp [nextSite, reduction]
    have hred : reduction L N y = reduction L N (x.1 + 1, x.2) := by
      calc
        reduction L N y = nextSite e.1 0 := hend.symm
        _ = nextSite (reduction L N x) 0 := by rw [hstart]
        _ = reduction L N (x.1 + 1, x.2) := hstep.symm
    have hyz : y = (x.1 + 1, x.2) := reduction_inj_on_halo hinj
      (square_subset_succ a M hy) hz hred
    rw [hyz]
    norm_num [Adjacent, latticeDist]
  · have hd1 : e.2 = 1 := Fin.eq_one_of_ne_zero e.2 hd
    rw [hd1] at hend
    have hz : (x.1, x.2 + 1) ∈ square a (M + 1) := hhalo.2.2.1
    have hstep : reduction L N (x.1, x.2 + 1) = nextSite (reduction L N x) 1 := by
      simp [nextSite, reduction]
    have hred : reduction L N y = reduction L N (x.1, x.2 + 1) := by
      calc
        reduction L N y = nextSite e.1 1 := hend.symm
        _ = nextSite (reduction L N x) 1 := by rw [hstart]
        _ = reduction L N (x.1, x.2 + 1) := hstep.symm
    have hyz : y = (x.1, x.2 + 1) := reduction_inj_on_halo hinj
      (square_subset_succ a M hy) hz hred
    rw [hyz]
    norm_num [Adjacent, latticeDist]

theorem main : AKLT.Blueprint.Gap.LiftBondStatement := by
  intro L N M hM hL hN a hinj
  let Q : Finset (Site L N) := (square a M).image (reduction L N)
  have hinside : ∀ x ∈ square a (M + 1),
      (reduction L N x ∈ Q ↔ x ∈ square a M) := by
    intro x hx
    exact reduction_image_iff hinj hx
  have hinj' : ∀ {x y : Plane}, x ∈ square a (M + 1) → y ∈ square a (M + 1) →
      reduction L N x = reduction L N y → x = y := by
    intro x y hx hy hxy
    exact reduction_inj_on_halo hinj hx hy hxy
  refine ⟨?_, ?_, ?_⟩
  · intro x y hx hy
    constructor
    · intro hadj
      rcases adjacent_cases x y hadj with he | hw | hn | hs
      · subst y
        exact ⟨(reduction L N x, 0), by simp [bondSites, nextSite, reduction]⟩
      · subst y
        refine ⟨(reduction L N (x.1 - 1, x.2), 0), ?_⟩
        simpa [bondSites, nextSite, reduction] using
          (Finset.pair_comm (reduction L N (x.1 - 1, x.2)) (reduction L N x))
      · subst y
        exact ⟨(reduction L N x, 1), by simp [bondSites, nextSite, reduction]⟩
      · subst y
        refine ⟨(reduction L N (x.1, x.2 - 1), 1), ?_⟩
        simpa [bondSites, nextSite, reduction] using
          (Finset.pair_comm (reduction L N (x.1, x.2 - 1)) (reduction L N x))
    · rintro ⟨e, he⟩
      have hxy : reduction L N x ≠ reduction L N y := by
        intro hred
        have hxeq := hinj' (square_subset_succ a M hx) (square_subset_succ a M hy) hred
        subst y
        have hcardbond : (bondSites e).card = 2 := by
          simpa [bondSites] using (Finset.card_pair_eq_two_iff.mpr (nextSite_ne e))
        have hc := congrArg Finset.card he
        rw [hcardbond] at hc
        simp at hc
      have hor := pair_eq_orient e.1 (nextSite e.1 e.2) (reduction L N x)
        (reduction L N y) (by simpa [bondSites] using he)
      rcases hor with ⟨hstart, hend⟩ | ⟨hstart, hend⟩
      · exact adjacent_of_positive_bond hinj hx hy e hstart hend
      · have hrev := adjacent_of_positive_bond hinj hy hx e hstart hend
        have hnat₁ : (x.1 - y.1).natAbs = (y.1 - x.1).natAbs := by
          rw [show x.1 - y.1 = -(y.1 - x.1) by omega, Int.natAbs_neg]
        have hnat₂ : (x.2 - y.2).natAbs = (y.2 - x.2).natAbs := by
          rw [show x.2 - y.2 = -(y.2 - x.2) by omega, Int.natAbs_neg]
        rw [Adjacent, latticeDist] at hrev ⊢
        rw [← hnat₁, ← hnat₂] at hrev
        exact hrev
  · intro e hcard
    have hcard' : ({e.1, nextSite e.1 e.2} ∩ Q).card = 1 := by
      simpa [bondSites] using hcard
    by_cases hstart : e.1 ∈ Q
    · have hend : nextSite e.1 e.2 ∉ Q := by
        by_contra hcontra
        have hpaircard : ({e.1, nextSite e.1 e.2} : Finset _).card = 2 :=
          Finset.card_pair_eq_two_iff.mpr (nextSite_ne e)
        simp [hstart, hcontra] at hcard'
        rw [hpaircard] at hcard'
        omega
      rcases Finset.mem_image.mp (show e.1 ∈ (square a M).image (reduction L N) by
        simpa [Q] using hstart) with ⟨x, hx, hxr⟩
      have hxhalo : x ∈ square a (M + 1) := square_subset_succ a M hx
      have hstep := square_step_succ a x M hx
      by_cases hd : e.2 = 0
      · let y : Plane := (x.1 + 1, x.2)
        have hstart' : e.1 = reduction L N x := hxr.symm
        have hyr : reduction L N y = nextSite e.1 e.2 := by
          rw [hd]
          simp [y, hstart', nextSite, reduction]
        have hyhalo : y ∈ square a (M + 1) := by simpa [y] using hstep.1
        have hyout : y ∉ square a M := by
          intro hy
          have : reduction L N y ∈ Q := (hinside y hyhalo).2 hy
          exact hend (by simpa [hyr] using this)
        have hyset : y ∈ square a (M + 1) \ square a M :=
          Finset.mem_sdiff.mpr ⟨hyhalo, hyout⟩
        refine ⟨x, hx, y, hyset, ?_, ?_⟩
        · norm_num [Adjacent, latticeDist, y]
        · simp [bondSites, hstart', hyr]
      · have hd1 : e.2 = 1 := Fin.eq_one_of_ne_zero e.2 hd
        let y : Plane := (x.1, x.2 + 1)
        have hstart' : e.1 = reduction L N x := hxr.symm
        have hyr : reduction L N y = nextSite e.1 e.2 := by
          rw [hd1]
          simp [y, hstart', nextSite, reduction]
        have hyhalo : y ∈ square a (M + 1) := by simpa [y] using hstep.2.2.1
        have hyout : y ∉ square a M := by
          intro hy
          have : reduction L N y ∈ Q := (hinside y hyhalo).2 hy
          exact hend (by simpa [hyr] using this)
        have hyset : y ∈ square a (M + 1) \ square a M :=
          Finset.mem_sdiff.mpr ⟨hyhalo, hyout⟩
        refine ⟨x, hx, y, hyset, ?_, ?_⟩
        · norm_num [Adjacent, latticeDist, y]
        · simp [bondSites, hstart', hyr]
    · have hend : nextSite e.1 e.2 ∈ Q := by
        by_contra hcontra
        simp [hstart, hcontra] at hcard'
      rcases Finset.mem_image.mp (show nextSite e.1 e.2 ∈
          (square a M).image (reduction L N) by simpa [Q] using hend) with ⟨x, hx, hxr⟩
      have hstep := square_step_succ a x M hx
      by_cases hd : e.2 = 0
      · let y : Plane := (x.1 - 1, x.2)
        have hx1 : (x.1 : ZMod L.val) = e.1.1 + 1 := by
          simpa [reduction, nextSite, hd] using congrArg Prod.fst hxr
        have hx2 : (x.2 : ZMod N.val) = e.1.2 := by
          simpa [reduction, nextSite, hd] using congrArg Prod.snd hxr
        have hyr : reduction L N y = e.1 := by
          apply Prod.ext
          · change ((x.1 - 1 : ℤ) : ZMod L.val) = e.1.1
            push_cast
            rw [hx1]
            abel
          · change (x.2 : ZMod N.val) = e.1.2
            exact hx2
        have hyhalo : y ∈ square a (M + 1) := by simpa [y] using hstep.2.1
        have hyout : y ∉ square a M := by
          intro hy
          have : reduction L N y ∈ Q := (hinside y hyhalo).2 hy
          exact hstart (by simpa [hyr] using this)
        have hend' : nextSite e.1 e.2 = reduction L N x := hxr.symm
        have hyset : y ∈ square a (M + 1) \ square a M :=
          Finset.mem_sdiff.mpr ⟨hyhalo, hyout⟩
        refine ⟨x, hx, y, hyset, ?_, ?_⟩
        · norm_num [Adjacent, latticeDist, y]
        · simpa [bondSites, hyr, hend'] using
            (Finset.pair_comm e.1 (reduction L N x))
      · have hd1 : e.2 = 1 := Fin.eq_one_of_ne_zero e.2 hd
        let y : Plane := (x.1, x.2 - 1)
        have hx1 : (x.1 : ZMod L.val) = e.1.1 := by
          simpa [reduction, nextSite, hd1] using congrArg Prod.fst hxr
        have hx2 : (x.2 : ZMod N.val) = e.1.2 + 1 := by
          simpa [reduction, nextSite, hd1] using congrArg Prod.snd hxr
        have hyr : reduction L N y = e.1 := by
          apply Prod.ext
          · change (x.1 : ZMod L.val) = e.1.1
            exact hx1
          · change ((x.2 - 1 : ℤ) : ZMod N.val) = e.1.2
            push_cast
            rw [hx2]
            abel
        have hyhalo : y ∈ square a (M + 1) := by simpa [y] using hstep.2.2.2
        have hyout : y ∉ square a M := by
          intro hy
          have : reduction L N y ∈ Q := (hinside y hyhalo).2 hy
          exact hstart (by simpa [hyr] using this)
        have hend' : nextSite e.1 e.2 = reduction L N x := hxr.symm
        have hyset : y ∈ square a (M + 1) \ square a M :=
          Finset.mem_sdiff.mpr ⟨hyhalo, hyout⟩
        refine ⟨x, hx, y, hyset, ?_, ?_⟩
        · norm_num [Adjacent, latticeDist, y]
        · simpa [bondSites, hyr, hend'] using
            (Finset.pair_comm e.1 (reduction L N x))
  · intro x hx
    exact hinside x hx

#print axioms main

end AKLT.W.GAP035
