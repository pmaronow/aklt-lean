import AKLT.Blueprint.Gap.NodesShell

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap

namespace AKLT.W.GAP048

private theorem sitesInVolume_mono {W V V' : Finset Plane} (h : V ⊆ V') :
    sitesInVolume W V ⊆ sitesInVolume W V' := by
  intro x hx
  simp only [sitesInVolume, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact h hx

private theorem shell_subset_farVolume_of_index_le
    (a y : Plane) (u : ℕ) {i b : ℤ}
    (hs : 1 < shellSpacing u) (hbi : b ≤ i) :
    shell a y u i ⊆ farVolume a y u b := by
  intro x hx
  simp only [shell, farVolume, Finset.mem_filter] at hx ⊢
  rcases hx with ⟨hxsq, hrad⟩
  refine ⟨hxsq, ?_⟩
  have hfloor := Int.sub_one_lt_floor ((i : ℝ) * shellSpacing u)
  have hidx : (b : ℝ) * shellSpacing u ≤ (i : ℝ) * shellSpacing u :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hbi) (by linarith : 0 ≤ shellSpacing u)
  have hbound : ((b : ℝ) - 1) * shellSpacing u <
      ((i : ℝ) * shellSpacing u - 1) := by
    nlinarith [hs]
  have hrad' : (supDist x y : ℝ) = (⌊(i : ℝ) * shellSpacing u⌋ : ℝ) := by
    dsimp [shellRadius] at hrad
    exact_mod_cast hrad
  rw [hrad']
  linarith

theorem main : AKLT.Blueprint.Gap.ShellAbsorptionStatement := by
  classical
  intro P a y u l h p α η ξ hs R t htrace hsuccess
  let W := square a u
  have hspos : 1 < shellSpacing u := by
    have : (16 : ℝ) ≤ shellSpacing u := hs
    linarith
  have hs0 : 0 < shellSpacing u := by linarith
  have hstepPos : ∀ k : Fin h,
      0 < R.kernel k (t k.castSucc) (t k.succ) := by
    intro k
    have hprodNonneg :
        0 ≤ ∏ q : Fin h, R.kernel q (t q.castSucc) (t q.succ) := by
      apply Finset.prod_nonneg
      intro q hq
      exact (R.stochastic q (t q.castSucc)).1 (t q.succ)
    have hprodNe :
        (∏ q : Fin h, R.kernel q (t q.castSucc) (t q.succ)) ≠ 0 := by
      intro hz
      have heq : surgeryTrace P a y u l h p α η ξ R t = 0 := by
        dsimp [surgeryTrace, traceLaw, independentPairs]
        rw [hz]
        ring
      linarith
    have hprodPos :
        0 < ∏ q : Fin h, R.kernel q (t q.castSucc) (t q.succ) := by
      by_contra hnot
      have hle : ∏ q : Fin h, R.kernel q (t q.castSucc) (t q.succ) ≤ 0 := le_of_not_gt hnot
      have hz : ∏ q : Fin h, R.kernel q (t q.castSucc) (t q.succ) = 0 :=
        le_antisymm hle hprodNonneg
      exact hprodNe hz
    have hfactorNe : R.kernel k (t k.castSucc) (t k.succ) ≠ 0 := by
      have hne := (Finset.prod_ne_zero_iff.mp (ne_of_gt hprodPos))
      exact hne k (Finset.mem_univ k)
    have hfactorNonneg := (R.stochastic k (t k.castSucc)).1 (t k.succ)
    by_contra hnot
    have hle : R.kernel k (t k.castSucc) (t k.succ) ≤ 0 := le_of_not_gt hnot
    have hz : R.kernel k (t k.castSucc) (t k.succ) = 0 :=
      le_antisymm hle hfactorNonneg
    exact hfactorNe hz

  rcases hsuccess with ⟨j, hjtrial, hsuccess⟩
  have hjfacts : j.val + 2 ≤ h ∧
      (j.val + 2 : ℤ) ∉ exceptionalIndices a y u ∧
      (j.val + 3 : ℤ) ∉ exceptionalIndices a y u := by
    simpa [trialTimes] using hjtrial
  rcases hjfacts with ⟨hjbound, hjnot, hjnextnot⟩
  let kfirst : Fin h := ⟨j.val + 1, by omega⟩
  have hkfirstCast : kfirst.castSucc = j.succ := by
    apply Fin.ext
    simp [kfirst]
  have hfirstIndex : (kfirst.val + 1 : ℤ) = (j.val + 2 : ℤ) := by
    simp [kfirst]
    omega
  have hnextIndex : (kfirst.val + 2 : ℤ) = (j.val + 3 : ℤ) := by
    simp [kfirst]
    omega
  have hfirst := R.identical kfirst (t kfirst.castSucc) (by
      rw [hnextIndex]
      exact hjnextnot)
      (by
        rw [hfirstIndex, hkfirstCast]
        exact hsuccess)
      (t kfirst.succ) (hstepPos kfirst)
  have hstart : AgreeOn (sitesInVolume W (farVolume a y u (j.val + 3 : ℤ)))
      (t kfirst.succ).1 (t kfirst.succ).2 := by
    rw [hnextIndex] at hfirst
    exact hfirst
  have hkfirstSucc : kfirst.succ = ⟨j.val + 2, by omega⟩ := by
    apply Fin.ext
    simp [kfirst]

  let Base : ℕ := j.val + 3
  let Q : ∀ n, j.val + 2 ≤ n → Prop := fun n _ =>
    ∀ hnhi : n ≤ h,
      AgreeOn (sitesInVolume W (farVolume a y u (Base : ℤ)))
        (t ⟨n, by omega⟩).1 (t ⟨n, by omega⟩).2
  have hQbase : Q (j.val + 2) (by omega) := by
    intro hnhi
    simpa [Q, Base, hkfirstSucc] using hstart
  have hQstep : ∀ n (hnlo : j.val + 2 ≤ n), Q n hnlo → Q (n + 1) (by omega) := by
    intro n hnlo ih hnhi
    let k : Fin h := ⟨n, by omega⟩
    have hkSucc : k.succ = ⟨n + 1, by omega⟩ := by
      apply Fin.ext
      simp [k]
    have hprev := ih (by omega)
    have hprev' : AgreeOn (sitesInVolume W (farVolume a y u (Base : ℤ)))
        (t k.castSucc).1 (t k.castSucc).2 := by
      simpa [k] using hprev
    have hrow := hstepPos k
    by_cases hex : (k.val + 2 : ℤ) ∈ exceptionalIndices a y u
    · have hmarg := R.marginals k (t k.castSucc)
      rw [ite_eq_left hex] at hmarg
      have hsame : t k.succ = t k.castSucc := by
        by_contra hne
        have hz : R.kernel k (t k.castSucc) (t k.succ) = 0 := by
          rw [hmarg]
          simp [hne]
        rw [hz] at hrow
        exact (lt_irrefl 0 hrow)
      rw [← hkSucc, hsame]
      exact hprev'
    · have hBaseLe : (Base : ℤ) ≤ (k.val + 1 : ℤ) := by
        change ((j.val + 3 : ℕ) : ℤ) ≤ ((n + 1 : ℕ) : ℤ)
        exact_mod_cast (show j.val + 3 ≤ n + 1 by omega)
      have hshellSub : shell a y u (k.val + 1 : ℤ) ⊆
          farVolume a y u (Base : ℤ) :=
        shell_subset_farVolume_of_index_le a y u hspos hBaseLe
      have hShellAgree : AgreeOn
          (sitesInVolume W (shell a y u (k.val + 1 : ℤ)))
          (t k.castSucc).1 (t k.castSucc).2 := by
        intro x hx
        exact hprev' x (sitesInVolume_mono hshellSub hx)
      have hcurrent := R.identical k (t k.castSucc) hex hShellAgree
          (t k.succ) hrow
      rcases R.fixed_exterior k (t k.castSucc) (t k.succ) hrow with ⟨hout₁, hout₂⟩
      have hpreserve : AgreeOn
          (sitesInVolume W (farVolume a y u (Base : ℤ)))
          (t k.succ).1 (t k.succ).2 := by
        intro x hxBase
        by_cases hxCurrent : x ∈ sitesInVolume W
            (farVolume a y u (k.val + 2 : ℤ))
        · exact hcurrent x hxCurrent
        · calc
            (t k.succ).1 x = (t k.castSucc).1 x := (hout₁ x hxCurrent).symm
            _ = (t k.castSucc).2 x := hprev' x hxBase
            _ = (t k.succ).2 x := hout₂ x hxCurrent
      rw [← hkSucc]
      exact hpreserve

  have hfinalBase : AgreeOn (sitesInVolume W
      (farVolume a y u (Base : ℤ))) (t (Fin.last h)).1 (t (Fin.last h)).2 := by
    have hall := Nat.le_induction (m := j.val + 2) (P := Q)
      hQbase hQstep h (by omega : j.val + 2 ≤ h)
    have hlast : (⟨h, by omega⟩ : Fin (h + 1)) = Fin.last h := by
      apply Fin.ext
      rfl
    simpa [Q, Base, hlast] using hall (le_rfl : h ≤ h)
  have htargetSub : farSites a y u ((h : ℝ) * shellSpacing u) ⊆
      sitesInVolume W (farVolume a y u (Base : ℤ)) := by
    intro x hx
    simp only [farSites, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [sitesInVolume, Finset.mem_filter, Finset.mem_univ, true_and]
    change x.val ∈ farVolume a y u (Base : ℤ)
    simp only [farVolume, Finset.mem_filter]
    refine ⟨x.property, ?_⟩
    have hBaseMinus : (Base : ℝ) - 1 = (j.val : ℝ) + 2 := by
      dsimp [Base]
      push_cast
      ring
    have hjh : (Base : ℝ) - 1 ≤ (h : ℝ) := by
      rw [hBaseMinus]
      exact_mod_cast hjbound
    have hmul : ((Base : ℝ) - 1) * shellSpacing u ≤
        (h : ℝ) * shellSpacing u := mul_le_mul_of_nonneg_right hjh hs0.le
    have hmul' : (((Base : ℤ) : ℝ) - 1) * shellSpacing u ≤
        (h : ℝ) * shellSpacing u := by
      have hcast : ((Base : ℤ) : ℝ) = (Base : ℝ) := by norm_cast
      rw [hcast]
      exact hmul
    exact lt_of_le_of_lt hmul' hx
  intro x hx
  exact hfinalBase x (htargetSub hx)

end AKLT.W.GAP048
