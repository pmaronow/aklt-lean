import CertData.H3.Bridge.Interface
set_option maxRecDepth 100000

namespace AKLT.W.H3C021

open AKLT.Cert.H3 AKLT.Defs AKLT.Gen.Packed

private theorem oneMask_le_of_lane_eq (P b i : Nat)
    (h : lane P b i = 2^b - 1) : (2^b - 1) <<< (b*i) ≤ P := by
  have hfull : (P / 2^(b*i)) % 2^b = 2^b - 1 := by
    simpa [lane, Nat.shiftRight_eq_div_pow] using h
  have hquot : 2^b - 1 ≤ P / 2^(b*i) := by
    rw [← hfull]
    exact Nat.mod_le _ _
  rw [Nat.shiftLeft_eq]
  let a := 2^(b*i)
  let q := P / a
  have hdecomp : P % a + a*q = P := by simpa [a, q] using Nat.mod_add_div P a
  have hmul : (2^b - 1) * 2^(b*i) ≤ (P / 2^(b*i)) * 2^(b*i) :=
    Nat.mul_le_mul_right _ hquot
  have hdivle : 2^(b*i) * (P / 2^(b*i)) ≤ P := by
    calc
      2^(b*i) * (P / 2^(b*i)) = 2^(b*i) * q := by simp [q, a]
      _ ≤ P % a + 2^(b*i) * q := Nat.le_add_left _ _
      _ = P := by simpa [a] using hdecomp
  have hbound : (P / 2^(b*i)) * 2^(b*i) ≤ P := by
    simpa [Nat.mul_comm] using hdivle
  exact hmul.trans hbound

private theorem lane_sub_oneMask (P b i s : Nat) (hb : 0 < b)
    (hfull : lane P b i = 2^b - 1) :
    lane (P - ((2^b - 1) <<< (b*i))) b s = if s = i then 0 else lane P b s := by
  induction i generalizing P s with
  | zero =>
      have hlow : P % 2^b = 2^b - 1 := by simpa [lane] using hfull
      have hdecomp := Nat.mod_add_div P (2^b)
      have hsub : P - ((2^b - 1) <<< (b*0)) = 2^b * (P / 2^b) := by
        have hp : P = (2^b - 1) + 2^b * (P / 2^b) := by
          simpa [hlow] using hdecomp.symm
        simp only [Nat.mul_zero, Nat.shiftLeft_zero]
        conv_lhs => rw [hp]
        omega
      cases s with
      | zero =>
          rw [hsub]
          simp [lane, Nat.mul_mod_right]
      | succ s =>
          have hshift : 2^b * (P / 2^b) = (P / 2^b) <<< b := by
            rw [Nat.shiftLeft_eq]
            simp [Nat.mul_comm]
          have hshift' : (P / 2^b) <<< b = (P / 2^b) <<< (b*1) := by simp
          rw [hsub, hshift, hshift', lane_shiftLeft _ _ 1 _ hb]
          simp [lane_succ]
  | succ i ih =>
      let B := 2^b
      let R := (B - 1) <<< (b*i)
      have hfullQ : lane (P / B) b i = B - 1 := by
        simpa [B, lane_succ] using hfull
      have hQR : R ≤ P / B := by
        simpa [B, R] using oneMask_le_of_lane_eq (P / B) b i hfullQ
      have hdecomp := Nat.mod_add_div P B
      have hlow : P % B < B := by
        dsimp [B]
        exact Nat.mod_lt _ (by positivity)
      have hone : (2^b - 1) <<< (b*(i+1)) = B * R := by
        dsimp [B, R]
        rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mul_succ, pow_add]
        ring
      have hsub : P - ((2^b - 1) <<< (b*(i+1))) = P % B + B * (P / B - R) := by
        calc
          P - ((2^b - 1) <<< (b*(i+1))) = (P % B + B * (P / B)) - B * R := by
            conv_lhs => rw [← hdecomp]
            rw [hone]
          _ = P % B + (B * (P / B) - B * R) := Nat.add_sub_assoc (Nat.mul_le_mul_left B hQR) _
          _ = P % B + B * (P / B - R) := by rw [Nat.mul_sub_left_distrib]
      cases s with
      | zero =>
          rw [hsub]
          simp [lane, B, Nat.add_mod, Nat.mod_eq_of_lt hlow, Nat.mul_mod_right]
      | succ s =>
          have hquot : (P % B + B * (P / B - R)) / B = P / B - R := by
            rw [Nat.add_mul_div_left _ _ (by positivity)]
            simp [Nat.div_eq_of_lt hlow]
          rw [hsub, lane_succ, hquot, lane_succ]
          simpa [B, R, Nat.succ_eq_add_one] using ih (P / B) s hfullQ

private theorem mul_sub_one (A C : Nat) (hA : 1 ≤ A) (hC : 1 ≤ C) :
    A*C-1 = (A-1) + A*(C-1) := by
  have hsum : (A-1) + A*(C-1) + 1 = A*C := by
    calc
      (A-1) + A*(C-1) + 1 = A + A*(C-1) := by omega
      _ = A*((C-1)+1) := by ring
      _ = A*C := by rw [Nat.sub_add_cancel hC]
  omega

private theorem pow_sub_div (N k : Nat) (hk : k ≤ N) :
    (2^N-1)/2^k = 2^(N-k)-1 := by
  have hmul : 2^k * 2^(N-k) = 2^N := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  have hdecomp : 2^N-1 = (2^k-1) + 2^k*(2^(N-k)-1) := by
    calc
      2^N-1 = (2^k * 2^(N-k))-1 := by rw [hmul]
      _ = (2^k-1) + 2^k*(2^(N-k)-1) :=
        mul_sub_one _ _ Nat.one_le_two_pow Nat.one_le_two_pow
  rw [hdecomp, Nat.add_mul_div_left _ _ (y := 2^k) (by positivity)]
  have hlt : 2^k - 1 < 2^k := Nat.sub_lt (show 1 ≤ 2^k from Nat.one_le_two_pow) (by decide)
  simp [Nat.div_eq_of_lt hlt]

private theorem lane_allMask (s : Nat) (hs : s < 19881) :
    lane allMask 80 s = 2^80 - 1 := by
  have hk : 80*s ≤ 80*19881 := Nat.mul_le_mul_left 80 (Nat.le_of_lt hs)
  have hrem : 80 ≤ 80*19881 - 80*s := by omega
  have hmul : 2^80 * 2^(80*19881 - 80*s - 80) = 2^(80*19881 - 80*s) := by
    rw [← pow_add]
    congr 1
    omega
  have hsplit : 2^(80*19881 - 80*s)-1 =
      (2^80-1) + 2^80*(2^(80*19881 - 80*s - 80)-1) := by
    calc
      2^(80*19881 - 80*s)-1 =
          2^80 * 2^(80*19881 - 80*s - 80) - 1 := by rw [hmul]
      _ = (2^80-1) + 2^80*(2^(80*19881 - 80*s - 80)-1) :=
        mul_sub_one _ _ Nat.one_le_two_pow Nat.one_le_two_pow
  change lane (2^(80*19881)-1) 80 s = 2^80 - 1
  rw [lane, Nat.shiftRight_eq_div_pow, pow_sub_div (80*19881) (80*s) hk, hsplit]
  simp [Nat.add_mul_mod_self_left]

private def removeFour (i₁ i₂ i₃ i₄ : Nat) : Nat :=
  (((allMask - oneMask i₁) - oneMask i₂) - oneMask i₃) - oneMask i₄

private theorem lane_sub_oneMask80 (P i s : Nat) (hfull : lane P 80 i = 2^80 - 1) :
    lane (P - oneMask i) 80 s = if s = i then 0 else lane P 80 s := by
  simpa only [oneMask] using lane_sub_oneMask P 80 i s (by decide) hfull

private theorem lane_removeFour (i₁ i₂ i₃ i₄ s : Nat)
    (hi₁ : i₁ < 19881) (hi₂ : i₂ < 19881) (hi₃ : i₃ < 19881) (hi₄ : i₄ < 19881)
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h14 : i₁ ≠ i₄)
    (h23 : i₂ ≠ i₃) (h24 : i₂ ≠ i₄) (h34 : i₃ ≠ i₄)
    (hs : s < 19881) :
    lane (removeFour i₁ i₂ i₃ i₄) 80 s =
      if s = i₁ ∨ s = i₂ ∨ s = i₃ ∨ s = i₄ then 0 else 2^80 - 1 := by
  have h1 : ∀ t < 19881, lane (allMask - oneMask i₁) 80 t = if t = i₁ then 0 else 2^80 - 1 := by
    intro t ht
    rw [lane_sub_oneMask80 allMask i₁ t (lane_allMask i₁ hi₁), lane_allMask t ht]
  have h2full : lane (allMask - oneMask i₁) 80 i₂ = 2^80 - 1 := by
    rw [h1 i₂ hi₂]
    simp [h12.symm]
  have h2 : ∀ t < 19881, lane ((allMask - oneMask i₁) - oneMask i₂) 80 t =
      if t = i₁ ∨ t = i₂ then 0 else 2^80 - 1 := by
    intro t ht
    have hcut : lane ((allMask - oneMask i₁) - oneMask i₂) 80 t =
        if t = i₂ then 0 else lane (allMask - oneMask i₁) 80 t := by
      exact lane_sub_oneMask80 (allMask - oneMask i₁) i₂ t h2full
    rw [hcut, h1 t ht]
    by_cases ht1 : t = i₁ <;> by_cases ht2 : t = i₂ <;> simp_all
  have h3full : lane ((allMask - oneMask i₁) - oneMask i₂) 80 i₃ = 2^80 - 1 := by
    rw [h2 i₃ hi₃]
    simp [h13.symm, h23.symm]
  have h3 : ∀ t < 19881, lane (((allMask - oneMask i₁) - oneMask i₂) - oneMask i₃) 80 t =
      if t = i₁ ∨ t = i₂ ∨ t = i₃ then 0 else 2^80 - 1 := by
    intro t ht
    have hcut : lane (((allMask - oneMask i₁) - oneMask i₂) - oneMask i₃) 80 t =
        if t = i₃ then 0 else lane ((allMask - oneMask i₁) - oneMask i₂) 80 t := by
      exact lane_sub_oneMask80 ((allMask - oneMask i₁) - oneMask i₂) i₃ t h3full
    rw [hcut, h2 t ht]
    by_cases ht1 : t = i₁ <;> by_cases ht2 : t = i₂ <;> by_cases ht3 : t = i₃ <;> simp_all
  have h4full : lane (((allMask - oneMask i₁) - oneMask i₂) - oneMask i₃) 80 i₄ = 2^80 - 1 := by
    rw [h3 i₄ hi₄]
    simp [h14.symm, h24.symm, h34.symm]
  have hcut := lane_sub_oneMask80 (((allMask - oneMask i₁) - oneMask i₂) - oneMask i₃) i₄ s h4full
  have hcut' : lane (removeFour i₁ i₂ i₃ i₄) 80 s =
      if s = i₄ then 0 else lane (((allMask - oneMask i₁) - oneMask i₂) - oneMask i₃) 80 s := by
    simpa only [removeFour] using hcut
  rw [hcut', h3 s hs]
  by_cases hs1 : s = i₁ <;> by_cases hs2 : s = i₂ <;> by_cases hs3 : s = i₃ <;>
    by_cases hs4 : s = i₄ <;> simp_all

private theorem siteIndex_gridSite (s : Nat) (hs : s < 19881) : siteIndex (gridSite s) = s := by
  have hq : s / 141 < 141 := by omega
  have hr : s % 141 < 141 := Nat.mod_lt _ (by decide)
  unfold siteIndex gridSite
  omega

private theorem gridSite_siteIndex (x : Plane) (hx₁ : -70 ≤ x.1) (hx₂ : x.1 ≤ 70)
    (hy₁ : -70 ≤ x.2) (hy₂ : x.2 ≤ 70) : gridSite (siteIndex x) = x := by
  let a := (x.1 + 70).toNat
  let c := (x.2 + 70).toNat
  have haI : (a : Int) = x.1 + 70 := by
    dsimp [a]
    exact Int.toNat_of_nonneg (by omega)
  have hcI : (c : Int) = x.2 + 70 := by
    dsimp [c]
    exact Int.toNat_of_nonneg (by omega)
  have hac : a < 141 := by omega
  have hcc : c < 141 := by omega
  have hdiv : (a * 141 + c) / 141 = a := by
    calc
      (a * 141 + c) / 141 = (c + 141 * a) / 141 := by rw [Nat.mul_comm a 141, Nat.add_comm]
      _ = c / 141 + a := Nat.add_mul_div_left c a (by decide)
      _ = a := by simp [Nat.div_eq_of_lt hcc]
  have hmod : (a * 141 + c) % 141 = c := by
    rw [Nat.mul_comm a 141, Nat.add_comm, Nat.add_mul_mod_self_left]
    simp [Nat.mod_eq_of_lt hcc]
  apply Prod.ext
  · change (((a * 141 + c) / 141 : Nat) : Int) - 70 = x.1
    rw [hdiv]
    omega
  · change (((a * 141 + c) % 141 : Nat) : Int) - 70 = x.2
    rw [hmod]
    omega

private theorem gridSite_eq_iff (s : Nat) (hs : s < 19881) (x : Plane)
    (hx₁ : -70 ≤ x.1) (hx₂ : x.1 ≤ 70) (hy₁ : -70 ≤ x.2) (hy₂ : x.2 ≤ 70) :
    gridSite s = x ↔ s = siteIndex x := by
  constructor
  · intro h
    have hi := congrArg siteIndex h
    simpa [siteIndex_gridSite s hs] using hi
  · intro h
    rw [h]
    exact gridSite_siteIndex x hx₁ hx₂ hy₁ hy₂

private theorem reserved_indices (X : PairType) (d₀ : Compass)
    (hcase : (X,d₀) ∈ stationaryCases) :
    let i₁ := siteIndex kernelCentre
    let i₂ := siteIndex (kernelTarget X)
    let i₃ := siteIndex kernelStart
    let i₄ := siteIndex (kernelStart + d₀.step)
    i₁ < 19881 ∧ i₂ < 19881 ∧ i₃ < 19881 ∧ i₄ < 19881 ∧
      i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₁ ≠ i₄ ∧ i₂ ≠ i₃ ∧ i₂ ≠ i₄ ∧ i₃ ≠ i₄ := by
  cases X <;> cases d₀ <;> simp_all [stationaryCases, kernelCentre, kernelTarget,
    kernelStart, Compass.step, siteIndex]

theorem main : CertData.H3.Bridge.OrdinaryMaskLeaf := by
  intro X d₀ hcase s hs
  obtain ⟨hi₁, hi₂, hi₃, hi₄, h12, h13, h14, h23, h24, h34⟩ := reserved_indices X d₀ hcase
  have hmask := lane_removeFour (siteIndex kernelCentre) (siteIndex (kernelTarget X))
    (siteIndex kernelStart) (siteIndex (kernelStart + d₀.step)) s
    hi₁ hi₂ hi₃ hi₄ h12 h13 h14 h23 h24 h34 hs
  have h1 := gridSite_eq_iff s hs kernelCentre (by norm_num [kernelCentre])
    (by norm_num [kernelCentre]) (by norm_num [kernelCentre]) (by norm_num [kernelCentre])
  have h2 := gridSite_eq_iff s hs (kernelTarget X) (by cases X <;> norm_num [kernelTarget, PairType])
    (by cases X <;> norm_num [kernelTarget, PairType]) (by cases X <;> norm_num [kernelTarget, PairType])
    (by cases X <;> norm_num [kernelTarget, PairType])
  have h3 := gridSite_eq_iff s hs kernelStart (by norm_num [kernelStart])
    (by norm_num [kernelStart]) (by norm_num [kernelStart]) (by norm_num [kernelStart])
  have h4 := gridSite_eq_iff s hs (kernelStart + d₀.step)
    (by cases d₀ <;> norm_num [kernelStart, Compass.step])
    (by cases d₀ <;> norm_num [kernelStart, Compass.step])
    (by cases d₀ <;> norm_num [kernelStart, Compass.step])
    (by cases d₀ <;> norm_num [kernelStart, Compass.step])
  change lane (removeFour (siteIndex kernelCentre) (siteIndex (kernelTarget X))
    (siteIndex kernelStart) (siteIndex (kernelStart + d₀.step))) 80 s = _
  simpa only [h1, h2, h3, h4] using hmask

end AKLT.W.H3C021

#print axioms AKLT.W.H3C021.main
