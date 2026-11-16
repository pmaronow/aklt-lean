import CertData.H3.Kernel.Rows

open scoped BigOperators
set_option maxRecDepth 4096

namespace AKLT.W.H3C056

open AKLT.Defs AKLT.Gen.Packed AKLT.Cert.H3
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Nat.shiftLeft Nat.shiftRight

theorem packFn_sub (b n : Nat) (f g : Nat → Nat)
    (h : ∀ s < n, g s ≤ f s) :
    packFn b n (fun s => f s - g s) = packFn b n f - packFn b n g := by
  have he : packFn b n (fun s => f s - g s) + packFn b n g = packFn b n f := by
    rw [← packFn_add]
    apply packFn_congr
    intro s hs
    exact Nat.sub_add_cancel (h s hs)
  omega

theorem lane_sub {P Q b n : Nat} (hP : Fits P b n) (hQ : Fits Q b n)
    (h : ∀ s < n, lane Q b s ≤ lane P b s) (s : Nat) (hs : s < n) :
    lane (P-Q) b s = lane P b s - lane Q b s := by
  conv_lhs => rw [← packFn_lanes P b n hP, ← packFn_lanes Q b n hQ,
    ← packFn_sub b n _ _ h]
  rw [lane_packFn _ _ _ (fun i _ =>
    (Nat.sub_le _ _).trans_lt (lane_lt P b i)), ite_eq_left hs]

/-- A complete-lane mask, described without evaluating its large integer. -/
def Mask (M : Nat) (p : Nat → Prop) : Prop :=
  Fits M 80 19881 ∧ ∀ s < 19881, lane M 80 s = if p s then 2^80-1 else 0

theorem mask_congr {M : Nat} {p q : Nat → Prop} (h : Mask M p)
    (hpq : ∀ s < 19881, p s ↔ q s) : Mask M q := by
  refine ⟨h.1, ?_⟩
  intro s hs
  rw [h.2 s hs, hpq s hs]

theorem mask_sub {P Q : Nat} {p q : Nat → Prop} (hP : Mask P p) (hQ : Mask Q q)
    (h : ∀ s < 19881, q s → p s) : Mask (P-Q) (fun s => p s ∧ ¬q s) := by
  refine ⟨lt_of_le_of_lt (Nat.sub_le _ _) hP.1, ?_⟩
  intro s hs
  rw [lane_sub hP.1 hQ.1 (by
    intro i hi
    rw [hP.2 i hi, hQ.2 i hi]
    by_cases hqi : q i <;> simp_all) s hs, hP.2 s hs, hQ.2 s hs]
  by_cases hp : p s <;> by_cases hq : q s <;> simp_all

theorem mask_add {P Q : Nat} {p q : Nat → Prop} (hP : Mask P p) (hQ : Mask Q q)
    (h : ∀ s < 19881, ¬(p s ∧ q s)) : Mask (P+Q) (fun s => p s ∨ q s) := by
  have hsum : P+Q = packFn 80 19881 (fun s => if p s ∨ q s then 2^80-1 else 0) := by
    rw [← packFn_lanes P 80 19881 hP.1, ← packFn_lanes Q 80 19881 hQ.1, ← packFn_add]
    apply packFn_congr
    intro s hs
    rw [hP.2 s hs, hQ.2 s hs]
    by_cases hp : p s <;> by_cases hq : q s <;> simp_all
  rw [hsum]
  have hb : ∀ s < 19881, (if p s ∨ q s then 2^80-1 else 0) < 2^80 := by
    intro s hs
    split <;> norm_num
  refine ⟨packFn_lt _ _ _ hb, ?_⟩
  intro s hs
  rw [lane_packFn _ _ _ hb, ite_eq_left hs]
  split_ifs <;> rfl

theorem mask_zero : Mask 0 (fun _ => False) := by
  refine ⟨by unfold Fits; positivity, ?_⟩
  intro s hs
  simp [lane]

theorem lane_lowMask (b s : Nat) (hb : 0 < b) :
    lane (2^b-1) b s = if s = 0 then 2^b-1 else 0 := by
  by_cases hs : s = 0
  · subst s
    rw [lane_zero, Nat.mod_eq_of_lt]
    · simp
    · exact Nat.sub_lt (by positivity) (by omega)
  · rw [ite_eq_right hs]
    apply lane_eq_zero_of_fits (n := 1)
    · simp only [Fits, Nat.mul_one]
      exact Nat.sub_lt (by positivity) (by omega)
    · omega

theorem mask_all : Mask allMask (fun _ => True) := by
  refine ⟨by unfold Fits allMask; exact Nat.sub_lt (by positivity) (by omega), ?_⟩
  intro s hs
  simp only [ite_true]
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 80
  · have hsi : 80*s+i < 80*19881 := by omega
    simp only [testBit_lane, allMask, Nat.testBit_two_pow_sub_one, hi, hsi,
      decide_true, Bool.true_and]
  · simp only [testBit_lane, Nat.testBit_two_pow_sub_one, hi,
      decide_false, Bool.false_and]

theorem mask_one (t : Nat) (ht : t < 19881) : Mask (oneMask t) (fun s => s = t) := by
  have hfit : Fits (oneMask t) 80 19881 := by
    unfold oneMask Fits
    rw [Nat.shiftLeft_eq_mul_pow]
    have hlt : (2^80-1)*2^(80*t) < 2^80*2^(80*t) :=
      Nat.mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    apply lt_of_lt_of_le hlt
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    omega
  refine ⟨hfit, ?_⟩
  intro s hs
  rw [oneMask, lane_shiftLeft _ _ _ _ (by decide)]
  by_cases hts : t ≤ s
  · rw [ite_eq_left hts, lane_lowMask _ _ (by decide)]
    have he : s-t = 0 ↔ s=t := by omega
    simp only [he]
    split_ifs <;> rfl
  · have hne : s ≠ t := by omega
    simp only [hts, hne, ite_false]

theorem lane_nested (P b w r c : Nat) (hc : c < w) :
    lane (lane P (b*w) r) b c = lane P b (r*w+c) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < b
  · have hci : b*c+i < b*w := by nlinarith
    have he : b*w*r+(b*c+i) = b*(r*w+c)+i := by ring
    simp [testBit_lane, hi, hci, he]
  · simp [testBit_lane, hi]

theorem mask_firstColumn : Mask firstColumn (fun s => s%141=0) := by
  have he : firstColumn = packFn (80*141) 141 (fun _ => 2^80-1) :=
    repeatLane_eq _ _ _ (by decide)
  have hb : 2^80-1 < 2^(80*141) := by
    apply lt_of_lt_of_le (show 2^80-1 < 2^80 by norm_num)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨?_, ?_⟩
  · change Fits firstColumn (80*141) 141
    rw [he]
    exact packFn_lt _ _ _ (fun _ _ => hb)
  · intro s hs
    have hr : s/141 < 141 := by omega
    have hc : s%141 < 141 := Nat.mod_lt _ (by decide)
    have hsc : s/141*141+s%141=s := by simpa [Nat.mul_comm] using Nat.div_add_mod s 141
    conv_lhs => rw [← hsc, ← lane_nested _ 80 141 _ _ hc]
    rw [he, lane_packFn _ _ _ (fun _ _ => hb), ite_eq_left hr,
      lane_lowMask _ _ (by decide)]
    split_ifs <;> rfl

theorem mask_firstRow : Mask firstRow (fun s => s < 141) := by
  have hf : Fits firstRow 80 19881 := by
    unfold firstRow Fits
    apply lt_of_lt_of_le (Nat.sub_lt (by positivity) (by omega))
    exact Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨hf, ?_⟩
  intro s hs
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 80
  · by_cases h : s < 141
    · have hsi : 80*s+i < 80*141 := by omega
      simp only [testBit_lane, firstRow, hi, h, ite_true, decide_true,
        Bool.true_and, Nat.testBit_two_pow_sub_one, hsi]
    · have hsi : ¬80*s+i < 80*141 := by omega
      simp only [testBit_lane, firstRow, hi, h, ite_false, decide_true,
        Bool.true_and, Nat.testBit_two_pow_sub_one, hsi, decide_false]
      simp
  · simp only [testBit_lane, hi, decide_false, Bool.false_and]
    split <;> simp only [Nat.testBit_two_pow_sub_one, hi, decide_false, Nat.zero_testBit]

theorem fits_shorten {P b n k : Nat} (hP : Fits P b n) (hk : k ≤ n) (hb : 0 < b)
    (hzero : ∀ s < n, k ≤ s → lane P b s = 0) : Fits P b k := by
  have hfit : Fits (P % 2^(b*k)) b k := Nat.mod_lt _ (by positivity)
  have hfit' : Fits (P % 2^(b*k)) b n :=
    hfit.trans_le (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left b hk))
  have he : P = P % 2^(b*k) := by
    apply lanes_ext hP hfit'
    intro s hs
    rw [← Nat.and_two_pow_sub_one_eq_mod]
    change lane P b s = lane (Nat.land P (2^(b*k)-1)) b s
    rw [lane_truncate _ _ _ _ hb]
    split_ifs with h
    · rfl
    · exact hzero s hs (by omega)
  rwa [he]

theorem fits_shiftLeft {P b n : Nat} (hP : Fits P b n) (k : Nat) :
    Fits (P <<< (b*k)) b (n+k) := by
  unfold Fits at *
  rw [Nat.shiftLeft_eq_mul_pow, Nat.mul_add, pow_add]
  exact Nat.mul_lt_mul_of_pos_right hP (by positivity)

attribute [local irreducible] firstColumn firstRow allMask

theorem mask_lastColumn : Mask lastColumn (fun s => s%141=140) := by
  unfold lastColumn
  have hf : Fits firstColumn 80 19741 := fits_shorten mask_firstColumn.1 (by decide) (by decide)
    (by
      intro s hs hge
      rw [mask_firstColumn.2 s hs]
      have hn : s%141 ≠ 0 := by omega
      simp only [hn, ite_false])
  have hf' := fits_shiftLeft hf 140
  simp only [show 19741+140=19881 from rfl] at hf'
  refine ⟨?_, ?_⟩
  · exact hf'
  intro s hs
  rw [lane_shiftLeft _ _ _ _ (by decide)]
  by_cases h : 140 ≤ s
  · rw [ite_eq_left h, mask_firstColumn.2 (s-140) (by omega)]
    have he : (s-140)%141=0 ↔ s%141=140 := by omega
    simp only [he]
    split_ifs <;> rfl
  · have he : s%141 ≠ 140 := by omega
    simp [h, he]

theorem mask_lastRow : Mask lastRow (fun s => s/141=140) := by
  unfold lastRow
  have hf : Fits firstRow 80 141 := by
    unfold Fits firstRow
    exact Nat.sub_lt (by positivity) (by omega)
  have hf' := fits_shiftLeft hf 19740
  simp only [show 141+19740=19881 from rfl] at hf'
  refine ⟨?_, ?_⟩
  · exact hf'
  intro s hs
  rw [lane_shiftLeft _ _ _ _ (by decide)]
  by_cases h : 19740 ≤ s
  · rw [ite_eq_left h, mask_firstRow.2 (s-19740) (by omega)]
    have hsmall : s-19740 < 141 := by omega
    have he : s/141=140 := by omega
    simp [hsmall, he]
  · have he : s/141 ≠ 140 := by omega
    simp [show ¬19881-141 ≤ s by omega, he]

def boundary (d : Compass) (s : Nat) : Prop := match d with
  | .east => s/141=140 | .north => s%141=140
  | .west => s/141=0 | .south => s%141=0

theorem mask_boundary (d : Compass) : Mask (boundaryMask d) (boundary d) := by
  cases d
  · exact mask_lastRow
  · exact mask_lastColumn
  · exact mask_congr mask_firstRow (by intro s hs; dsimp [boundary]; omega)
  · exact mask_firstColumn

end
end AKLT.W.H3C056
