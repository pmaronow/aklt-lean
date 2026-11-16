import CertData.H3.Bridge.Interface
import CertData.H3.Kernel.View

set_option maxRecDepth 100000

namespace AKLT.W.H3C041

open AKLT.Defs
open AKLT.Cert.H3
open AKLT.Cert.H3.Production
open AKLT.Gen.Packed
open CertData.H3.Bridge

private def rectChunk (P r : Nat) : Nat :=
  Nat.land (P >>> (80 * ((r + 57) * 141 + 58))) (2 ^ (80 * 25) - 1)

private def rectRows (P start count : Nat) : Nat :=
  (List.range count).foldr
    (fun i rest => rectChunk P (start + i) + (rest <<< (80 * 25))) 0

private theorem rectRows_succ (P start n : Nat) :
    rectRows P start (n + 1) = rectChunk P start + (rectRows P (start + 1) n <<< (80 * 25)) := by
  change (List.range (n + 1)).foldr
    (fun i rest => rectChunk P (start + i) + (rest <<< (80 * 25))) 0 = _
  rw [List.range_succ_eq_map]
  rw [List.foldr_cons, List.foldr_map]
  rw [rectRows]
  have hfun :
      (fun i rest => rectChunk P (start + i.succ) + (rest <<< (80 * 25))) =
      (fun i rest => rectChunk P (start + 1 + i) + (rest <<< (80 * 25))) := by
    funext i rest
    have hidx : start + i.succ = start + 1 + i := by omega
    rw [hidx]
  rw [hfun]
  simp only [Nat.add_zero]

private theorem rectChunk_fits (P r : Nat) : Fits (rectChunk P r) 80 25 := by
  dsimp [rectChunk, Fits]
  apply Nat.and_lt_two_pow
  have hpow : 0 < 2 ^ (80 * 25) := by positivity
  exact Nat.sub_lt hpow (by decide)

private theorem fits_append {P Q b n m : Nat} (hP : Fits P b n) (hQ : Fits Q b m) :
    Fits (P + (Q <<< (b * n))) b (n + m) := by
  dsimp [Fits] at hP hQ ⊢
  rw [Nat.shiftLeft_eq_mul_pow]
  have hpw : 2 ^ (b * n) * 2 ^ (b * m) = 2 ^ (b * (n + m)) := by
    rw [← Nat.pow_add]
    rw [Nat.mul_add]
  calc
    P + Q * 2 ^ (b * n) < (Q + 1) * 2 ^ (b * n) := by nlinarith
    _ ≤ 2 ^ (b * m) * 2 ^ (b * n) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hQ)
    _ = 2 ^ (b * (n + m)) := by rw [Nat.mul_comm, hpw]

private theorem lane_append {P Q b n m s : Nat} (hP : Fits P b n) (hQ : Fits Q b m)
    (hb : 0 < b) (hs : s < n + m) :
    lane (P + (Q <<< (b * n))) b s = if s < n then lane P b s else lane Q b (s - n) := by
  have hPbig : Fits P b (n + m) := by
    dsimp [Fits] at hP ⊢
    exact lt_of_lt_of_le hP
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left b (Nat.le_add_right n m)))
  have hQbig : Fits (Q <<< (b * n)) b (n + m) := by
    dsimp [Fits] at hQ ⊢
    rw [Nat.shiftLeft_eq_mul_pow]
    have hpw : 2 ^ (b * n) * 2 ^ (b * m) = 2 ^ (b * (n + m)) := by
      rw [← Nat.pow_add]
      rw [Nat.mul_add]
    calc
      Q * 2 ^ (b * n) < 2 ^ (b * m) * 2 ^ (b * n) :=
        Nat.mul_lt_mul_of_pos_right hQ (by positivity)
      _ = 2 ^ (b * (n + m)) := by rw [Nat.mul_comm, hpw]
  have hsum : ∀ i < n + m,
      lane P b i + lane (Q <<< (b * n)) b i < 2 ^ b := by
    intro i hi
    by_cases hin : i < n
    · have hzero : lane (Q <<< (b * n)) b i = 0 := by
        rw [lane_shiftLeft Q b n i hb]
        simp [show ¬ n ≤ i by omega]
      rw [hzero, Nat.add_zero]
      exact lane_lt P b i
    · have hzero : lane P b i = 0 := lane_eq_zero_of_fits hP i (by omega)
      rw [hzero, Nat.zero_add, lane_shiftLeft Q b n i hb]
      simp only [if_pos (show n ≤ i by omega)]
      exact lane_lt Q b (i - n)
  rw [lane_add hPbig hQbig hsum s hs]
  by_cases hin : s < n
  · simp only [if_pos hin]
    have hzero : lane (Q <<< (b * n)) b s = 0 := by
      rw [lane_shiftLeft Q b n s hb]
      simp [show ¬ n ≤ s by omega]
    rw [hzero, Nat.add_zero]
  · simp only [if_neg hin]
    have hzero : lane P b s = 0 := lane_eq_zero_of_fits hP s (by omega)
    rw [hzero, Nat.zero_add, lane_shiftLeft Q b n s hb]
    simp only [if_pos (show n ≤ s by omega)]

private theorem rectRows_fits (P start : Nat) (n : Nat) :
    Fits (rectRows P start n) 80 (25 * n) := by
  induction n generalizing start with
  | zero => simp [rectRows, Fits]
  | succ n ih =>
    have ht := ih (start + 1)
    rw [rectRows_succ]
    have ha := fits_append (rectChunk_fits P start) ht
    simpa only [Nat.mul_succ, Nat.add_comm] using ha

private theorem rectRows_lane (P start : Nat) (n r c : Nat) (hr : r < n) (hc : c < 25) :
    lane (rectRows P start n) 80 (25 * r + c) = lane (rectChunk P (start + r)) 80 c := by
  induction n generalizing start r with
  | zero => omega
  | succ n ih =>
    have ht := rectRows_fits P (start + 1) n
    rw [rectRows_succ]
    have ha := lane_append (rectChunk_fits P start) ht (by decide : 0 < 80)
      (s := 25 * r + c) (by omega)
    by_cases hr0 : r = 0
    · subst r
      simpa [Nat.zero_add, hc] using ha
    · have hrpos : 1 ≤ r := by omega
      have htail : r - 1 < n := by omega
      have hsub : 25 * r + c - 25 = 25 * (r - 1) + c := by omega
      have hstart : start + 1 + (r - 1) = start + r := by omega
      have hrest := ih (start + 1) (r - 1) htail
      have hnot : ¬ 25 * r + c < 25 := by omega
      simp only [if_neg hnot] at ha
      rw [hsub] at ha
      rw [hstart] at hrest
      exact ha.trans hrest

private theorem rectChunk_lane (P r c : Nat) (hc : c < 25) :
    lane (rectChunk P r) 80 c = lane P 80 ((r + 57) * 141 + (c + 58)) := by
  unfold rectChunk
  rw [lane_truncate _ _ _ _ (by decide : 0 < 80)]
  simp only [if_pos hc, lane_shiftRight]
  congr 1
  omega

private theorem rectangle_eq_rectRows (P : Nat) : rectangle P = rectRows P 0 25 := by
  unfold rectangle rectRows
  apply congrArg (fun f : Nat → Nat → Nat => (List.range 25).foldr f 0)
  funext r rest
  simp [rectChunk]

private theorem rectangle_endpoint_lane (P : Nat) (x : Point) (hx : endpointInside x = true) :
    lane (rectangle P) 80 (endpointIndex x) = lane P 80 (siteIndex x) := by
  have hcoords : -13 ≤ x.1 ∧ x.1 ≤ 11 ∧ -12 ≤ x.2 ∧ x.2 ≤ 12 := by
    change decide (-13 ≤ x.1 ∧ x.1 ≤ 11 ∧ -12 ≤ x.2 ∧ x.2 ≤ 12) = true at hx
    exact of_decide_eq_true hx
  let r := (x.1 + 13).toNat
  let c := (x.2 + 12).toNat
  have hr : r < 25 := by
    dsimp [r]
    exact (Int.toNat_lt (by omega : 0 ≤ x.1 + 13)).2 (by omega)
  have hc : c < 25 := by
    dsimp [c]
    exact (Int.toNat_lt (by omega : 0 ≤ x.2 + 12)).2 (by omega)
  have hend : endpointIndex x = 25 * r + c := by
    simp [endpointIndex, r, c, Nat.mul_comm]
  have hsite1 : (x.1 + 70).toNat = r + 57 := by
    dsimp [r]
    rw [show x.1 + 70 = (x.1 + 13) + 57 by omega]
    exact Int.toNat_add_nat (by omega) 57
  have hsite2 : (x.2 + 70).toNat = c + 58 := by
    dsimp [c]
    rw [show x.2 + 70 = (x.2 + 12) + 58 by omega]
    exact Int.toNat_add_nat (by omega) 58
  have hsite : siteIndex x = (r + 57) * 141 + (c + 58) := by
    unfold siteIndex
    rw [hsite1, hsite2]
  have hrow : lane (rectRows P 0 25) 80 (25 * r + c) = lane (rectChunk P r) 80 c := by
    simpa using rectRows_lane P 0 25 r c hr hc
  have hchunk := rectChunk_lane P r c hc
  calc
    lane (rectangle P) 80 (endpointIndex x) =
        lane (rectRows P 0 25) 80 (endpointIndex x) :=
      congrArg (fun Q => lane Q 80 (endpointIndex x)) (rectangle_eq_rectRows P)
    _ = lane (rectRows P 0 25) 80 (25 * r + c) :=
      congrArg (fun i => lane (rectRows P 0 25) 80 i) hend
    lane (rectRows P 0 25) 80 (25 * r + c) = lane (rectChunk P r) 80 c := hrow
    _ = lane P 80 ((r + 57) * 141 + (c + 58)) := hchunk
    _ = lane P 80 (siteIndex x) :=
      congrArg (fun i => lane P 80 i) hsite.symm

theorem main : CertData.H3.Bridge.EndpointTableSoundLeaf := by
  intro G T lookup X d₀ hrows heq
  intro p a x hx
  have hpcode : phaseCode (phase p.val) = p.val := by
    have hp := p.isLt
    interval_cases p.val <;> rfl
  let key := phaseKey p.val a.val
  have hkey : key < 14964 := by
    dsimp [key, phaseKey]
    have ha := a.isLt
    have hp := p.isLt
    omega
  have hc := hrows (phase p.val) a
  rw [hpcode] at hc
  have hcparts := hc
  simp only [planeCheck, Bool.and_eq_true, and_assoc] at hcparts
  have hrect : (rectangle (T.plane key) == T.endpoint key) = true := by
    simpa [key] using hcparts.2.2.2.2.2.2.2
  have hrectEq : rectangle (T.plane key) = T.endpoint key := by
    simpa only [beq_iff_eq] using hrect
  have hendpoint : T.endpoint key = lookup.endpoint key := heq key hkey
  have hrectangle := rectangle_endpoint_lane (T.plane key) x hx
  have hcoords : -13 ≤ x.1 ∧ x.1 ≤ 11 ∧ -12 ≤ x.2 ∧ x.2 ≤ 12 := by
    change decide (-13 ≤ x.1 ∧ x.1 ≤ 11 ∧ -12 ≤ x.2 ∧ x.2 ≤ 12) = true at hx
    exact of_decide_eq_true hx
  have hxbox : x ∈ square (0, 0) certificateRadius := by
    rw [mem_square_iff]
    unfold inBox
    rcases hcoords with ⟨h1, h2, h3, h4⟩
    exact ⟨by omega, by omega, by omega, by omega⟩
  have hxInBox : inBox x := by
    unfold inBox
    rcases hcoords with ⟨h1, h2, h3, h4⟩
    exact ⟨by omega, by omega, by omega, by omega⟩
  have hext : T.data.extended (phase p.val) a x =
      lane (T.planeFn (phase p.val) a) 80 (siteIndex x) := by
    change (dataOf T.planeFn T.capFn).extended (phase p.val) a x = _
    rw [extended_view]
    simp [valueAt, hxInBox]
  have hplaneKey : T.planeFn (phase p.val) a = T.plane key := by
    dsimp [Tables.planeFn, key, phaseKey]
    rw [hpcode]
  change endpointValue lookup p.val a.val x = T.data.extended (phase p.val) a x
  rw [hext]
  dsimp [endpointValue, key, phaseKey]
  calc
    lane (lookup.endpoint (phaseKey p.val a.val)) 80 (endpointIndex x) =
        lane (T.endpoint (phaseKey p.val a.val)) 80 (endpointIndex x) := by rw [hendpoint]
    _ = lane (rectangle (T.plane (phaseKey p.val a.val))) 80 (endpointIndex x) := by
      rw [hrectEq]
    _ = lane (T.planeFn (phase p.val) a) 80 (siteIndex x) := by
      rw [hplaneKey]
      exact hrectangle

#print axioms main

end AKLT.W.H3C041
