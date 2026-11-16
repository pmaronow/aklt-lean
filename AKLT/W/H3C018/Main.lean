import CertData.H3.Bridge.Interface

namespace AKLT.W.H3C018

open AKLT.Cert.H3.Production AKLT.Gen.Packed

private theorem chunk_fits {A B b m n : Nat}
    (hA : Fits A b m) (hB : Fits B b n) :
    Fits (A + (B <<< (b*m))) b (m+n) := by
  dsimp [Fits] at hA hB ⊢
  rw [Nat.shiftLeft_eq, Nat.mul_add, pow_add]
  let p := 2 ^ (b*m)
  let q := 2 ^ (b*n)
  have hp : 0 < p := by positivity
  have hq : 0 < q := by positivity
  have hA' : A ≤ p - 1 := by omega
  have hB' : B ≤ q - 1 := by omega
  have hmul : B*p ≤ (q-1)*p := Nat.mul_le_mul_right p hB'
  have hBp : B*p + p ≤ q*p := by
    have hqsub : q-1+1=q := Nat.sub_add_cancel (by omega)
    calc
      B*p+p ≤ (q-1)*p+p := Nat.add_le_add_right hmul p
      _ = (q-1+1)*p := by
        rw [Nat.add_mul]
        simp
      _ = q*p := by rw [hqsub]
  have htotal : A + B*p < p*q := by
    calc
      A+B*p < p+B*p := Nat.add_lt_add_right (by simpa [p] using hA) (B*p)
      _ = B*p+p := by omega
      _ ≤ q*p := hBp
      _ = p*q := Nat.mul_comm _ _
  simpa [p, q, Nat.mul_comm] using htotal

private theorem lane_chunk {A B b m n s : Nat}
    (hA : Fits A b m) (hB : Fits B b n) (hb : 0 < b) :
    lane (A + (B <<< (b*m))) b s =
      if s < m then lane A b s else lane B b (s-m) := by
  have hAext : Fits A b (m+n) := by
    dsimp [Fits] at hA ⊢
    rw [Nat.mul_add, pow_add]
    have hmul : 2 ^ (b*m) ≤ 2 ^ (b*m) * 2 ^ (b*n) :=
      Nat.le_mul_of_pos_right _ (by positivity)
    exact lt_of_lt_of_le hA (by simpa [pow_add] using hmul)
  have hShift : Fits (B <<< (b*m)) b (m+n) := by
    dsimp [Fits] at hB ⊢
    rw [Nat.shiftLeft_eq, Nat.mul_add, pow_add]
    have hmul := Nat.mul_lt_mul_of_pos_right hB (by positivity : 0 < 2 ^ (b*m))
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  have hadd : ∀ t < m+n,
      lane A b t + lane (B <<< (b*m)) b t < 2^b := by
    intro t ht
    by_cases htm : t < m
    · rw [lane_shiftLeft _ _ _ _ hb]
      have hnot : ¬ m ≤ t := by omega
      rw [if_neg hnot]
      exact lane_lt A b t
    · have hzero : lane A b t = 0 := lane_eq_zero_of_fits hA t (by omega)
      rw [hzero, lane_shiftLeft _ _ _ _ hb]
      have hmt : m ≤ t := by omega
      rw [if_pos hmt]
      simpa using lane_lt B b (t-m)
  have hAB := chunk_fits hA hB
  by_cases hrange : s < m+n
  · have hsum := lane_add hAext hShift hadd s hrange
    rw [hsum]
    by_cases hs : s < m
    · rw [if_pos hs, lane_shiftLeft _ _ _ _ hb]
      have hnot : ¬ m ≤ s := by omega
      simp [hnot]
    · rw [if_neg hs, lane_shiftLeft _ _ _ _ hb]
      have hms : m ≤ s := by omega
      have hzero : lane A b s = 0 := lane_eq_zero_of_fits hA s (by omega)
      simp [hms, hzero]
  · have hzeroOut : lane (A + (B <<< (b*m))) b s = 0 :=
      lane_eq_zero_of_fits hAB s (by omega)
    have hzeroB : lane B b (s-m) = 0 := lane_eq_zero_of_fits hB (s-m) (by omega)
    rw [hzeroOut, hzeroB]
    simp [Nat.not_lt_of_ge (by omega : m ≤ s)]

private def chunks : List Nat → Nat
  | [] => 0
  | a :: xs => a + (chunks xs <<< (80*25))

private theorem chunks_foldr (xs : List Nat) :
    chunks xs = xs.foldr (fun a rest => a + (rest <<< (80*25))) 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      change a + (chunks xs <<< (80*25)) =
        a + ((xs.foldr (fun a rest => a + (rest <<< (80*25))) 0) <<< (80*25))
      rw [ih]

private theorem chunks_fits (xs : List Nat)
    (hxs : ∀ a ∈ xs, Fits a 80 25) : Fits (chunks xs) 80 (25*xs.length) := by
  induction xs with
  | nil => change 0 < 2^(80*0); decide
  | cons a xs ih =>
      have ha : Fits a 80 25 := hxs a List.mem_cons_self
      have htail : ∀ b ∈ xs, Fits b 80 25 := by
        intro b hb
        exact hxs b (List.mem_cons_of_mem a hb)
      have hxs' := ih htail
      have hchunk := chunk_fits ha hxs'
      change Fits (a + (chunks xs <<< (80*25))) 80 (25*(xs.length+1))
      simpa only [Nat.mul_succ, Nat.add_comm] using hchunk

set_option maxHeartbeats 1000000 in
private theorem chunks_lane_at (xs : List Nat)
    (hxs : ∀ a ∈ xs, Fits a 80 25) {r c : Nat}
    (hr : r < xs.length) (hc : c < 25) :
    lane (chunks xs) 80 (r*25+c) = lane (xs[r]?.getD 0) 80 c := by
  induction xs generalizing r with
  | nil => simp at hr
  | cons a xs ih =>
      have ha : Fits a 80 25 := hxs a List.mem_cons_self
      have htail : ∀ b ∈ xs, Fits b 80 25 := by
        intro b hb
        exact hxs b (List.mem_cons_of_mem a hb)
      have htailFits := chunks_fits xs htail
      cases r with
      | zero =>
          simp only [Nat.zero_mul, Nat.zero_add]
          change lane (a + (chunks xs <<< (80*25))) 80 c =
            lane ((a::xs)[0]?.getD 0) 80 c
          have hsplit := lane_chunk (s := c) ha htailFits (by decide : 0 < 80)
          rw [hsplit]
          simp only [List.getElem?_cons_zero, Option.getD_some, if_pos hc]
      | succ r =>
          change lane (a + (chunks xs <<< (80*25))) 80 ((r+1)*25+c) =
            lane ((a::xs)[r+1]?.getD 0) 80 c
          rw [List.getElem?_cons_succ]
          have hsplit := lane_chunk (s := (r+1)*25+c) ha htailFits (by decide : 0 < 80)
          have hnot : ¬ (r+1)*25+c < 25 := by omega
          have hsub : (r+1)*25+c-25 = r*25+c := by omega
          rw [hsplit, if_neg hnot, hsub]
          have hr' : r < xs.length := by simp at hr; omega
          simpa using ih htail hr'

private def rectangleRow (P r : Nat) : Nat :=
  Nat.land (P >>> (80*((r+57)*141+58))) (2^(80*25)-1)

private theorem rectangle_eq_chunks (P : Nat) :
    AKLT.Cert.H3.Production.rectangle P =
      chunks ((List.range 25).map (rectangleRow P)) := by
  unfold AKLT.Cert.H3.Production.rectangle
  rw [chunks_foldr, List.foldr_map]
  rfl

private theorem rectangleRow_fits (P r : Nat) : Fits (rectangleRow P r) 80 25 := by
  dsimp [Fits, rectangleRow]
  exact lt_of_le_of_lt Nat.and_le_right (by
    have hp : 0 < 2^(80*25) := by positivity
    omega)

private theorem lane_rectangleMask (c : Nat) (hc : c < 25) :
    lane (2^(80*25)-1) 80 c = 2^80-1 := by
  have hrep : repeatLane 80 25 (2^80-1) = 2^(80*25)-1 := by
    simp [repeatLane]
  rw [← hrep, repeatLane_eq 80 25 (2^80-1) (by decide : 0 < 80)]
  rw [lane_packFn]
  · simp [hc]
  · intro s hs
    omega

private theorem rectangleRow_lane (P r c : Nat) (hc : c < 25) :
    lane (rectangleRow P r) 80 c = lane P 80 ((r+57)*141+58+c) := by
  unfold rectangleRow
  rw [lane_land, lane_rectangleMask c hc]
  have hlt := lane_lt (P >>> (80*((r+57)*141+58))) 80 c
  calc
    Nat.land (lane (P >>> (80*((r+57)*141+58))) 80 c) (2^80-1) =
        lane (P >>> (80*((r+57)*141+58))) 80 c :=
          Nat.and_two_pow_sub_one_of_lt_two_pow hlt
    _ = lane P 80 ((r+57)*141+58+c) := by
      simpa [Nat.add_comm] using lane_shiftRight P 80 ((r+57)*141+58) c

theorem main : CertData.H3.Bridge.RectangleLeaf := by
  intro P hP x hx
  have hxbox : -13 ≤ x.1 ∧ x.1 ≤ 11 ∧ -12 ≤ x.2 ∧ x.2 ≤ 12 := by
    simpa [endpointInside] using hx
  rcases hxbox with ⟨hxlo, hxhi, hylo, hyhi⟩
  have hr : (x.1+13).toNat < 25 := by
    have hn : 0 ≤ x.1+13 := by omega
    exact (Int.toNat_lt_of_ne_zero (m := x.1+13) (by decide : 25 ≠ 0)).2 (by omega)
  have hc : (x.2+12).toNat < 25 := by
    have hn : 0 ≤ x.2+12 := by omega
    exact (Int.toNat_lt_of_ne_zero (m := x.2+12) (by decide : 25 ≠ 0)).2 (by omega)
  have hrow : (x.1+70).toNat = (x.1+13).toNat+57 := by
    have h₁ : 0 ≤ x.1+70 := by omega
    have h₂ : 0 ≤ x.1+13 := by omega
    have hcast : ((x.1+70).toNat : Int) = ((x.1+13).toNat : Int) + 57 := by
      rw [Int.toNat_of_nonneg h₁, Int.toNat_of_nonneg h₂]
      omega
    exact_mod_cast hcast
  have hcol : (x.2+70).toNat = (x.2+12).toNat+58 := by
    have h₁ : 0 ≤ x.2+70 := by omega
    have h₂ : 0 ≤ x.2+12 := by omega
    have hcast : ((x.2+70).toNat : Int) = ((x.2+12).toNat : Int) + 58 := by
      rw [Int.toNat_of_nonneg h₁, Int.toNat_of_nonneg h₂]
      omega
    exact_mod_cast hcast
  have hsite : AKLT.Cert.H3.siteIndex x =
      ((x.1+13).toNat+57)*141+((x.2+12).toNat+58) := by
    simp [AKLT.Cert.H3.siteIndex, hrow, hcol]
  have hendpoint : endpointIndex x = (x.1+13).toNat*25+(x.2+12).toNat := rfl
  rw [rectangle_eq_chunks]
  have hrows : ∀ a ∈ (List.range 25).map (rectangleRow P), Fits a 80 25 := by
    intro a ha
    rcases List.mem_map.mp ha with ⟨r, hrmem, rfl⟩
    exact rectangleRow_fits P r
  have hchunk := chunks_lane_at ((List.range 25).map (rectangleRow P)) hrows
    (r := (x.1+13).toNat) (c := (x.2+12).toNat) (by simpa using hr) hc
  have hindex : ((List.range 25).map (rectangleRow P))[(x.1+13).toNat]?.getD 0 =
      rectangleRow P ((x.1+13).toNat) := by simp [hr]
  rw [hendpoint, hchunk, hindex, rectangleRow_lane P _ _ hc, hsite]
  simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

end AKLT.W.H3C018
