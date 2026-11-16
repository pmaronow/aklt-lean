import CertData.H3.Bridge.Interface

set_option maxRecDepth 100000

namespace AKLT.W.H3C020

open AKLT.Defs AKLT.Gen.Packed AKLT.Cert.H3

private theorem packFn_shift (B n : Nat) (f : Nat → Nat)
    (hf : f 0 < 2^B) :
    packFn B (n+1) f >>> B = packFn B n (fun i => f (i+1)) := by
  rw [Nat.shiftRight_eq_div_pow, packFn]
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hf]
  simp

private theorem packFn_drop (B n k : Nat) (f : Nat → Nat)
    (hf : ∀ i < n, f i < 2^B) (hk : k ≤ n) :
    packFn B n f >>> (B*k) = packFn B (n-k) (fun i => f (i+k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkn : k < n := by omega
    have hshift : packFn B n f >>> (B*(k+1)) =
        (packFn B n f >>> (B*k)) >>> B := by
      simp only [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
      rw [Nat.mul_add, Nat.mul_one, ← pow_add]
    rw [hshift, ih (by omega)]
    have htail := packFn_shift B (n-k-1) (fun i => f (i+k)) (by simpa using hf k hkn)
    have hsize : (n-k-1)+1 = n-k := by omega
    rw [hsize] at htail
    rw [htail]
    rw [show n-k-1 = n-(k+1) by omega]
    congr 1
    funext i
    congr 1
    omega

private theorem packFn_blockHead (b w n : Nat) (f : Nat → Nat)
    (hf0 : f 0 < 2^b)
    (hw : 0 < w) (c : Nat) (hc : c < w) :
    lane (packFn (b*w) (n+1) f) b c = lane (f 0) b c := by
  have hpow : 2^(b*w) = 2^(b*c) * 2^(b*(w-c)) := by
    rw [← pow_add]
    congr 1
    rw [← Nat.mul_add]
    congr 1
    omega
  have hdiv :
      (f 0 + 2^(b*w) * packFn (b*w) n (fun i => f (i+1))) / 2^(b*c) =
        f 0 / 2^(b*c) + 2^(b*(w-c)) * packFn (b*w) n (fun i => f (i+1)) := by
    have hfactor : 2^(b*w) * packFn (b*w) n (fun i => f (i+1)) =
        2^(b*c) * (2^(b*(w-c)) * packFn (b*w) n (fun i => f (i+1))) := by
      rw [hpow]
      ring
    rw [hfactor, Nat.add_mul_div_left _ _ (by positivity)]
  simp only [lane, Nat.shiftRight_eq_div_pow]
  rw [packFn, hdiv]
  by_cases hc0 : c = 0
  · subst c
    simp only [Nat.mul_zero, pow_zero, Nat.div_one, Nat.sub_zero] at *
    have hexp : b ≤ b*w := by
      calc b = b*1 := by simp
        _ ≤ b*w := Nat.mul_le_mul_left b (by omega)
    have hpow' : 2^(b*w) = 2^b * 2^(b*w-b) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow']
    have hfactor : 2^b * 2^(b*w-b) * packFn (b*w) n (fun i => f (i+1)) =
        2^b * (2^(b*w-b) * packFn (b*w) n (fun i => f (i+1))) := by ring
    rw [hfactor, Nat.add_mul_mod_self_left]
  · have hcpos : 0 < c := by omega
    have hlow : f 0 / 2^(b*c) = 0 := by
      apply Nat.div_eq_of_lt
      have hbc : b ≤ b*c := by
        simpa using Nat.mul_le_mul_left b (Nat.succ_le_iff.mpr hcpos)
      exact lt_of_lt_of_le hf0 (Nat.pow_le_pow_right (by decide) hbc)
    have hexp : b ≤ b*(w-c) := by
      have hpos : 0 < w-c := Nat.sub_pos_of_lt hc
      have hsub : 1 ≤ w-c := Nat.succ_le_iff.mpr hpos
      calc b = b*1 := by simp
        _ ≤ b*(w-c) := Nat.mul_le_mul_left b hsub
    have hmultiple : 2^b ∣ 2^(b*(w-c)) := Nat.pow_dvd_pow 2 hexp
    rw [hlow, Nat.zero_add]
    have hz : (2^(b*(w-c)) * packFn (b*w) n (fun i => f (i+1))) % 2^b = 0 :=
      Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hmultiple _)
    rw [hz]
    simp

private theorem lane_repeatLane (b n v s : Nat) (hb : 0 < b) (hv : v < 2^b) :
    lane (repeatLane b n v) b s = if s < n then v else 0 := by
  rw [repeatLane_eq b n v hb]
  exact lane_packFn b n (fun _ => v) (by intro i hi; exact hv) s

private theorem repeatLane_full (b n : Nat) (hb : 0 < b) :
    repeatLane b n (2^b-1) = 2^(b*n)-1 := by
  unfold repeatLane
  have hv : 0 < 2^b-1 := by
    have hp : 1 < 2^b := Nat.one_lt_pow (by omega : b ≠ 0) (by decide : 1 < 2)
    omega
  rw [Nat.mul_comm (2^(b*n)-1) (2^b-1), Nat.mul_div_cancel_left _ hv]

private theorem lane_firstColumn (s : Nat) :
    lane firstColumn 80 s = if s < 19881 ∧ s % 141 = 0 then 2^80-1 else 0 := by
  have hcol : firstColumn = packFn (80*141) 141 (fun _ => 2^80-1) := by
    unfold firstColumn
    exact repeatLane_eq (80*141) 141 (2^80-1) (by positivity)
  have hv : 2^80-1 < 2^(80*141) := by
    have hlt : 2^80-1 < 2^80 := Nat.sub_lt (by positivity) (by decide)
    exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))
  have hfit : Fits firstColumn 80 19881 := by
    rw [hcol]
    have h := packFn_lt (80*141) 141 (fun _ => 2^80-1) (by intro i hi; exact hv)
    change packFn (80*141) 141 (fun _ => 2^80-1) < 2^(11280*141) at h
    change packFn (80*141) 141 (fun _ => 2^80-1) < 2^(80*19881)
    norm_num at h ⊢
    exact h
  by_cases hs : s < 19881
  · let q := s / 141
    let c := s % 141
    have hq : q < 141 := by dsimp [q]; omega
    have hc : c < 141 := by dsimp [c]; exact Nat.mod_lt _ (by decide)
    have hdrop := packFn_drop (80*141) 141 q (fun _ => 2^80-1)
      (by intro i hi; exact hv) (by omega)
    have hindex : s = 141*q+c := by dsimp [q,c]; exact (Nat.div_add_mod s 141).symm
    have hindex' : c+(141*q)=s := by omega
    have hshift : lane firstColumn 80 s =
        lane (firstColumn >>> (80*(141*q))) 80 c := by
      rw [← hindex']
      rw [← lane_shiftRight firstColumn 80 (141*q) c]
    rw [hshift, hcol]
    have hdrop' : packFn (80*141) 141 (fun _ => 2^80-1) >>>
        ((80*141)*q) = packFn (80*141) (141-q) (fun _ => 2^80-1) := hdrop
    have hmul : 80*(141*q) = (80*141)*q := by ring
    rw [hmul, hdrop']
    have htail : lane (packFn (80*141) (141-q) (fun _ => 2^80-1)) 80 c =
        lane (2^80-1) 80 c := by
      have hn : 141-q = (140-q)+1 := by omega
      rw [hn]
      exact packFn_blockHead 80 141 (140-q) (fun _ => 2^80-1) (by omega)
        (by norm_num) c hc
    rw [htail]
    have hcell : lane (2^80-1) 80 c = if c = 0 then 2^80-1 else 0 := by
      cases c with
      | zero => simp [lane]
      | succ c =>
        have hlt : 2^80-1 < 2^(80*(c+1)) := by
          have hbase : 2^80-1 < 2^80 := Nat.sub_lt (by positivity) (by decide)
          exact lt_of_lt_of_le hbase
            (Nat.pow_le_pow_right (by decide) (by omega))
        simp only [lane, Nat.shiftRight_eq_div_pow]
        rw [Nat.div_eq_of_lt hlt]
        simp
    rw [hcell]
    have hcong : (s % 141 = 0) ↔ c = 0 := by rfl
    simp [q, c, hs, hq, hc, hcong]
  · rw [lane_eq_zero_of_fits hfit s (by omega)]
    simp [hs]

private theorem lane_firstRow (s : Nat) :
    lane firstRow 80 s = if s < 141 then 2^80-1 else 0 := by
  unfold firstRow
  rw [← repeatLane_full 80 141 (by decide)]
  exact lane_repeatLane 80 141 (2^80-1) s (by decide)
    (Nat.sub_lt (by positivity) (by decide))

private theorem lane_lastRow (s : Nat) (hs : s < 19881) :
    lane lastRow 80 s = if s / 141 = 140 then 2^80-1 else 0 := by
  unfold lastRow
  rw [lane_shiftLeft _ _ _ _ (by decide), lane_firstRow]
  split_ifs <;> simp_all <;> omega

private theorem lane_lastColumn (s : Nat) (hs : s < 19881) :
    lane lastColumn 80 s = if s % 141 = 140 then 2^80-1 else 0 := by
  unfold lastColumn
  rw [lane_shiftLeft _ _ _ _ (by decide), lane_firstColumn]
  by_cases h : s % 141 = 140
  · have hs140 : 140 ≤ s := by omega
    have hmod : (s-140) % 141 = 0 := by omega
    have hrem : s-140 < 19881 := by omega
    simp [hs140, hmod, hrem, h]
  · by_cases hs140 : 140 ≤ s
    · have hmod : (s-140) % 141 ≠ 0 := by
        intro hz
        apply h
        omega
      simp [hs140, hmod, h]
    · simp [hs140, h]

private theorem inBox_neighbor (s : Nat) (hs : s < 19881) (d : Compass) :
    inBox (gridSite s + d.step) ↔
      match d with
      | .east => s / 141 < 140
      | .north => s % 141 < 140
      | .west => 0 < s / 141
      | .south => 0 < s % 141 := by
  cases d <;> simp [inBox, gridSite, Compass.step] <;> omega

private theorem lane_boundaryMask (s : Nat) (hs : s < 19881) (d : Compass) :
    lane (boundaryMask d) 80 s =
      if inBox (gridSite s + d.step) then 0 else 2^80-1 := by
  cases d with
  | east =>
      rw [boundaryMask, lane_lastRow s hs]
      have hg := inBox_neighbor s hs Compass.east
      have hq : s / 141 < 141 := by omega
      by_cases h : s / 141 = 140 <;> simp [hg, h] <;> omega
  | north =>
      rw [boundaryMask, lane_lastColumn s hs]
      have hg := inBox_neighbor s hs Compass.north
      by_cases h : s % 141 = 140 <;> simp [hg, h] <;> omega
  | west =>
      rw [boundaryMask, lane_firstRow s]
      have hg := inBox_neighbor s hs Compass.west
      by_cases h : s < 141 <;> simp [hg, h] <;> omega
  | south =>
      rw [boundaryMask, lane_firstColumn s]
      have hg := inBox_neighbor s hs Compass.south
      by_cases h : s % 141 = 0 <;> simp [hg, h] <;> omega

private theorem boundary_fits (d : Compass) : Fits (boundaryMask d) 80 19881 := by
  cases d <;> unfold Fits boundaryMask lastRow firstRow lastColumn firstColumn <;>
    decide +kernel

private theorem allMask_fits : Fits allMask 80 19881 := by
  unfold Fits allMask
  exact Nat.sub_lt (by positivity) (by decide)

private theorem lane_allMask (s : Nat) (hs : s < 19881) :
    lane allMask 80 s = 2^80-1 := by
  unfold allMask
  rw [← repeatLane_full 80 19881 (by decide)]
  rw [lane_repeatLane 80 19881 (2^80-1) s (by decide)
    (Nat.sub_lt (by positivity) (by decide)), if_pos hs]

private theorem lane_sub_allones {A B b n : Nat} (hA : Fits A b n)
    (hAfull : ∀ i < n, lane A b i = 2^b-1) (hB : Fits B b n)
    (s : Nat) (hs : s < n) :
    lane (A-B) b s = 2^b-1-lane B b s := by
  let f : Nat → Nat := fun i => 2^b-1-lane B b i
  have hf : ∀ i < n, f i < 2^b := by
    intro i hi
    dsimp [f]
    have hlt := lane_lt B b i
    omega
  have hrepr : packFn b n f + B = A := by
    rw [← packFn_lanes B b n hB, ← packFn_add]
    rw [← packFn_lanes A b n hA]
    apply packFn_congr
    intro i hi
    simp only [f]
    rw [hAfull i hi]
    have hle : lane B b i ≤ 2^b-1 := by have := lane_lt B b i; omega
    rw [Nat.sub_add_cancel hle]
  have hsub : A-B = packFn b n f := by omega
  rw [hsub, lane_packFn b n f hf, ite_eq_left hs]

private theorem lane_insideMask (s : Nat) (hs : s < 19881) (d : Compass) :
    lane (allMask-boundaryMask d) 80 s =
      if inBox (gridSite s+d.step) then 2^80-1 else 0 := by
  rw [lane_sub_allones allMask_fits (fun i hi => lane_allMask i hi)
    (boundary_fits d) s hs, lane_boundaryMask s hs d]
  split_ifs <;> simp

private def pullShift (P : Nat) : Compass → Nat
  | .east => P >>> (80*141)
  | .north => P >>> 80
  | .west => P <<< (80*141)
  | .south => P <<< 80

private theorem siteIndex_neighbor (s : Nat) (hs : s < 19881) (d : Compass)
    (hbox : inBox (gridSite s+d.step)) :
    siteIndex (gridSite s+d.step) =
      match d with
      | .east => s+141
      | .north => s+1
      | .west => s-141
      | .south => s-1 := by
  cases d <;> simp [inBox, gridSite, siteIndex, Compass.step] at hbox ⊢ <;> omega

private theorem pullShift_lane (P : Nat) (s : Nat) (hs : s < 19881) (d : Compass)
    (hbox : inBox (gridSite s+d.step)) :
    lane (pullShift P d) 80 s = lane P 80 (siteIndex (gridSite s+d.step)) := by
  cases d with
  | east =>
      change lane (P >>> (80*141)) 80 s = _
      rw [lane_shiftRight]
      rw [siteIndex_neighbor s hs .east hbox]
  | north =>
      change lane (P >>> 80) 80 s = _
      rw [siteIndex_neighbor s hs .north hbox]
      have h := lane_shiftRight P 80 1 s
      simpa only [Nat.mul_one] using h
  | west =>
      change lane (P <<< (80*141)) 80 s = _
      rw [siteIndex_neighbor s hs .west hbox]
      rw [lane_shiftLeft _ _ _ _ (by decide)]
      have hrow : 0 < s / 141 := (inBox_neighbor s hs .west).mp hbox
      have hge : 141 ≤ s := by omega
      simp [hge]
  | south =>
      change lane (P <<< 80) 80 s = _
      rw [siteIndex_neighbor s hs .south hbox]
      have hcol : 0 < s % 141 := (inBox_neighbor s hs .south).mp hbox
      have hge : 1 ≤ s := by omega
      rw [show 80 = 80*1 by ring, lane_shiftLeft P 80 1 s (by decide)]
      simp [hge]

private theorem repeatLane_fits (b n v : Nat) (hb : 0 < b) (hv : v < 2^b) :
    Fits (repeatLane b n v) b n := by
  rw [repeatLane_eq b n v hb]
  exact packFn_lt b n (fun _ => v) (by intro i hi; exact hv)

private theorem pull_lane_core (P Z : Nat) (d : Compass) (s : Nat)
    (hs : s < 19881) (hZ : Z < 2^80) :
    lane (pull P Z d) 80 s =
      if inBox (gridSite s+d.step) then lane (pullShift P d) 80 s else Z := by
  let A := Nat.land (pullShift P d) (allMask-boundaryMask d)
  let B := Nat.land (repeatLane 80 19881 Z) (boundaryMask d)
  have hAfit : Fits A 80 19881 := by
    change Nat.land (pullShift P d) (allMask-boundaryMask d) < 2^(80*19881)
    have hm : allMask-boundaryMask d ≤ allMask := Nat.sub_le _ _
    have hall : allMask < 2^(80*19881) := allMask_fits
    exact lt_of_le_of_lt (Nat.and_le_right.trans hm) hall
  have hBfit : Fits B 80 19881 := by
    change Nat.land (repeatLane 80 19881 Z) (boundaryMask d) < 2^(80*19881)
    have hcap := repeatLane_fits 80 19881 Z (by decide) hZ
    change repeatLane 80 19881 Z < 2^(80*19881) at hcap
    exact lt_of_le_of_lt Nat.and_le_left hcap
  have hA_lane (i : Nat) (hi : i < 19881) :
      lane A 80 i = if inBox (gridSite i+d.step) then lane (pullShift P d) 80 i else 0 := by
    change lane (Nat.land (pullShift P d) (allMask-boundaryMask d)) 80 i = _
    rw [lane_land, lane_insideMask i hi d]
    split_ifs with h
    · exact Nat.and_two_pow_sub_one_of_lt_two_pow (lane_lt _ _ _)
    · simp
  have hB_lane (i : Nat) (hi : i < 19881) :
      lane B 80 i = if inBox (gridSite i+d.step) then 0 else Z := by
    change lane (Nat.land (repeatLane 80 19881 Z) (boundaryMask d)) 80 i = _
    rw [lane_land, lane_repeatLane 80 19881 Z i (by decide) hZ,
      lane_boundaryMask i hi d]
    split_ifs with h
    · simp [h]
    · exact Nat.and_two_pow_sub_one_of_lt_two_pow hZ
  have hnocarry : ∀ i < 19881, lane A 80 i + lane B 80 i < 2^80 := by
    intro i hi
    rw [hA_lane i hi, hB_lane i hi]
    by_cases h : inBox (gridSite i+d.step)
    · simp [h]
      exact lane_lt (pullShift P d) 80 i
    · simp [h]
      exact hZ
  rw [show pull P Z d = A+B by rfl]
  rw [lane_add hAfit hBfit hnocarry s hs, hA_lane s hs, hB_lane s hs]
  split_ifs <;> simp

theorem main : CertData.H3.Bridge.PullLeaf := by
  intro P Z d hP hZ s hs
  have hZ80 : Z < 2^80 := lt_of_lt_of_le hZ (by norm_num)
  rw [pull_lane_core P Z d s hs hZ80]
  split_ifs with h
  · rw [pullShift_lane P s hs d h]
  · rfl

#print axioms main

#print axioms packFn_shift

end AKLT.W.H3C020
