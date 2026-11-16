import AKLT.W.H1C015.Algebra

namespace AKLT.W.H1C015

open AKLT.Cert.H1 AKLT.Cert.H1.Production
open scoped BigOperators

def lanes (ss : List SectorSite) : Nat :=
  (ss.map fun s => s.coordinates.length).prod

@[simp] theorem lanes_nil : lanes [] = 1 := rfl
@[simp] theorem lanes_cons (s : SectorSite) (ss : List SectorSite) :
    lanes (s :: ss) = s.coordinates.length * lanes ss := rfl

/-- Each site's place value is the number of columns in the remaining sites. -/
def Strides : List SectorSite → Prop
  | [] => True
  | s :: ss => s.stride = lanes ss ∧ Strides ss

theorem strides_of_indexed (ss : List SectorSite)
    (h : ∀ (i : Nat) (hi : i < ss.length), ss[i].stride = lanes (ss.drop (i+1))) :
    Strides ss := by
  induction ss with
  | nil => trivial
  | cons s ss ih =>
      constructor
      · have h0 := h 0 (by simp)
        rw [List.getElem_cons_zero] at h0
        simpa only [List.drop_succ_cons, List.drop_zero] using h0
      · apply ih
        intro i hi
        have hs := h (i+1) (by simpa using Nat.succ_lt_succ hi)
        rw [List.getElem_cons_succ] at hs
        simpa only [List.drop_succ_cons] using hs

theorem strides_of_check (base : List PackedSite) (parity : Nat) (ss : List SectorSite)
    (h : sectorNetworkCheck base parity ss = true) : Strides ss := by
  unfold sectorNetworkCheck at h
  obtain ⟨hlen, hall⟩ := Bool.and_eq_true_iff.mp h
  have hlen' : ss.length = base.length := by simpa using hlen
  apply strides_of_indexed
  intro i hi
  have hz : i < (base.zip ss).length := by
    simpa only [List.length_zip, ← hlen', Nat.min_self] using hi
  have hs := List.forall_mem_zipIdx'.mp (List.all_eq_true.mp hall) i hz
  simp only [List.getElem_zip] at hs
  have hstride := (Bool.and_eq_true_iff.mp hs).2
  simpa only [beq_iff_eq, lanes] using hstride

theorem digit_period (a m n c : Nat) :
    (a*(m*n)+c) / n % m = c / n % m := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    rw [show a*(m*n)+c = c+(a*m)*n by ring,
      Nat.add_mul_div_right c (a*m) hn', Nat.add_mul_mod_self_right]

theorem direct_product_period : ∀ (ss : List SectorSite), Strides ss →
    ∀ (row a col : Nat) (codes : List Nat),
    directSectorRingProduct row (a*lanes ss+col) ss codes =
      directSectorRingProduct row col ss codes := by
  intro ss
  induction ss with
  | nil => intros; rfl
  | cons s ss ih =>
      intro h row a col codes
      obtain ⟨hstride, ht⟩ := h
      have hd : (a*lanes (s::ss)+col) / s.stride % s.coordinates.length =
          col / s.stride % s.coordinates.length := by
        rw [lanes_cons, hstride]
        exact digit_period a s.coordinates.length (lanes ss) col
      have hm : directSectorSiteMatrix s row (a*lanes (s::ss)+col) (codes.headD 0) =
          directSectorSiteMatrix s row col (codes.headD 0) := by
        unfold directSectorSiteMatrix
        rw [hd]
      simp only [directSectorRingProduct]
      rw [hm]
      congr 1
      rw [lanes_cons, show a*(s.coordinates.length*lanes ss)+col =
        (a*s.coordinates.length)*lanes ss+col by ring]
      exact ih ht row (a*s.coordinates.length) col codes.tail

def coefficient (s : SectorSite) (row digit v i j : Nat) : R :=
  value (s.base.table.get (tableIndex s.base.spec.dim
    (s.coordinates.getD (row / s.stride % s.coordinates.length) 0) i j v
    (s.coordinates.getD digit 0)))

theorem entry_direct_site (s : SectorSite) (row col v i j : Nat)
    (hi : i < 4) (hj : j < 4) :
    entry (directSectorSiteMatrix s row col v) i j =
      coefficient s row (col / s.stride % s.coordinates.length) v i j := by
  unfold entry directSectorSiteMatrix
  rw [matrixEntry_map _ i j hi hj]
  rfl

theorem entry_packed_site (s : SectorSite) (row v width i j : Nat)
    (hi : i < 4) (hj : j < 4) :
    entry (sectorSiteMatrix s row v width) i j =
      ∑ digit ∈ Finset.range s.coordinates.length,
        coefficient s row digit v i j * weight width (digit*s.stride) := by
  unfold entry sectorSiteMatrix
  rw [matrixEntry_map _ i j hi hj, value_pack_map _ _ _ 0]
  have hb : (((2 : Nat)^(width*s.stride) : Int) : R) = weight width s.stride := by
    simp [weight]
  simp only [hb, weight_pow]
  rfl

theorem digit_block (a m n b : Nat) (ha : a < m) (hb : b < n) :
    (a*n+b) / n % m = a := by
  rw [Nat.mul_comm a n, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hb,
    Nat.add_zero, Nat.mod_eq_of_lt ha]

/-- The ring product is the evaluation of its column polynomial. -/
theorem product_expansion : ∀ (ss : List SectorSite), Strides ss →
    ∀ (row width : Nat) (codes : List Nat) (i j : Nat), i < 4 → j < 4 →
    entry (sectorRingProduct row width ss codes) i j =
      ∑ col ∈ Finset.range (lanes ss),
        entry (directSectorRingProduct row col ss codes) i j * weight width col := by
  intro ss
  induction ss with
  | nil =>
      intro h row width codes i j hi hj
      simp only [sectorRingProduct, directSectorRingProduct, lanes_nil,
        Finset.sum_range_one, weight_zero, mul_one]
  | cons s ss ih =>
      intro h row width codes i j hi hj
      obtain ⟨hstride, ht⟩ := h
      let C := fun a k => coefficient s row a (codes.headD 0) i k
      let D := fun b k => entry (directSectorRingProduct row b ss codes.tail) k j
      calc
        entry (sectorRingProduct row width (s::ss) codes) i j =
            ∑ k ∈ Finset.range 4,
              (∑ a ∈ Finset.range s.coordinates.length,
                C a k * weight width (a*lanes ss)) *
              (∑ b ∈ Finset.range (lanes ss), D b k * weight width b) := by
          rw [sectorRingProduct, entry_mul _ _ i j hi hj]
          apply Finset.sum_congr rfl
          intro k hk
          rw [entry_packed_site s row (codes.headD 0) width i k hi
            (Finset.mem_range.mp hk),
            ih ht row width codes.tail k j (Finset.mem_range.mp hk) hj, hstride]
        _ = ∑ a ∈ Finset.range s.coordinates.length,
              ∑ b ∈ Finset.range (lanes ss), ∑ k ∈ Finset.range 4,
                C a k * D b k * weight width (a*lanes ss+b) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro k hk
          rw [weight_add]
          ring
        _ = ∑ col ∈ Finset.range (lanes (s::ss)),
              entry (directSectorRingProduct row col (s::ss) codes) i j *
                weight width col := by
          rw [lanes_cons, sum_blocks]
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          rw [directSectorRingProduct, entry_mul _ _ i j hi hj, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          rw [entry_direct_site s row (a*lanes ss+b) (codes.headD 0) i k hi
            (Finset.mem_range.mp hk), hstride,
            digit_block a s.coordinates.length (lanes ss) b
              (Finset.mem_range.mp ha) (Finset.mem_range.mp hb),
            direct_product_period ss ht row a b codes.tail]

theorem ring_expansion (ss : List SectorSite) (h : Strides ss)
    (row width : Nat) (codes : List Nat) :
    value (sectorRingValue ss row width codes) =
      ∑ col ∈ Finset.range (lanes ss),
        value (directSectorRingValue ss row col codes) * weight width col := by
  unfold sectorRingValue directSectorRingValue
  simp only [value_trace]
  calc
    (∑ i ∈ Finset.range 4, entry (sectorRingProduct row width ss codes) i i) =
        ∑ i ∈ Finset.range 4, ∑ col ∈ Finset.range (lanes ss),
          entry (directSectorRingProduct row col ss codes) i i * weight width col := by
      apply Finset.sum_congr rfl
      intro i hi
      exact product_expansion ss h row width codes i i
        (Finset.mem_range.mp hi) (Finset.mem_range.mp hi)
    _ = ∑ col ∈ Finset.range (lanes ss),
        (∑ i ∈ Finset.range 4, entry (directSectorRingProduct row col ss codes) i i) *
          weight width col := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]

end AKLT.W.H1C015
