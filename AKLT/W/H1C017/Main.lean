module
public import AKLT.Cert.H1.Production.Leaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

open scoped BigOperators

namespace AKLT.W.H1C017

private def packNat (b : Nat) {n : Nat} (d : Fin n → Nat) : Nat :=
  ∑ i : Fin n, d i * b ^ i.val

private theorem packNat_succ (b : Nat) {n : Nat} (d : Fin (n + 1) → Nat) :
    packNat b d = d 0 + b * packNat b (fun i => d i.succ) := by
  unfold packNat
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.pow_zero, Nat.mul_one, Fin.val_succ, Nat.pow_succ]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem div_head (b x y : Nat) (hx : x < b) :
    (x + b * y) / b = y := by
  apply Nat.div_eq_of_lt_le (k := y) (n := b) (m := x + b * y)
  · nlinarith
  · nlinarith

private theorem packNat_digit (b : Nat) : ∀ {n : Nat}
    (d : Fin n → Nat), (∀ i, d i < b) → ∀ i : Fin n,
    packNat b d / b ^ i.val % b = d i := by
  intro n
  induction n with
  | zero =>
      intro d hd i
      exact Fin.elim0 i
  | succ n ih =>
      intro d hd i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [packNat_succ]
        simp only [Fin.val_zero, Nat.pow_zero, Nat.div_one]
        rw [Nat.add_mod, Nat.mul_mod]
        simp [Nat.mod_eq_of_lt (hd 0)]
      · have hd' : ∀ k : Fin n, d k.succ < b := fun k => hd k.succ
        have hdrop : packNat b d / b = packNat b (fun k => d k.succ) := by
          rw [packNat_succ]
          exact div_head b (d 0) (packNat b (fun k => d k.succ)) (hd 0)
        have hdiv : packNat b d / b ^ (j.succ).val =
            packNat b (fun k => d k.succ) / b ^ j.val := by
          calc
            packNat b d / b ^ (j.succ).val =
                packNat b d / (b ^ j.val * b) := by rw [Fin.val_succ, Nat.pow_succ]
            _ = packNat b d / b / b ^ j.val := by
              rw [Nat.mul_comm]
              rw [← Nat.div_div_eq_div_mul]
            _ = packNat b (fun k => d k.succ) / b ^ j.val := by rw [hdrop]
        rw [hdiv]
        exact ih (fun k => d k.succ) hd' j

private theorem signedBias_eq_sum (width n : Nat) (hw : 0 < width) :
    AKLT.Cert.H1.signedBias width n =
      ∑ i : Fin n, ((2 : Nat) ^ (width - 1) : Int) *
        ((2 : Nat) ^ width : Int) ^ i.val := by
  let b : Nat := 2 ^ width
  let h : Nat := 2 ^ (width - 1)
  have hb : 2 ≤ b := by
    dsimp [b]
    cases width with
    | zero => omega
    | succ w =>
        rw [pow_succ]
        have hp : 1 ≤ 2 ^ w := Nat.one_le_pow w 2 (by omega)
        omega
  have hgeom : (b ^ n - 1) / (b - 1) = ∑ i : Fin n, b ^ i.val := by
    rw [Fin.sum_univ_eq_sum_range]
    exact (Nat.geomSum_eq hb n).symm
  have hnat : (b ^ n - 1) / (b - 1) * h =
      ∑ i : Fin n, h * b ^ i.val := by
    rw [hgeom]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hnat' : (2 ^ (width * n) - 1) / (2 ^ width - 1) * 2 ^ (width - 1) =
      ∑ i : Fin n, 2 ^ (width - 1) * (2 ^ width) ^ i.val := by
    simpa [b, h, Nat.pow_mul] using hnat
  unfold AKLT.Cert.H1.signedBias
  exact_mod_cast hnat'

private theorem pow_width_mul (width j : Nat) :
    ((2 : Nat) ^ (width * j) : Int) = ((2 : Nat) ^ width : Int) ^ j := by
  norm_cast
  rw [Nat.pow_mul]

/-- Signed, half-open balanced digits are recovered from their biased radix pack. -/
theorem main : AKLT.Cert.H1.Production.Leaves.signedPacking := by
  intro width n hw f hf i
  let b : Nat := 2 ^ width
  let h : Nat := 2 ^ (width - 1)
  let d : Fin n → Nat := fun j => (f j + (h : Int)).toNat
  have hb : 1 < b := by
    dsimp [b]
    cases width with
    | zero => omega
    | succ w =>
        rw [pow_succ]
        have hp : 1 ≤ 2 ^ w := Nat.one_le_pow w 2 (by omega)
        omega
  have hbh : (b : Int) = 2 * (h : Int) := by
    dsimp [b, h]
    have hw' : width = width - 1 + 1 := by omega
    have hBnat : (2 : Nat) ^ width = 2 * (2 : Nat) ^ (width - 1) := by
      calc
        (2 : Nat) ^ width = (2 : Nat) ^ (width - 1 + 1) := by rw [← hw']
        _ = (2 : Nat) ^ (width - 1) * 2 := by rw [pow_succ]
        _ = 2 * (2 : Nat) ^ (width - 1) := by ring
    exact_mod_cast hBnat
  have hdnonneg : ∀ j : Fin n, 0 ≤ f j + (h : Int) := by
    intro j
    have hh : (h : Int) = (2 : Nat) ^ (width - 1) := rfl
    rw [hh]
    have := (hf j).1
    omega
  have hdlt : ∀ j : Fin n, f j + (h : Int) < (b : Int) := by
    intro j
    have hh : (h : Int) = (2 : Nat) ^ (width - 1) := rfl
    rw [hbh]
    rw [hh]
    have := (hf j).2
    omega
  have hdcast : ∀ j : Fin n, (d j : Int) = f j + (h : Int) := by
    intro j
    dsimp [d]
    exact Int.toNat_of_nonneg (hdnonneg j)
  have hdbound : ∀ j : Fin n, d j < b := by
    intro j
    have hlt := hdlt j
    rw [← hdcast j] at hlt
    exact_mod_cast hlt
  have hhcast : (h : Int) = (2 : Nat) ^ (width - 1) := rfl
  have hbaseInt : ((2 : Nat) ^ width : Int) = (b : Int) := rfl
  have hpow : ∀ j : Fin n,
      ((2 : Nat) ^ (width * j.val) : Int) = (b : Int) ^ j.val := by
    intro j
    dsimp [b]
    exact pow_width_mul width j.val
  have hpacked :
      (∑ j : Fin n, f j * ((2 : Nat) ^ (width * j.val) : Int)) +
          AKLT.Cert.H1.signedBias width n =
        (packNat b d : Int) := by
    rw [signedBias_eq_sum width n hw]
    rw [show (packNat b d : Int) =
        ∑ j : Fin n, (d j : Int) * (b : Int) ^ j.val by
          simp [packNat, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hdc := hdcast j
    rw [hhcast] at hdc
    rw [hpow j, hbaseInt]
    rw [← add_mul, ← hdc]
  have hdigit := packNat_digit b d hdbound i
  unfold AKLT.Cert.H1.signedDigit
  rw [hpacked]
  simp only [← Int.natCast_pow]
  rw [← Int.natCast_ediv, ← Int.natCast_emod]
  have hnatpow : 2 ^ (width * i.val) = b ^ i.val := by
    dsimp [b]
    rw [Nat.pow_mul]
  rw [hnatpow]
  change ((packNat b d / (b ^ i.val) % b : Nat) : Int) - (h : Int) = f i
  rw [hdigit, hdcast i]
  ring

end AKLT.W.H1C017

#print axioms AKLT.W.H1C017.main
