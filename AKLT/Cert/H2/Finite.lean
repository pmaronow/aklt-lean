import AKLT.Cert.H2.Check
import AKLT.Cert.H2.Words

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Cert.H2

set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem digit_lt (d : Compass) : directionDigit d < 4 := by cases d <;> decide

@[simp] theorem direction_digit (d : Compass) : digitDirection (directionDigit d) = d := by
  cases d <;> rfl

theorem code_lt (w : DirectionWord 6) : wordCode w < 4096 := by
  have h₀ := digit_lt (w 0)
  have h₁ := digit_lt (w 1)
  have h₂ := digit_lt (w 2)
  have h₃ := digit_lt (w 3)
  have h₄ := digit_lt (w 4)
  have h₅ := digit_lt (w 5)
  norm_num [wordCode, Fin.sum_univ_succ] at *
  omega

theorem decode_code (w : DirectionWord 6) : decodeSix (wordCode w) = w := by
  have h₀ := digit_lt (w 0)
  have h₁ := digit_lt (w 1)
  have h₂ := digit_lt (w 2)
  have h₃ := digit_lt (w 3)
  have h₄ := digit_lt (w 4)
  have h₅ := digit_lt (w 5)
  funext i
  have he : wordCode w / 4 ^ i.val % 4 = directionDigit (w i) := by
    fin_cases i <;> norm_num [wordCode, Fin.sum_univ_succ] <;> omega
  change digitDirection (wordCode w / 4 ^ i.val) = w i
  unfold digitDirection
  rw [he]
  cases w i <;> rfl

theorem digit_direction (c : ℕ) : directionDigit (digitDirection c) = c % 4 := by
  have h : c % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have he : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega
  rcases he with he | he | he | he <;> simp [digitDirection, he, directionDigit]

theorem code_decode (c : ℕ) (hc : c < 4096) : wordCode (decodeSix c) = c := by
  norm_num [wordCode, decodeSix, Fin.sum_univ_succ, digit_direction]
  omega

def rawCodeEquiv : MemoryWindow 6 ≃ ↥rawCodes where
  toFun ω := ⟨⟨wordCode ω.val, code_lt ω.val⟩, by
    simp only [rawCodes, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [decode_code]
    exact ω.property⟩
  invFun c := ⟨decodeSix c.val.val, (Finset.mem_filter.mp c.property).2⟩
  left_inv ω := Subtype.ext (decode_code ω.val)
  right_inv c := Subtype.ext (Fin.ext (code_decode c.val.val c.val.isLt))

theorem raw_count : Fintype.card (MemoryWindow 6) = 916 := by
  calc
    Fintype.card (MemoryWindow 6) = Fintype.card ↥rawCodes := Fintype.card_congr rawCodeEquiv
    _ = rawCodes.card := Fintype.card_coe rawCodes
    _ = 916 := raw_codes_count

/-- Soundness of the exhaustive Boolean check, on the mathematical raw state predicate. -/
theorem checked_rows (w : DirectionWord 6) (hw : RawWindow w) :
    186377076276 ≤ witnessNat w ∧ witnessNat w ≤ 1000000000000 ∧
      1120437614225 * rowNumerator w ≤ 1119948287353 * 2695605 * witnessNat w ∧
      ∀ g : SquareSymmetry, witnessNat (symmetryWord g w) = witnessNat w := by
  have hc := List.all_eq_true.mp complete_checked (wordCode w)
    (List.mem_range.mpr (code_lt w))
  simpa only [sixRowCheck, decode_code, ite_eq_left hw, decide_eq_true_eq] using hc

def integerWitness (ω : MemoryWindow 6) : ℤ := witnessNat ω.val

theorem kind_numerator (k : StepKind) :
    (kindNumerator k : ℚ) = 2695605 * kindWeight k := by
  cases k <;> norm_num [kindNumerator, kindWeight, passageFactor, localThreshold]

theorem matrix_row {m : ℕ} (ω : MemoryWindow m) (f : MemoryWindow m → ℚ) :
    (∑ ω', memoryMatrix m ω ω' * f ω') =
      ∑ d : Compass, if h : WindowAdmissible ω.val d then
        kindWeight (windowKind ω.val d) * f ⟨windowSuccessor ω.val d,
          successor_raw _ _ ω.property h⟩ else 0 := by
  classical
  unfold memoryMatrix
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : WindowAdmissible ω.val d
  · rw [dite_eq_left hd]
    let s : MemoryWindow m := ⟨windowSuccessor ω.val d, successor_raw _ _ ω.property hd⟩
    have he (ω' : MemoryWindow m) :
        (WindowAdmissible ω.val d ∧ windowSuccessor ω.val d = ω'.val) ↔ ω' = s := by
      simp only [hd, true_and]
      exact ⟨fun h => (Subtype.ext h).symm, fun h => by subst ω'; rfl⟩
    simp_rw [he]
    simp [s]
  · simp [hd]

theorem witness_row (ω : MemoryWindow 6) :
    (∑ ω', memoryMatrix 6 ω ω' * (integerWitness ω' : ℚ)) =
      (rowNumerator ω.val : ℚ) / 2695605 := by
  classical
  rw [matrix_row]
  unfold rowNumerator
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : WindowAdmissible ω.val d
  · simp only [hd, dite_eq_left, ite_true, kind_numerator, integerWitness, Int.cast_natCast]
    ring
  · simp [hd]

theorem witness_positive (ω : MemoryWindow 6) : 0 < integerWitness ω := by
  have hh := (checked_rows ω.val ω.property).1
  unfold integerWitness
  exact_mod_cast (show 0 < witnessNat ω.val by omega)

theorem witness_ratio_bound (ω : MemoryWindow 6) :
    (∑ ω', memoryMatrix 6 ω ω' * (integerWitness ω' : ℚ)) /
      (integerWitness ω : ℚ) ≤ certifiedRate := by
  rw [witness_row]
  have hh := (checked_rows ω.val ω.property).2.2.1
  have hp : (0 : ℚ) < integerWitness ω := by exact_mod_cast witness_positive ω
  apply (div_le_iff₀ hp).2
  unfold certifiedRate integerWitness
  simp only [Int.cast_natCast]
  have hh' : (1120437614225 : ℚ) * rowNumerator ω.val ≤
      1119948287353 * 2695605 * witnessNat ω.val := by exact_mod_cast hh
  nlinarith

theorem witness_orbit (ω ω' : MemoryWindow 6)
    (h : SameWindowOrbit ω.val ω'.val) : integerWitness ω = integerWitness ω' := by
  obtain ⟨g, hg⟩ := h
  have hh := (checked_rows ω.val ω.property).2.2.2 g
  rw [hg] at hh
  unfold integerWitness
  exact_mod_cast hh.symm

def matrixNumerator {m : ℕ} (ω ω' : MemoryWindow m) : ℕ :=
  ∑ d : Compass, if WindowAdmissible ω.val d ∧ windowSuccessor ω.val d = ω'.val then
    kindNumerator (windowKind ω.val d) else 0

theorem matrix_numerator {m : ℕ} (ω ω' : MemoryWindow m) :
    (matrixNumerator ω ω' : ℚ) = 2695605 * memoryMatrix m ω ω' := by
  classical
  unfold matrixNumerator memoryMatrix
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp [kind_numerator]

theorem floor_matrix {m : ℕ} (ω ω' : MemoryWindow m) :
    ⌊(2695605 : ℚ) * memoryMatrix m ω ω'⌋ = (matrixNumerator ω ω' : ℤ) := by
  rw [← matrix_numerator]
  simp

theorem integer_row (ω : MemoryWindow 6) :
    (∑ ω', ⌊(2695605 : ℚ) * memoryMatrix 6 ω ω'⌋ * integerWitness ω') =
      (rowNumerator ω.val : ℤ) := by
  classical
  apply Int.cast_injective (α := ℚ)
  simp only [Int.cast_sum, Int.cast_mul, floor_matrix, Int.cast_natCast]
  simp_rw [matrix_numerator]
  rw [show (∑ ω', (2695605 : ℚ) * memoryMatrix 6 ω ω' * (integerWitness ω' : ℚ)) =
      2695605 * ∑ ω', memoryMatrix 6 ω ω' * (integerWitness ω' : ℚ) by
    simp_rw [Finset.mul_sum, mul_assoc]]
  rw [witness_row]
  ring

def lowWindow : MemoryWindow 6 := ⟨decodeSix 441, by decide +kernel⟩
def highWindow : MemoryWindow 6 := ⟨decodeSix 0, by decide +kernel⟩
def tightWindow : MemoryWindow 6 := ⟨decodeSix 428, by decide +kernel⟩

theorem witness_low : integerWitness lowWindow = 186377076276 := by decide +kernel
theorem witness_high : integerWitness highWindow = 1000000000000 := by decide +kernel
theorem witness_tight : integerWitness tightWindow = 224087522845 := by decide +kernel
theorem row_tight : rowNumerator tightWindow.val = 603787640626036713 := by decide +kernel

/-- The exact Top finite-test contract, using the full raw check. -/
theorem h2Test : AKLT.Blueprint.Top.H2TestStatement := by
  refine ⟨by norm_num [kindWeight, passageFactor, localThreshold],
    by norm_num [kindWeight, passageFactor, localThreshold],
    by norm_num [kindWeight, passageFactor, localThreshold], integerWitness,
    186377076276, 1000000000000, by norm_num, ?_,
    ⟨lowWindow, witness_low⟩, ⟨highWindow, witness_high⟩, by norm_num, by norm_num,
    witness_orbit, witness_ratio_bound, ?_, ?_, by norm_num [certifiedRate]⟩
  · intro ω
    have hh := checked_rows ω.val ω.property
    constructor <;> unfold integerWitness
    · exact_mod_cast hh.1
    · exact_mod_cast hh.2.1
  · refine ⟨tightWindow, ?_⟩
    rw [witness_row, witness_tight, row_tight]
    norm_num [certifiedRate]
  · intro ω
    rw [integer_row]
    have hh := (checked_rows ω.val ω.property).2.2.1
    unfold integerWitness
    exact_mod_cast hh

end AKLT.Cert.H2
