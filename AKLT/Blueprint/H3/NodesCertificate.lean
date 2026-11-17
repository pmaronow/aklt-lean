module
public import AKLT.Blueprint.H3.Positivity

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
set_option maxRecDepth 8192

namespace AKLT.Blueprint.H3

/-- `l:stationary-local-global`, lines 800–813: per-labeled-edge comparison with the
position-free row. Revisit edges do not inspect arrival. For first visits translate the local
neighbor sets and compare beta-prime≤beta; known-site rows only reduce diagonals and kill edges. -/
def StationaryFreeEdgeStatement : Prop :=
  ∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ X : PairType, ∀ d₀ : Compass, d₀ ≠ .east →
    ∀ φ : Phase, ∀ a : Fin 3741, ∀ x : Plane, ∀ d : Compass, ∀ ψ : Phase,
      stationaryCoefficient Q X d₀ φ a x d ψ ≤ freeCoefficient Q φ a d ψ

/-- `d:stationary-certificate`, lines 748–756: the natural ceiling is an upper bound.
Both scales are positive fixed powers of two; the proof does not use floating point arithmetic. -/
def CoefficientCeilingStatement : Prop :=
  ∀ t : ℚ, 0 ≤ t → t ≤ (coefficientCeiling t : ℚ) / certificateCoefficientScale

/-- Immediate arithmetic leaf; a natural ceiling also bounds negative inputs. -/
theorem coefficientCeiling_proved : CoefficientCeilingStatement := by
  intro t _
  have hD : (0 : ℚ) < certificateCoefficientScale := by norm_num [certificateCoefficientScale]
  apply (le_div_iff₀ hD).mpr
  simpa [coefficientCeiling, mul_comm] using
    (Nat.le_ceil ((certificateCoefficientScale : ℚ) * t))

/-- Rational specialization of the already-proved generic integer-row soundness theorem. -/
theorem rational_scaled_row {E : Type} (s : Finset E) (t : E → ℚ) (p v : E → ℕ)
    (D V u : ℕ) (hD : 0 < D) (hV : 0 < V)
    (hceil : ∀ e ∈ s, t e ≤ (p e : ℚ) / D)
    (hcheck : ∑ e ∈ s, p e * v e ≤ D * u) :
    (∑ e ∈ s, t e * ((v e : ℚ) / V)) ≤ (u : ℚ) / V := by
  have hc := AKLT.Gen.Bellman.scaled_row_sound s (fun e => (t e : ℝ)) p v D V u hD hV
    (fun e he => by
      have hh : (t e : ℝ) ≤ (((p e : ℚ) / D : ℚ) : ℝ) := Rat.cast_le.mpr (hceil e he)
      simpa only [Rat.cast_div, Rat.cast_natCast] using hh) hcheck
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast] using hc

/-- `d:stationary-certificate`, lines 692–714: nonnegativity, caps, and outside equality.
No positivity of the inside values is assumed: zero terminal values are allowed. -/
theorem potential_bounds {q m : ℕ} (C : StationaryData q) (Q : MemoryQuotient m q)
    (X : PairType) (d₀ : Compass) (hC : C.Passes Q X d₀) (φ : Phase) (a : Fin q) (x : Plane) :
    0 ≤ C.potential φ a x ∧ C.potential φ a x ≤ (C.cap φ a : ℚ) / certificateValueScale ∧
    (x ∉ square (0, 0) certificateRadius → C.potential φ a x = (C.cap φ a : ℚ) / certificateValueScale) := by
  classical
  have hcap : C.extended φ a x ≤ C.cap φ a := by
    unfold StationaryData.extended
    split_ifs with hx
    · exact hC.2.2.2.1 φ a ⟨x, hx⟩
    · exact le_rfl
  refine ⟨by unfold StationaryData.potential; positivity, ?_, ?_⟩
  · unfold StationaryData.potential
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcap) (by positivity)
  · intro hx
    have he : C.extended φ a x = C.cap φ a := dite_eq_right hx
    exact congrArg (fun z : ℕ => (z : ℚ) / certificateValueScale) he

/-- `l:stationary-local-global`, lines 787–795: checked free integer rows. -/
theorem checked_free_row (Q : MemoryQuotient 10 3741) (X : PairType) (d₀ : Compass)
    (C : StationaryData 3741) (hC : C.Passes Q X d₀) (φ : Phase) (a : Fin 3741) :
    freeApply Q (fun ψ b => (C.cap ψ b : ℚ) / certificateValueScale) φ a ≤
      (C.cap φ a : ℚ) / certificateValueScale := by
  have hh := rational_scaled_row (Finset.univ : Finset (Compass × Phase))
    (fun e => freeCoefficient Q φ a e.1 e.2)
    (fun e => coefficientCeiling (freeCoefficient Q φ a e.1 e.2))
    (fun e => C.cap e.2 (Q.successor a e.1)) certificateCoefficientScale certificateValueScale
    (C.cap φ a) (by norm_num [certificateCoefficientScale]) (by norm_num [certificateValueScale])
    (fun e _ => coefficientCeiling_proved _ (freeCoefficient_nonneg _ _ _ _ _))
    (by simpa only [Fintype.sum_prod_type] using hC.2.2.1 φ a)
  simpa only [freeApply, Fintype.sum_prod_type] using hh

/-- `l:stationary-local-global`, lines 796–799: checked inside nonterminal rows.
Successors outside the square use the extended cap, exactly as the integer row does. -/
theorem checked_inside_row (Q : MemoryQuotient 10 3741) (X : PairType) (d₀ : Compass)
    (C : StationaryData 3741) (hC : C.Passes Q X d₀) (φ : Phase) (a : Fin 3741)
    (x : square (0, 0) certificateRadius) (hc : x.val ≠ kernelCentre) (hv : x.val ≠ kernelTarget X) :
    stationaryApply Q X d₀ C.potential φ a x.val ≤ C.potential φ a x.val := by
  have hh := rational_scaled_row (Finset.univ : Finset (Compass × Phase))
    (fun e => stationaryCoefficient Q X d₀ φ a x.val e.1 e.2)
    (fun e => coefficientCeiling (stationaryCoefficient Q X d₀ φ a x.val e.1 e.2))
    (fun e => C.extended e.2 (Q.successor a e.1) (x.val + e.1.step))
    certificateCoefficientScale certificateValueScale (C.value φ a x)
    (by norm_num [certificateCoefficientScale]) (by norm_num [certificateValueScale])
    (fun e _ => coefficientCeiling_proved _ (stationaryCoefficient_nonneg _ _ _ _ _ _ _ _))
    (by simpa only [Fintype.sum_prod_type] using hC.2.2.2.2.2 φ a x hc hv)
  have hx : C.potential φ a x.val = (C.value φ a x : ℚ) / certificateValueScale := by
    have he : C.extended φ a x.val = C.value φ a x := dite_eq_left x.property
    exact congrArg (fun z : ℕ => (z : ℚ) / certificateValueScale) he
  calc
    stationaryApply Q X d₀ C.potential φ a x.val ≤ (C.value φ a x : ℚ) / certificateValueScale := by
      simpa only [stationaryApply, Fintype.sum_prod_type, StationaryData.potential] using hh
    _ = _ := hx.symm

end AKLT.Blueprint.H3
