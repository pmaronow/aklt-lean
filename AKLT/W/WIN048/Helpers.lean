import AKLT.Blueprint.Win.NodesRemoval

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN048

theorem normSq_nonneg (a : Vec3) : 0 ≤ normSq a := by
  change 0 ≤ ∑ i, a i * a i
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (a i))

theorem normSq_add (a b : Vec3) :
    normSq (a + b) = normSq a + 2 * dot a b + normSq b := by
  simp only [normSq, dot, Pi.add_apply]
  simp_rw [add_mul, mul_add]
  simp only [Finset.sum_add_distrib]
  have h : (∑ i, b i * a i) = ∑ i, a i * b i := by
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [h]
  ring

theorem eq_zero_of_normSq_eq_zero {a : Vec3} (h : normSq a = 0) : a = 0 := by
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => mul_self_nonneg (a i))).mp h
  funext i
  exact mul_self_eq_zero.mp (hz i (Finset.mem_univ i))

theorem factor_nonneg {a b : Vec3} (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have h := normSq_nonneg (a + b)
  rw [normSq_add] at h
  linarith

theorem eq_neg_of_factor_zero {a b : Vec3} (ha : normSq a ≤ 1)
    (hb : normSq b ≤ 1) (h : 1 + dot a b = 0) : b = -a := by
  have hz : normSq (a + b) = 0 := by
    have h0 := normSq_nonneg (a + b)
    rw [normSq_add] at h0 ⊢
    linarith
  have hv := eq_zero_of_normSq_eq_zero hz
  exact eq_neg_of_add_eq_zero_right hv

/-- Six letters with one fixed positive sign. They contain no antipodal pair. -/
abbrev HalfLetter := Fin 3 × Fin 2

def halfLetter (j : HalfLetter) : IcoLetter := (j.1, 0, j.2)

theorem goldenRatio_pos : 0 < goldenRatio := by
  unfold goldenRatio
  positivity

theorem icoRadius_pos : 0 < icoRadius := by
  unfold icoRadius
  exact Real.sqrt_pos.mpr (by have := goldenRatio_pos; linarith)

theorem halfLetter_injective : Function.Injective (fun j => icoVector (halfLetter j)) := by
  intro ⟨a, s⟩ ⟨b, t⟩ h
  have h0 := congrArg (fun v : Vec3 => v 0 * icoRadius) h
  have h1 := congrArg (fun v : Vec3 => v 1 * icoRadius) h
  have h2 := congrArg (fun v : Vec3 => v 2 * icoRadius) h
  have hr : icoRadius ≠ 0 := ne_of_gt icoRadius_pos
  have hg := goldenRatio_pos
  fin_cases a <;> fin_cases s <;> fin_cases b <;> fin_cases t <;>
    norm_num [halfLetter, icoVector, signValue, div_mul_cancel₀ _ hr] at h0 h1 h2 ⊢ <;>
    linarith

theorem halfLetter_not_antipodal (j k : HalfLetter) :
    icoVector (halfLetter j) ≠ -icoVector (halfLetter k) := by
  intro h
  rcases j with ⟨a, s⟩
  rcases k with ⟨b, t⟩
  have h0 := congrArg (fun v : Vec3 => v 0 * icoRadius) h
  have h1 := congrArg (fun v : Vec3 => v 1 * icoRadius) h
  have h2 := congrArg (fun v : Vec3 => v 2 * icoRadius) h
  have hr : icoRadius ≠ 0 := ne_of_gt icoRadius_pos
  fin_cases a <;> fin_cases b <;>
    norm_num [halfLetter, icoVector, signValue, neg_mul, div_mul_cancel₀ _ hr]
      at h0 h1 h2 ⊢ <;>
    simp only [inv_mul_cancel₀ hr] at h0 h1 h2 <;>
    first | contradiction | linarith

theorem neighbours_card_le (x : Plane) : (neighbours x).card ≤ 4 := by
  calc
    (neighbours x).card ≤ Fintype.card Compass := Finset.card_image_le
    _ = 4 := by decide +kernel

/-- A local original leg is determined by its exterior endpoint. -/
theorem local_legs_card_le (G : Finset Plane) (x : Plane) :
    Fintype.card {e : originalLegs G // e.val.1 = x} ≤ 4 := by
  classical
  let f : {e : originalLegs G // e.val.1 = x} → ↥(neighbours x) := fun e =>
    ⟨e.val.val.2, by
      have he := e.val.property
      simp only [originalLegs, Finset.mem_biUnion, Finset.mem_image] at he
      obtain ⟨y, _, z, hz, heq⟩ := he
      have hy : y = x := by
        have := congrArg Prod.fst heq
        exact this.trans e.property
      have hz' : z = e.val.val.2 := congrArg Prod.snd heq
      simpa only [hy, hz'] using (Finset.mem_sdiff.mp hz).1⟩
  have hf : Function.Injective f := by
    intro e d h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact e.property.trans d.property.symm
    · exact congrArg Subtype.val h
  exact (Fintype.card_le_of_injective f hf).trans (by
    simpa only [Fintype.card_coe] using neighbours_card_le x)

#print axioms normSq_nonneg
#print axioms normSq_add
#print axioms eq_zero_of_normSq_eq_zero
#print axioms factor_nonneg
#print axioms eq_neg_of_factor_zero
#print axioms goldenRatio_pos
#print axioms icoRadius_pos
#print axioms halfLetter_injective
#print axioms halfLetter_not_antipodal
#print axioms neighbours_card_le
#print axioms local_legs_card_le

end AKLT.W.WIN048
