import AKLT.W.H3C032.Arithmetic

namespace AKLT.W.H3C032

open AKLT.Cert.H3.Production AKLT.Defs

/-- Arithmetic core of the short-comparator leaf, with the prefix-state
representation already reduced to scalar facts about the two items. -/
def ResidualScaledComparator : Prop :=
  ∀ (E : Exact), CertData.H3.Bridge.ExactValid E →
    ∀ (n : Nat) (w : DirectionWord n) (a b : RewardItem) (i j : Fin n),
      i.val = a.time → j.val = b.time →
      a.straight = wordStraight kernelIncoming w i →
      b.straight = wordStraight kernelIncoming w j →
      (a.reward : ℚ) / E.denominator = witnessKappa w i →
      (b.reward : ℚ) / E.denominator = witnessKappa w j →
      itemLE E a b = shortOrderLE w i j

/-- The scalar comparator, including zero-reward infinity and chronological ties. -/
theorem scaledComparator : ResidualScaledComparator := by
  intro E hE n w a b i j hitA hitB hstraightA hstraightB hrewardA hrewardB
  have hKq : (E.denominator : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hE.1)
  unfold itemLE shortOrderLE
  dsimp only
  rw [← hrewardA, ← hrewardB, ← hstraightA, ← hstraightB]
  simp only [div_eq_zero_iff, hKq, or_false, Nat.cast_eq_zero]
  by_cases ha : a.reward = 0
  · simp [ha, hitA, hitB]
  by_cases hb : b.reward = 0
  · simp [ha, hb]
  simp only [ha, hb, ↓reduceIte]
  rw [← exposureFactor_normalized E hE a, ← exposureFactor_normalized E hE b]
  have hcmp := scaledScore_comparison E.denominator (exposureFactor E a)
    (exposureFactor E b) a.reward b.reward hE.1
    (denominator_le_exposureFactor E hE a) (denominator_le_exposureFactor E hE b)
    (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
  change decide (_ ∨ (_ ∧ a.time ≤ b.time)) =
    decide (scaledScore E.denominator (exposureFactor E a) a.reward <
      scaledScore E.denominator (exposureFactor E b) b.reward ∨
      (scaledScore E.denominator (exposureFactor E a) a.reward =
        scaledScore E.denominator (exposureFactor E b) b.reward ∧ i.val ≤ j.val))
  simp only [hcmp.1, hcmp.2, hitA, hitB]

/-- Extract the scalar facts supplied by the prefix-state representation. -/
theorem main_of_residual (hcore : ResidualScaledComparator) :
    CertData.H3.Bridge.ShortComparatorLeaf := by
  intro E hE n w s hs a b ha hb i j hitA hitB
  rcases hs with ⟨_, _, _, _, hitem⟩
  obtain ⟨i', htimeA, hstraightA, hrewardA⟩ := hitem a ha
  obtain ⟨j', htimeB, hstraightB, hrewardB⟩ := hitem b hb
  have hii : i' = i := Fin.ext (by omega)
  have hjj : j' = j := Fin.ext (by omega)
  subst i'
  subst j'
  exact hcore E hE n w a b i j hitA hitB hstraightA hstraightB hrewardA hrewardB

/-- The executable short comparator agrees with the prescribed short-trail order. -/
theorem main : CertData.H3.Bridge.ShortComparatorLeaf :=
  main_of_residual scaledComparator

#print axioms scaledScore_comparison
#print axioms exposureFactor_normalized
#print axioms denominator_le_exposureFactor
#print axioms scaledComparator
#print axioms main_of_residual
#print axioms main

end AKLT.W.H3C032
