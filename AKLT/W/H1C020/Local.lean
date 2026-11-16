import AKLT.Cert.H1.Production.Leaves

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

def colorExponent (a b c : Nat) (k : Fin 3) : Nat :=
  if k = 0 then a else if k = 1 then b else c

lemma colorExponent_sum (a b c : Nat) :
    (∑ k : Fin 3, colorExponent a b c k) = a+b+c := by
  simp [Fin.sum_univ_three, colorExponent]

set_option maxHeartbeats 2000000 in
/-- The executable integer numerator is the exact degree-four rational moment. -/
lemma momentNumerator_correct (d a b c : Nat) (diluted : Bool)
    (hd : a+b+c ≤ d) (hfour : a+b+c ≤ 4) :
    (momentNumerator (siteLCD d diluted) diluted a b c : ℚ) =
      (siteLCD d diluted : ℚ) *
        rationalStatusMoment (if diluted then .D else .U) (colorExponent a b c) := by
  have ha : a ≤ 4 := by omega
  have hb : b ≤ 4 := by omega
  have hc : c ≤ 4 := by omega
  by_cases htwo : d < 2
  · have hsmall : a+b+c < 2 := by omega
    cases diluted <;>
      interval_cases a <;> interval_cases b <;> interval_cases c <;>
      first | omega | norm_num [siteLCD, htwo, momentNumerator, rationalStatusMoment,
        rationalMoment, colorExponent, Fin.sum_univ_three, Fin.exists_fin_succ]
  · by_cases hfourD : d < 4
    · have hsmall : a+b+c < 4 := by omega
      cases diluted <;>
        interval_cases a <;> interval_cases b <;> interval_cases c <;>
        first | omega | norm_num [siteLCD, htwo, hfourD, momentNumerator, rationalStatusMoment,
          rationalMoment, colorExponent, Fin.sum_univ_three, Fin.exists_fin_succ]
    · cases diluted <;>
        interval_cases a <;> interval_cases b <;> interval_cases c <;>
        first | omega | norm_num [siteLCD, htwo, hfourD, momentNumerator, rationalStatusMoment,
          rationalMoment, colorExponent, Fin.sum_univ_three, Fin.exists_fin_succ]

lemma countColor_sum_le (cs : List Nat) :
    countColor 1 cs + countColor 2 cs + countColor 3 cs ≤ cs.length := by
  induction cs with
  | nil => simp [countColor]
  | cons a cs ih =>
      by_cases h1 : a = 1
      · subst a
        simp only [countColor, beq_self_eq_true, ↓reduceIte, Nat.reduceBEq,
          Bool.false_eq_true, zero_add, List.length_cons]
        omega
      · by_cases h2 : a = 2
        · subst a
          simp only [countColor, beq_self_eq_true, ↓reduceIte, Nat.reduceBEq,
            Bool.false_eq_true, zero_add, List.length_cons]
          omega
        · by_cases h3 : a = 3
          · subst a
            simp only [countColor, beq_self_eq_true, ↓reduceIte, Nat.reduceBEq,
              Bool.false_eq_true, zero_add, List.length_cons]
            omega
          · simp only [countColor, beq_iff_eq, h1, h2, h3, ↓reduceIte,
              Bool.false_eq_true, zero_add, List.length_cons]
            omega

lemma colorChoices_length (n : Nat) (cs : List Nat) (hcs : cs ∈ colorChoices n) :
    cs.length = n := by
  induction n generalizing cs with
  | zero => simpa [colorChoices] using hcs
  | succ n ih =>
      obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp hcs
      obtain ⟨tail, htail, rfl⟩ := List.mem_map.mp ha
      simpa using congrArg Nat.succ (ih tail htail)

def siteDegree (s : SiteSpec) : Nat :=
  s.left.toNat + s.right.toNat + s.center.toNat + s.nslots

def siteColors (s : SiteSpec) (l r v : Nat) (cs : List Nat) : List Nat :=
  (if s.left then [l] else []) ++ (if s.right then [r] else []) ++
    (if s.center then [v] else []) ++ cs

lemma siteColors_length (s : SiteSpec) (l r v : Nat) (cs : List Nat)
    (hcs : cs.length = s.nslots) :
    (siteColors s l r v cs).length = siteDegree s := by
  simp only [siteColors, List.length_append]
  rw [hcs]
  unfold siteDegree
  cases s.left <;> cases s.right <;> cases s.center <;> simp

/-- The local tensor without cleared denominators. Leaf radii and tip radius
are kept as rational factors, and there are no integer moment numerators. -/
def rationalLocal (site : Nat) (s : SiteSpec) (l r v : Nat) : VectorPolynomial :=
  if (!s.left && l != 0) || (!s.right && r != 0) || (!s.center && v != 0) then 0
  else if s.leaf then
    let label := if s.left then l else r
    let sc : ℚ := if label == 0 then 1
      else (if s.inverted then -1 else 1) / (if s.diluted then 3 else 2)
    MvPolynomial.C sc * (if label == 0 then 1 else vectorVariable (ringLeader site) label)
  else
    ((colorChoices s.nslots).map fun cs =>
      let colors := siteColors s l r v cs
      let mom := rationalStatusMoment (if s.diluted then .D else .U)
        (colorExponent (countColor 1 colors) (countColor 2 colors) (countColor 3 colors))
      let tip : ℚ := if s.tip then if cs.headD 0 == 0 then 1 else 3/5 else 1
      let sign : ℚ := if s.inverted && (cs.filter (· != 0)).length % 2 == 1 then -1 else 1
      MvPolynomial.C (mom*tip*sign) * vectorMonomial (ringLeader site) cs).sum

lemma site_den_pos (s : SiteSpec) : 0 < s.den := by
  unfold SiteSpec.den siteLCD
  split_ifs <;> decide

lemma site_totalDen_pos (s : SiteSpec) : 0 < s.totalDen := by
  exact Nat.mul_pos (site_den_pos s) (by cases s.tip <;> decide)

lemma localPolynomial_clear (site : Nat) (s : SiteSpec) (l r v : Nat)
    (hd : siteDegree s ≤ 4) (hleaf : s.leaf = true → s.tip = false) :
    localPolynomial site s l r v = MvPolynomial.C (s.totalDen : ℚ) *
      rationalLocal site s l r v := by
  unfold localPolynomial rationalLocal
  split
  · simp
  · rename_i habsent
    split
    · rename_i hl
      have ht := hleaf hl
      simp only [SiteSpec.totalDen, ht, Bool.false_eq_true, ↓reduceIte, mul_one]
      have hden : (s.den : ℚ) = if s.diluted then 3 else 2 := by
        simp only [SiteSpec.den, hl, ↓reduceIte]
        cases s.diluted <;> norm_num
      rw [← mul_assoc, ← MvPolynomial.C_mul]
      apply congrArg (fun z : ℚ => MvPolynomial.C z *
        (if (if s.left then l else r) == 0 then 1 else
          vectorVariable (ringLeader site) (if s.left then l else r)))
      split_ifs <;> simp_all only [Int.cast_natCast, Int.cast_neg, Int.cast_one,
        mul_one] <;> cases s.diluted <;> norm_num at *
    · rename_i hl
      rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro cs hcs
      have hlen := colorChoices_length s.nslots cs hcs
      have hcolors := siteColors_length s l r v cs hlen
      have hcount := countColor_sum_le (siteColors s l r v cs)
      rw [hcolors] at hcount
      have hm := momentNumerator_correct (siteDegree s)
        (countColor 1 (siteColors s l r v cs))
        (countColor 2 (siteColors s l r v cs))
        (countColor 3 (siteColors s l r v cs)) s.diluted hcount (hcount.trans hd)
      have hden : s.den = siteLCD (siteDegree s) s.diluted := by
        simp [SiteSpec.den, hl, siteDegree]
      simp only [siteColors] at hm
      simp only [Int.cast_mul, Int.cast_ite, Int.cast_neg,
        Int.cast_one, Int.cast_ofNat, Int.cast_natCast]
      rw [hden, hm]
      rw [← mul_assoc, ← MvPolynomial.C_mul]
      apply congrArg (fun z : ℚ => MvPolynomial.C z * vectorMonomial (ringLeader site) cs)
      simp only [siteColors, SiteSpec.totalDen, Nat.cast_mul, Nat.cast_ite,
        Nat.cast_ofNat, hden]
      by_cases ht : s.tip = true <;>
        by_cases hz : (cs.headD 0 == 0) = true <;>
        simp only [ht, hz, Bool.false_eq_true, ↓reduceIte] <;> ring

end AKLT.W.H1C020
