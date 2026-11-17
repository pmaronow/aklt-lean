module
public import AKLT.W.H1C020.Local
public import AKLT.W.H1C020.Transfer

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

def networkDenominator (ss : List PackedSite) : Nat :=
  (ss.map (fun s => s.spec.totalDen)).prod

def LocalValidity (s : SiteSpec) : Prop :=
  siteDegree s ≤ 4 ∧ (s.leaf = true → s.tip = false)

lemma openTransfer_clear (site : Nat) (ss : List PackedSite) (codes : List Nat)
    (hv : ∀ s ∈ ss, LocalValidity s.spec) (a b : Nat) :
    openTransfer localPolynomial site ss codes a b =
      MvPolynomial.C (networkDenominator ss : ℚ) *
        openTransfer rationalLocal site ss codes a b := by
  induction ss generalizing site codes a with
  | nil => simp [openTransfer, networkDenominator]
  | cons s ss ih =>
      have hs := hv s (by simp)
      have ht : ∀ t ∈ ss, LocalValidity t.spec := fun t ht => hv t (by simp [ht])
      simp only [openTransfer]
      rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro k hk
      rw [localPolynomial_clear _ _ _ _ _ hs.1 hs.2, ih _ _ ht]
      simp only [networkDenominator, List.map_cons, List.prod_cons, Nat.cast_mul,
        MvPolynomial.C_mul]
      ring

lemma polynomialRingValue_clear (ss : List PackedSite) (codes : List Nat)
    (hv : ∀ s ∈ ss, LocalValidity s.spec) :
    polynomialRingValue ss codes = MvPolynomial.C (networkDenominator ss : ℚ) *
      closedTransfer rationalLocal ss codes := by
  rw [polynomialRingValue_paths]
  unfold closedTransfer
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  exact openTransfer_clear 0 ss codes hv a a

/-- The selected pair insertions after the passage spin is integrated. -/
def centerInsertions (value : List Nat → VectorPolynomial) (n out : Nat)
    (next : Bool) (pairs : List (Nat × Nat)) : VectorPolynomial :=
  (pairs.filterMap fun (x,y) =>
    if next && (x == out || y == out) then none else
      some (((List.range 3).map fun k => value (centerCodes n x y (k+1))).sum)).sum

lemma centerInsertions_scale (value : List Nat → VectorPolynomial) (n out : Nat)
    (next : Bool) (pairs : List (Nat × Nat)) (d : VectorPolynomial) :
    centerInsertions (fun codes => d * value codes) n out next pairs =
      d * centerInsertions value n out next pairs := by
  induction pairs with
  | nil => simp [centerInsertions]
  | cons p pairs ih =>
      rcases p with ⟨x,y⟩
      by_cases h : (next && (x == out || y == out)) = true
      · simpa only [centerInsertions, List.filterMap_cons, h, Bool.false_eq_true, ↓reduceIte,
          List.sum_cons] using ih
      · simp only [centerInsertions, List.filterMap_cons, h, Bool.false_eq_true, ↓reduceIte,
          List.sum_cons, List.sum_map_mul_left, mul_add]
        simpa only [centerInsertions, List.sum_map_mul_left] using
          congrArg (fun z => d *
          ((List.range 3).map (fun k => value (centerCodes n x y (k+1)))).sum + z) ih

def centerScale (next : Bool) : ℚ := if next then 5 else 3

/-- The normalized ring expression, with its passage denominator explicit. -/
def rationalNetwork (ss : List PackedSite) (out : Nat) (next : Bool) : VectorPolynomial :=
  closedTransfer rationalLocal ss [] + MvPolynomial.C (1 / centerScale next) *
    centerInsertions (closedTransfer rationalLocal ss) ss.length out next (centerPairs ss)

lemma centerScale_ne_zero (next : Bool) : centerScale next ≠ 0 := by
  cases next <;> norm_num [centerScale]

/-- All denominator clearing in the packed numerator is accounted for here. -/
lemma networkNumerator_clear (ss : List PackedSite) (out : Nat) (next : Bool)
    (hv : ∀ s ∈ ss, LocalValidity s.spec) :
    networkNumerator ss out next =
      MvPolynomial.C (centerScale next * (networkDenominator ss : ℚ)) *
        rationalNetwork ss out next := by
  change MvPolynomial.C (centerScale next) * polynomialRingValue ss [] +
    centerInsertions (polynomialRingValue ss) ss.length out next (centerPairs ss) = _
  have hvalue : polynomialRingValue ss = fun codes =>
      MvPolynomial.C (networkDenominator ss : ℚ) * closedTransfer rationalLocal ss codes := by
    funext codes
    exact polynomialRingValue_clear ss codes hv
  rw [hvalue, centerInsertions_scale]
  unfold rationalNetwork
  rw [MvPolynomial.C_mul, mul_add]
  have hc : MvPolynomial.C (centerScale next) *
      MvPolynomial.C (1 / centerScale next) = (1 : VectorPolynomial) := by
    rw [← MvPolynomial.C_mul, mul_one_div_cancel (centerScale_ne_zero next), MvPolynomial.C_1]
  calc
    _ = (MvPolynomial.C (centerScale next) * MvPolynomial.C (networkDenominator ss : ℚ)) *
          closedTransfer rationalLocal ss [] +
        (MvPolynomial.C (centerScale next) * MvPolynomial.C (1 / centerScale next)) *
          (MvPolynomial.C (networkDenominator ss : ℚ) *
            centerInsertions (closedTransfer rationalLocal ss) ss.length out next (centerPairs ss)) := by
          rw [hc]
          ring
    _ = _ := by ring

end AKLT.W.H1C020
