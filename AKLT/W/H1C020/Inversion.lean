import AKLT.W.H1C020.Local

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

def tokenIndex (t : Nat) : Fin 20 := ⟨t%20,Nat.mod_lt _ (by decide)⟩

lemma invertPolynomial_mul (I : Finset (Fin 20)) (p q : VectorPolynomial) :
    invertPolynomial I (p*q) = invertPolynomial I p * invertPolynomial I q :=
  map_mul _ _ _

lemma invertPolynomial_C (I : Finset (Fin 20)) (a : ℚ) :
    invertPolynomial I (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [invertPolynomial]

lemma invertPolynomial_vectorVariable (I : Finset (Fin 20)) (t c : Nat) :
    invertPolynomial I (vectorVariable t c) =
      MvPolynomial.C (if tokenIndex t ∈ I then (-1 : ℚ) else 1) * vectorVariable t c := by
  unfold invertPolynomial vectorVariable
  rw [MvPolynomial.eval₂Hom_X']
  change (if tokenIndex t ∈ I then (-1 : VectorPolynomial) else 1) *
      vectorVariable t c = _
  by_cases h : tokenIndex t ∈ I <;> simp [h, vectorVariable]

def inversionSign (b : Bool) (cs : List Nat) : ℚ :=
  if b && (cs.filter (· != 0)).length % 2 == 1 then -1 else 1

lemma inversionSign_eq_pow (b : Bool) (cs : List Nat) :
    inversionSign b cs = if b then (-1 : ℚ) ^ (cs.filter (· != 0)).length else 1 := by
  cases b with
  | false => simp [inversionSign]
  | true =>
      rw [neg_one_pow_eq_pow_mod_two]
      have hmod := Nat.mod_lt (cs.filter (· != 0)).length (by decide : 0 < 2)
      interval_cases h : (cs.filter (· != 0)).length % 2 <;> simp [inversionSign, h]

lemma inversionSign_nil (b : Bool) : inversionSign b [] = 1 := by
  cases b <;> norm_num [inversionSign]

lemma inversionSign_cons (b : Bool) (a : Nat) (cs : List Nat) :
    inversionSign b (a::cs) =
      (if a == 0 then 1 else if b then -1 else 1) * inversionSign b cs := by
  simp only [inversionSign_eq_pow]
  by_cases ha : a = 0 <;> cases b <;>
    simp [List.filter_cons, ha, pow_succ, mul_comm]

/-- The parity sign in the constructor agrees with inversion on the original
token indices. Every nonzero colour contributes exactly one inverted token. -/
theorem invertPolynomial_vectorMonomial (I : Finset (Fin 20)) (t : Nat)
    (b : Bool) (cs : List Nat)
    (hI : ∀ q < cs.length, tokenIndex (t+q) ∈ I ↔ b = true) :
    invertPolynomial I (vectorMonomial t cs) =
      MvPolynomial.C (inversionSign b cs) * vectorMonomial t cs := by
  induction cs generalizing t with
  | nil => simp [vectorMonomial, invertPolynomial, inversionSign_nil]
  | cons a cs ih =>
      have hhead : tokenIndex t ∈ I ↔ b = true := by
        simpa only [Nat.add_zero] using hI 0 (by simp)
      have htail : ∀ q < cs.length, tokenIndex ((t+1)+q) ∈ I ↔ b = true := by
        intro q hq
        simpa only [Nat.add_assoc, Nat.add_comm 1 q] using
          hI (q+1) (by simpa using Nat.succ_lt_succ hq)
      rw [vectorMonomial, invertPolynomial_mul, ih (t+1) htail, inversionSign_cons]
      by_cases ha : a = 0
      · simp [ha, invertPolynomial]
      · simp only [beq_iff_eq, ha, ↓reduceIte, invertPolynomial_vectorVariable,
          MvPolynomial.C_mul]
        cases b <;> simp_all only [Bool.false_eq_true, iff_false, iff_true,
          ↓reduceIte, MvPolynomial.C_1, one_mul] <;> ring

lemma invertPolynomial_add (I : Finset (Fin 20)) (p q : VectorPolynomial) :
    invertPolynomial I (p+q) = invertPolynomial I p + invertPolynomial I q := map_add _ _ _

lemma invertPolynomial_listSum (I : Finset (Fin 20)) (ps : List VectorPolynomial) :
    invertPolynomial I ps.sum = (ps.map (invertPolynomial I)).sum := by
  induction ps with
  | nil => simp [invertPolynomial]
  | cons p ps ih => simp only [List.sum_cons, List.map_cons, invertPolynomial_add, ih]

def eraseInversion (s : SiteSpec) : SiteSpec := {s with inverted := false}

set_option maxHeartbeats 1000000 in
/-- Local constructor signs implement inversion of entire groups, including
the reduced-corner branch. The token premise uses original slot numbers. -/
theorem rationalLocal_inversion (I : Finset (Fin 20)) (site : Nat) (s : SiteSpec)
    (l r v : Nat)
    (hhead : tokenIndex (ringLeader site) ∈ I ↔ s.inverted = true)
    (hslots : ∀ q < s.nslots, tokenIndex (ringLeader site+q) ∈ I ↔ s.inverted = true) :
    invertPolynomial I (rationalLocal site (eraseInversion s) l r v) =
      rationalLocal site s l r v := by
  unfold rationalLocal eraseInversion
  dsimp only
  split
  · simp [invertPolynomial]
  · split
    · generalize hlabel : (if s.left then l else r) = label
      by_cases hz : label = 0
      · simp [hz, invertPolynomial, MvPolynomial.eval₂Hom_C]
      · simp only [beq_iff_eq, hz, Bool.false_eq_true, ↓reduceIte,
          invertPolynomial_mul, invertPolynomial_C, invertPolynomial_vectorVariable]
        cases hb : s.inverted <;>
          simp_all only [Bool.false_eq_true, iff_false, iff_true, ↓reduceIte,
            MvPolynomial.C_1, one_mul]
        all_goals rw [← mul_assoc, ← MvPolynomial.C_mul]; congr 1 <;> ring
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, mul_one]
      rw [invertPolynomial_listSum, List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro cs hcs
      have hlen := colorChoices_length s.nslots cs hcs
      simp only [Function.comp_apply, siteColors]
      rw [invertPolynomial_mul, invertPolynomial_C,
        invertPolynomial_vectorMonomial I (ringLeader site) s.inverted cs (by
          intro q hq
          exact hslots q (hlen ▸ hq))]
      simp only [inversionSign, MvPolynomial.C_mul]
      ring

end AKLT.W.H1C020
