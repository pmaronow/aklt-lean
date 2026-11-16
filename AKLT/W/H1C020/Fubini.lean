import AKLT.Cert.H1.Contraction

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1

abbrev LocalExp := LocalVariable →₀ Nat
abbrev VectorExp := (Fin 20 × Fin 3) →₀ Nat

def vectorPart (m : LocalExp) : VectorExp :=
  Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn

def momentWeight (V : Finset Plane) (s : Plane → Status) (m : LocalExp) : ℚ :=
  ∏ x ∈ V, rationalStatusMoment (s x) (fun k => m (.inl (x,k)))

def ExponentSupported (V : Finset Plane) (m : LocalExp) : Prop :=
  ∀ x ∉ V, ∀ k : Fin 3, m (.inl (x,k)) = 0

def InternallySupported (V : Finset Plane) (p : MvPolynomial LocalVariable ℚ) : Prop :=
  ∀ m ∈ p.support, ExponentSupported V m

lemma vectorPart_add (m n : LocalExp) : vectorPart (m+n) = vectorPart m + vectorPart n :=
  Finsupp.comapDomain_add_of_injective Sum.inr_injective m n

lemma contractSpins_sum {α : Type*} (V : Finset Plane) (s : Plane → Status)
    (t : Finset α) (f : α → MvPolynomial LocalVariable ℚ) :
    contractSpins V s (∑ a ∈ t, f a) = ∑ a ∈ t, contractSpins V s (f a) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [contractSpins]
  | @insert a t ha ih =>
      simp only [Finset.sum_insert ha, contractSpins_add, ih]

lemma momentWeight_disjoint (V W : Finset Plane) (s : Plane → Status)
    (hd : Disjoint V W) (m n : LocalExp)
    (hm : ExponentSupported V m) (hn : ExponentSupported W n) :
    momentWeight (V ∪ W) s (m+n) = momentWeight V s m * momentWeight W s n := by
  classical
  unfold momentWeight
  rw [Finset.prod_union hd]
  congr 1
  · apply Finset.prod_congr rfl
    intro x hx
    congr 1
    funext k
    have hxW : x ∉ W := fun h => Finset.disjoint_left.mp hd hx h
    simp only [Finsupp.add_apply, hn x hxW k, add_zero]
  · apply Finset.prod_congr rfl
    intro x hx
    congr 1
    funext k
    have hxV : x ∉ V := fun h => Finset.disjoint_left.mp hd h hx
    simp only [Finsupp.add_apply, hm x hxV k, zero_add]

lemma contractSpins_disjoint_monomials (V W : Finset Plane) (s : Plane → Status)
    (hd : Disjoint V W) (m n : LocalExp) (c d : ℚ)
    (hm : ExponentSupported V m) (hn : ExponentSupported W n) :
    contractSpins (V ∪ W) s (MvPolynomial.monomial m c * MvPolynomial.monomial n d) =
      contractSpins V s (MvPolynomial.monomial m c) *
        contractSpins W s (MvPolynomial.monomial n d) := by
  rw [MvPolynomial.monomial_mul_monomial, contractSpins_monomial,
    contractSpins_monomial, contractSpins_monomial, MvPolynomial.monomial_mul_monomial]
  change MvPolynomial.monomial (vectorPart (m+n)) (c*d*momentWeight (V∪W) s (m+n)) =
    MvPolynomial.monomial (vectorPart m + vectorPart n)
      ((c*momentWeight V s m) * (d*momentWeight W s n))
  rw [vectorPart_add, momentWeight_disjoint V W s hd m n hm hn]
  congr 1
  ring

/-- Finite Fubini for polynomials on disjoint internal spin sets. It requires
no degree assumption and allows arbitrary overlap of external vector tokens. -/
theorem contractSpins_disjoint_mul (V W : Finset Plane) (s : Plane → Status)
    (hd : Disjoint V W) (p q : MvPolynomial LocalVariable ℚ)
    (hp : InternallySupported V p) (hq : InternallySupported W q) :
    contractSpins (V ∪ W) s (p*q) = contractSpins V s p * contractSpins W s q := by
  classical
  calc
    contractSpins (V ∪ W) s (p*q) =
        contractSpins (V ∪ W) s
          ((∑ m ∈ p.support, MvPolynomial.monomial m (p.coeff m)) *
            ∑ n ∈ q.support, MvPolynomial.monomial n (q.coeff n)) := by
          rw [← p.as_sum, ← q.as_sum]
    _ = ∑ m ∈ p.support, ∑ n ∈ q.support,
        contractSpins (V ∪ W) s
          (MvPolynomial.monomial m (p.coeff m) * MvPolynomial.monomial n (q.coeff n)) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum, contractSpins_sum]
    _ = ∑ m ∈ p.support, ∑ n ∈ q.support,
        contractSpins V s (MvPolynomial.monomial m (p.coeff m)) *
          contractSpins W s (MvPolynomial.monomial n (q.coeff n)) := by
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro n hn
          exact contractSpins_disjoint_monomials V W s hd m n _ _ (hp m hm) (hq n hn)
    _ = contractSpins V s p * contractSpins W s q := by
          rw [← Finset.sum_mul_sum, ← contractSpins_sum, ← contractSpins_sum,
            ← p.as_sum, ← q.as_sum]

end AKLT.W.H1C020
