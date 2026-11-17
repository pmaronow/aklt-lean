module
public import AKLT.Defs.OperatorContracts

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.Cert.H1
open AKLT.Defs
open scoped BigOperators

noncomputable def contractTerm (V : Finset Plane) (status : Plane → Status)
    (m : LocalVariable →₀ Nat) (c : ℚ) : MvPolynomial (Fin 20 × Fin 3) ℚ :=
  MvPolynomial.monomial (Finsupp.comapDomain Sum.inr m (by
    intro a _ b _ h; exact Sum.inr.inj h))
    (c * ∏ x ∈ V, rationalStatusMoment (status x) (fun k => m (.inl (x,k))))

/-- Finite moment contraction is additive; no monomial enumeration is trusted. -/
theorem contractSpins_add (V : Finset Plane) (status : Plane → Status)
    (p q : MvPolynomial LocalVariable ℚ) :
    contractSpins V status (p+q) = contractSpins V status p + contractSpins V status q := by
  classical
  unfold contractSpins
  change (p.coeff+q.coeff).sum (contractTerm V status) =
    p.coeff.sum (contractTerm V status) + q.coeff.sum (contractTerm V status)
  apply Finsupp.sum_add_index'
  · intro m
    simp [contractTerm]
  · intro m a b
    simp [contractTerm, add_mul]

/-- Monomial contraction is the literal tensor formula in Defs. -/
theorem contractSpins_monomial (V : Finset Plane) (status : Plane → Status)
    (m : LocalVariable →₀ Nat) (c : ℚ) :
    contractSpins V status (MvPolynomial.monomial m c) =
      MvPolynomial.monomial (Finsupp.comapDomain Sum.inr m (by
        intro a _ b _ h; exact Sum.inr.inj h))
        (c * ∏ x ∈ V, rationalStatusMoment (status x) (fun k => m (.inl (x,k)))) := by
  classical
  unfold contractSpins
  change (MvPolynomial.monomial m c).coeff.sum (contractTerm V status) = contractTerm V status m c
  apply MvPolynomial.sum_monomial_eq
  simp [contractTerm]

#print axioms contractSpins_add
#print axioms contractSpins_monomial
end AKLT.Cert.H1
