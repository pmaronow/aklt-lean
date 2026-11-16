import AKLT.Cert.H1.Production.Leaves

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

/-- A transfer product with its two open edge colours specified. -/
def openTransfer (f : Nat → SiteSpec → Nat → Nat → Nat → VectorPolynomial)
    (site : Nat) : List PackedSite → List Nat → Nat → Nat → VectorPolynomial
  | [], _, a, b => if a == b then 1 else 0
  | s :: ss, codes, a, b => ((List.range 4).map fun k =>
      f site s.spec a k (codes.headD 0) * openTransfer f (site+1) ss codes.tail k b).sum

/-- The sum over all closed edge-colour paths. -/
def closedTransfer (f : Nat → SiteSpec → Nat → Nat → Nat → VectorPolynomial)
    (ss : List PackedSite) (codes : List Nat) : VectorPolynomial :=
  ((List.range 4).map fun a => openTransfer f 0 ss codes a a).sum

lemma getD_range_map {α : Type*} (f : Nat → α) (n i : Nat)
    (d : α) (hi : i < n) : ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range]

lemma polyEntry_ofFn (f : Nat → Nat → VectorPolynomial) (i j : Nat)
    (hi : i < 4) (hj : j < 4) :
    polyEntry ((List.range 4).map fun a => (List.range 4).map (f a)) i j = f i j := by
  unfold polyEntry
  rw [getD_range_map _ _ _ _ hi, getD_range_map _ _ _ _ hj]

lemma polyEntry_identity (i j : Nat) (hi : i < 4) (hj : j < 4) :
    polyEntry polyIdentity i j = if i == j then 1 else 0 := by
  exact polyEntry_ofFn _ i j hi hj

lemma polyEntry_mul (a b : PolyFour) (i j : Nat) (hi : i < 4) (hj : j < 4) :
    polyEntry (polyMul a b) i j =
      ((List.range 4).map fun k => polyEntry a i k * polyEntry b k j).sum := by
  exact polyEntry_ofFn _ i j hi hj

lemma polynomialRingProduct_entry
    (site : Nat) (ss : List PackedSite) (codes : List Nat)
    (i j : Nat) (hi : i < 4) (hj : j < 4) :
    polyEntry (polynomialRingProduct site ss codes) i j =
      openTransfer localPolynomial site ss codes i j := by
  induction ss generalizing site codes i with
  | nil => exact polyEntry_identity i j hi hj
  | cons s ss ih =>
      rw [polynomialRingProduct, polyEntry_mul _ _ i j hi hj]
      simp only [openTransfer]
      apply congrArg List.sum
      apply List.map_congr_left
      intro k hk
      have hk' : k < 4 := List.mem_range.mp hk
      rw [polyEntry_ofFn _ i k hi hk', ih (site+1) codes.tail k hk']

lemma polynomialRingValue_paths (ss : List PackedSite) (codes : List Nat) :
    polynomialRingValue ss codes = closedTransfer localPolynomial ss codes := by
  unfold polynomialRingValue polyTrace closedTransfer
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  exact polynomialRingProduct_entry 0 ss codes a a
    (List.mem_range.mp ha) (List.mem_range.mp ha)

end AKLT.W.H1C020
