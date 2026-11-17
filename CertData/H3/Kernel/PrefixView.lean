module
public import CertData.H3.Kernel.Prefix
import all Init.Data.List.Sort.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.Cert.H3
open AKLT.Defs

/-- Structural merge, with the standard merge equation proved below. -/
def mergeFuel {α : Type*} (le : α → α → Bool) : Nat → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | f+1, x::xs, y::ys =>
    if le x y then x::mergeFuel le f xs (y::ys) else y::mergeFuel le f (x::xs) ys

theorem mergeFuel_eq {α : Type*} (le : α → α → Bool) (f : Nat) (xs ys : List α)
    (h : xs.length + ys.length ≤ f) : mergeFuel le f xs ys = List.merge xs ys le := by
  induction f generalizing xs ys with
  | zero =>
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs; subst ys
    simp only [mergeFuel, List.merge, List.nil_append]
  | succ f ih =>
    cases xs with
    | nil => simp only [mergeFuel, List.merge]
    | cons x xs =>
      cases ys with
      | nil => simp only [mergeFuel, List.merge]
      | cons y ys =>
        simp only [mergeFuel, List.merge]
        split
        · congr 1; exact ih _ _ (by simp only [List.length_cons] at *; omega)
        · congr 1; exact ih _ _ (by simp only [List.length_cons] at *; omega)

theorem mergeFuel_full {α : Type*} (le : α → α → Bool) (xs ys : List α) :
    mergeFuel le (xs.length+ys.length) xs ys = List.merge xs ys le := mergeFuel_eq le _ _ _ le_rfl

/-- Explicit structural fuel avoids the well-founded recursor in the Defs sort. -/
def mergeSortFuel {α : Type*} (le : α → α → Bool) : Nat → List α → List α
  | 0, _ => []
  | _+1, [] => []
  | _+1, [a] => [a]
  | f+1, a::b::xs =>
    let lr := List.MergeSort.Internal.splitInTwo ⟨a::b::xs,rfl⟩
    let l := mergeSortFuel le f lr.1.val
    let r := mergeSortFuel le f lr.2.val
    mergeFuel le (l.length+r.length) l r

theorem mergeSortFuel_eq {α : Type*} (le : α → α → Bool) (fuel : Nat) (xs : List α)
    (h : xs.length ≤ fuel) : mergeSortFuel le fuel xs = xs.mergeSort le := by
  induction fuel generalizing xs with
  | zero =>
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    simp only [mergeSortFuel, List.mergeSort]
  | succ f ih =>
    cases xs with
    | nil => simp only [mergeSortFuel, List.mergeSort]
    | cons a xs =>
      cases xs with
      | nil => simp only [mergeSortFuel, List.mergeSort]
      | cons b xs =>
        let lr := List.MergeSort.Internal.splitInTwo ⟨a::b::xs,rfl⟩
        have h1 : lr.1.val.length ≤ f := by
          have hh := lr.1.property
          simp only [List.length_cons] at h hh
          omega
        have h2 : lr.2.val.length ≤ f := by
          have hh := lr.2.property
          simp only [List.length_cons] at h hh
          omega
        simp only [mergeSortFuel, mergeFuel_full, List.mergeSort]
        rw [ih _ h1, ih _ h2]

/-- A decidable geometric spelling of the Defs dead-site filter. -/
def liveOtherView {n : Nat} (w : DirectionWord n) (i : Fin n) : Finset Plane :=
  ((responseNeighbours w i).erase (wordVertex kernelStart w (i.val+1))).filter
    (fun z => z ≠ kernelCentre ∧ departureCount kernelStart w i.val z < 2)

theorem liveOther_view {n : Nat} (w : DirectionWord n) (i : Fin n) :
    liveOtherNeighbours w i = liveOtherView w i := by
  classical
  ext z
  simp [liveOtherNeighbours, liveOtherView, deadAt, not_or, not_le]

noncomputable def kappaView {n : Nat} (w : DirectionWord n) (i : Fin n) : ℚ :=
  let live := liveOtherView w i
  let o := wordVertex kernelStart w (i.val+1)
  ∑ p ∈ (insert o live).powersetCard 2,
    (if o ∈ p then if live.card = 1 then betaPrimeBound (wordStraight kernelIncoming w i)
      else betaBound (wordStraight kernelIncoming w i)
    else alphaBound (wordStraight kernelIncoming w i)) * kernelWitness (responsePairType p)

theorem witnessKappa_view {n : Nat} (w : DirectionWord n) (i : Fin n) :
    witnessKappa w i = kappaView w i := by
  simp only [witnessKappa, responsePairs, pairCoefficient, liveOther_view, kappaView]

noncomputable def prefixPhasesView {n : Nat} (w : DirectionWord n) : Phase → ℚ :=
  (List.finRange n).foldl (fun p i ψ => ∑ φ : Phase, p φ *
    phaseTransition (if wordRevisit kernelStart w i then .revisit
      else if wordStraight kernelIncoming w i then .straight else .turn) (kappaView w i) φ ψ)
    phaseInitial

theorem prefixPhases_view {n : Nat} (w : DirectionWord n) : prefixPhases w = prefixPhasesView w := by
  simp only [prefixPhases, prefixPhasesView, witnessKappa_view]

noncomputable def shortOrderView {n : Nat} (w : DirectionWord n) (i j : Fin n) : Bool :=
  let ki := kappaView w i
  let kj := kappaView w j
  let xi := passageFactor (wordStraight kernelIncoming w i)
  let xj := passageFactor (wordStraight kernelIncoming w j)
  if ki = 0 then decide (kj = 0 ∧ i.val ≤ j.val)
  else if kj = 0 then true else
    let si := (xi-1)/(xi*ki)
    let sj := (xj-1)/(xj*kj)
    decide (si < sj ∨ (si = sj ∧ i.val ≤ j.val))

noncomputable def closedView {n : Nat} (w : DirectionWord n) : ℚ :=
  trailBaseWeight kernelStart w * exposureSum w (kappaView w)
    (if n ≤ 12 then mergeSortFuel (shortOrderView w) n (firstVisitList w)
     else (firstVisitList w).filter (wordStraight kernelIncoming w) ++
       (firstVisitList w).filter (fun i => !wordStraight kernelIncoming w i))

theorem closedContribution_view {n : Nat} (w : DirectionWord n) : closedContribution w = closedView w := by
  have hk : witnessKappa w = kappaView w := funext (witnessKappa_view w)
  have ho : shortOrderLE w = shortOrderView w := by
    funext i j
    simp only [shortOrderLE, shortOrderView, witnessKappa_view]
  have hl : (firstVisitList w).length ≤ n := by
    simpa only [firstVisitList, List.length_finRange] using List.length_filter_le (fun i => !wordRevisit kernelStart w i) (List.finRange n)
  simp only [closedContribution, kernelOrdering, closedView, hk, ho, mergeSortFuel_eq _ _ _ hl]

#print axioms liveOther_view
#print axioms mergeSortFuel_eq
#print axioms mergeFuel_eq
#print axioms mergeFuel_full
#print axioms witnessKappa_view
#print axioms prefixPhases_view
#print axioms closedContribution_view
end AKLT.Cert.H3
