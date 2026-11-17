module
public import AKLT.W.H1C020.GroupTokens
public import AKLT.W.H1C020.Fubini
public import AKLT.W.H1C020.Inversion

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

/-- Set only the passage coordinates to zero, leaving all other formal
coordinates untouched. This deletes precisely its linear bond terms. -/
def eraseCenterHom : MvPolynomial LocalVariable ℚ →+* MvPolynomial LocalVariable ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun w =>
    match w with
    | .inl (x,_) => if x = (0,0) then 0 else MvPolynomial.X w
    | .inr _ => MvPolynomial.X w

def ringIntegrand (π : PatternData) (r : Representation) : MvPolynomial LocalVariable ℚ :=
  eraseCenterHom (reducedIntegrand π r false)

def ringCoordinate (site color : Nat) : MvPolynomial LocalVariable ℚ :=
  if color == 0 then 1 else
    MvPolynomial.X (.inl (ringSites.getD site (0,0),
      ⟨(color-1)%3,Nat.mod_lt _ (by decide)⟩))

def insertedRingIntegrand (π : PatternData) (r : Representation) (codes : List Nat) :
    MvPolynomial LocalVariable ℚ :=
  ringIntegrand π r * ((List.range 8).map fun i => ringCoordinate i (codes.getD i 0)).prod

/-- No passage spin is contracted in this polynomial. -/
def ringPolynomial (π : PatternData) (r : Representation) (codes : List Nat) : VectorPolynomial :=
  contractSpins ((reducedSpinSites π r).erase (0,0)) π.statusAt
    (insertedRingIntegrand π r codes)

/-- Only the zero insertion and the pair insertions used by the constructor. -/
def CenterCode (ss : List PackedSite) (codes : List Nat) : Prop :=
  codes = [] ∨ ∃ xy ∈ centerPairs ss, ∃ k < 3,
    codes = centerCodes ss.length xy.1 xy.2 (k+1)

/-- The center step depends only on the eight center-bond flags. -/
def CenterGeometry (π : PatternData) (ss : List PackedSite) : Prop :=
  ss.length = 8 ∧ ∀ si ∈ ss.zipIdx,
    si.1.spec.center = presentBond π (ringSites.getD si.2 (0,0)) (0,0)

lemma centerGeometry_of_network (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (ss : List PackedSite) (hg : NetworkGeometry π r I ss) :
    CenterGeometry π ss := by
  exact ⟨hg.1, fun si hsi => (hg.2 si hsi).2.2.1⟩

/-- Remaining geometric/Fubini bridge, before the passage integration. There
are no integer numerators, matrix products, cleared-denominator factors,
current/next mode, or inversion in its conclusion. Both representations use
the actual erased integrand. -/
def Residual_ringFubini : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation,
  ∀ I : Finset (Fin 20), GroupInversion π r I → ∀ ss : List PackedSite,
  NetworkGeometry π r I ss → ∀ codes : List Nat, CenterCode ss codes →
    closedTransfer rationalLocal (eraseNetworkInversion ss) codes = ringPolynomial π r codes

/-- Remaining passage integration: its unit moment contributes the base and
its second moment contributes 1/3 or 1/5 times the eligible pairs. This step
contains no inversion or local transfer tensors and only needs center flags. -/
def Residual_centerContraction : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ ss : List PackedSite,
  CenterGeometry π ss → ∀ out : Nat, ringSites.getD out (0,0) = π.outgoing.step →
  ∀ next : Bool, reducedPolynomial π r next = ringPolynomial π r [] +
    MvPolynomial.C (1 / centerScale next) *
      centerInsertions (ringPolynomial π r) ss.length out next (centerPairs ss)

lemma centerInsertions_cons (value : List Nat → VectorPolynomial) (n out : Nat)
    (next : Bool) (x y : Nat) (pairs : List (Nat × Nat)) :
    centerInsertions value n out next ((x,y)::pairs) =
      if next && (x == out || y == out) then centerInsertions value n out next pairs
      else ((List.range 3).map (fun k => value (centerCodes n x y (k+1)))).sum +
        centerInsertions value n out next pairs := by
  by_cases h : (next && (x == out || y == out)) = true <;>
    simp only [centerInsertions, List.filterMap_cons, h, Bool.false_eq_true,
      ↓reduceIte, List.sum_cons]

lemma centerInsertions_congr (f g : List Nat → VectorPolynomial) (n out : Nat)
    (next : Bool) (pairs : List (Nat × Nat))
    (h : ∀ xy ∈ pairs, ∀ k < 3,
      f (centerCodes n xy.1 xy.2 (k+1)) = g (centerCodes n xy.1 xy.2 (k+1))) :
    centerInsertions f n out next pairs = centerInsertions g n out next pairs := by
  induction pairs with
  | nil => simp [centerInsertions]
  | cons xy pairs ih =>
      rcases xy with ⟨x,y⟩
      rw [centerInsertions_cons, centerInsertions_cons]
      have ht := ih (fun xy hxy k hk => h xy (by simp [hxy]) k hk)
      split
      · exact ht
      · rw [ht]
        congr 1
        apply congrArg List.sum
        apply List.map_congr_left
        intro k hk
        exact h (x,y) (by simp) k (List.mem_range.mp hk)

lemma invertPolynomial_centerInsertions (I : Finset (Fin 20))
    (value : List Nat → VectorPolynomial) (n out : Nat) (next : Bool)
    (pairs : List (Nat × Nat)) :
    invertPolynomial I (centerInsertions value n out next pairs) =
      centerInsertions (fun codes => invertPolynomial I (value codes)) n out next pairs := by
  induction pairs with
  | nil => simp [centerInsertions, invertPolynomial]
  | cons xy pairs ih =>
      rcases xy with ⟨x,y⟩
      rw [centerInsertions_cons, centerInsertions_cons]
      split
      · exact ih
      · rw [invertPolynomial_add, ih, invertPolynomial_listSum, List.map_map]
        rfl

theorem ringTransfer_of_residual (hF : Residual_ringFubini)
    (π : PatternData) (hπ : π.Covered) (r : Representation)
    (I : Finset (Fin 20)) (hI : GroupInversion π r I) (ss : List PackedSite)
    (hg : NetworkGeometry π r I ss) (codes : List Nat) (hc : CenterCode ss codes) :
    closedTransfer rationalLocal ss codes = invertPolynomial I (ringPolynomial π r codes) := by
  rw [← closedTransfer_inversion π r I hI ss hg codes, hF π hπ r I hI ss hg codes hc]

theorem rationalNetwork_of_residuals (hF : Residual_ringFubini)
    (hC : Residual_centerContraction) (π : PatternData) (hπ : π.Covered)
    (r : Representation) (I : Finset (Fin 20)) (hI : GroupInversion π r I)
    (ss : List PackedSite) (hg : NetworkGeometry π r I ss)
    (out : Nat) (hout : ringSites.getD out (0,0) = π.outgoing.step) (next : Bool) :
    rationalNetwork ss out next = invertPolynomial I (reducedPolynomial π r next) := by
  have hbase := ringTransfer_of_residual hF π hπ r I hI ss hg [] (Or.inl rfl)
  have hpairs := centerInsertions_congr (closedTransfer rationalLocal ss)
    (fun codes => invertPolynomial I (ringPolynomial π r codes)) ss.length out next
    (centerPairs ss) (by
      intro xy hxy k hk
      exact ringTransfer_of_residual hF π hπ r I hI ss hg _ (Or.inr ⟨xy,hxy,k,hk,rfl⟩))
  rw [hC π hπ r ss (centerGeometry_of_network π r I ss hg) out hout next,
    invertPolynomial_add, invertPolynomial_mul, invertPolynomial_C,
    invertPolynomial_centerInsertions]
  unfold rationalNetwork
  rw [hbase, hpairs]

end AKLT.W.H1C020
