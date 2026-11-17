module
public import CertData.H3.Kernel.Common

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.Cert.H3
open AKLT.Defs AKLT.Gen.Packed

def inBox (x : Plane) : Prop := -70 ≤ x.1 ∧ x.1 ≤ 70 ∧ -70 ≤ x.2 ∧ x.2 ≤ 70
instance (x : Plane) : Decidable (inBox x) := by unfold inBox; infer_instance
def valueAt {q : Nat} (plane cap : Phase → Fin q → Nat) (φ : Phase) (a : Fin q) (x : Plane) : Nat :=
  if inBox x then lane (plane φ a) 80 (siteIndex x) else cap φ a
def dataOf {q : Nat} (plane cap : Phase → Fin q → Nat) : StationaryData q where
  cap := cap
  value φ a x := lane (plane φ a) 80 (siteIndex x.val)

theorem mem_square_iff (x : Plane) : x ∈ square (0,0) certificateRadius ↔ inBox x := by
  simp [square, certificateRadius, inBox]
  omega

theorem extended_view {q : Nat} (plane cap : Phase → Fin q → Nat) (φ : Phase) (a : Fin q) (x : Plane) :
    (dataOf plane cap).extended φ a x = valueAt plane cap φ a x := by
  change (if x ∈ square (0,0) certificateRadius then lane (plane φ a) 80 (siteIndex x) else cap φ a) =
    if inBox x then lane (plane φ a) 80 (siteIndex x) else cap φ a
  simp only [mem_square_iff]

/-- Computable view of exactly the Defs row; only membership representation changes. -/
def viewRow {m q : Nat} (Q : MemoryQuotient m q) (plane cap : Phase → Fin q → Nat)
    (X : PairType) (d₀ : Compass) (φ : Phase) (a : Fin q) (x : Plane) : Prop :=
  (∑ d : Compass, ∑ ψ : Phase,
    coefficientCeiling (stationaryCoefficient Q X d₀ φ a x d ψ) *
      valueAt plane cap ψ (Q.successor a d) (x+d.step)) ≤
        certificateCoefficientScale * valueAt plane cap φ a x

instance viewRowDecidable {m q : Nat} (Q : MemoryQuotient m q) (plane cap : Phase → Fin q → Nat)
    (X : PairType) (d₀ : Compass) (φ : Phase) (a : Fin q) (x : Plane) :
    Decidable (viewRow Q plane cap X d₀ φ a x) := by unfold viewRow; infer_instance

theorem viewRow_iff {m q : Nat} (Q : MemoryQuotient m q) (plane cap : Phase → Fin q → Nat)
    (X : PairType) (d₀ : Compass) (φ : Phase) (a : Fin q) (x : Plane) :
    viewRow Q plane cap X d₀ φ a x ↔ DefRow Q (dataOf plane cap) X d₀ φ a x := by
  simp only [DefRow, extended_view, viewRow]

#print axioms mem_square_iff
#print axioms extended_view
#print axioms viewRow_iff
end AKLT.Cert.H3
