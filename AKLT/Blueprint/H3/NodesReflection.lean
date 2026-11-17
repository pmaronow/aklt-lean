module
public import AKLT.Blueprint.H3.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.H3

/-- `l:kernel-reflection`, lines 1035–1044: reflection transports word geometry and
all prefix departure counts. It fixes u,c,v_B and the virtual incoming direction; the same
index is used before/after reflection, so chronological first-hit conditions are preserved. -/
def ReflectionGeometryStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n,
    (∀ j : ℕ, wordVertex kernelStart (reflectWord w) j = reflectSite (wordVertex kernelStart w j)) ∧
    (ClosedTrail .B w ↔ ClosedTrail .B (reflectWord w)) ∧
    (FirstDirection w .north ↔ FirstDirection (reflectWord w) .south) ∧
    ∀ i : Fin n,
      wordStraight kernelIncoming w i = wordStraight kernelIncoming (reflectWord w) i ∧
      wordRevisit kernelStart w i = wordRevisit kernelStart (reflectWord w) i

/-- `l:kernel-reflection`, lines 1045–1052: reflection bijects the finite live-pair sets.
Transport neighbors, erases, dead predicates and powersetCard through the lattice involution. -/
def ReflectionLivePairsStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n, ∀ i : Fin n,
    (responsePairs w i).image (fun p => p.image reflectSite) = responsePairs (reflectWord w) i

/-- `l:kernel-reflection`, lines 1050–1059: scalar labels on each live pair.
Cardinality and outgoing membership select the same alpha/beta/beta-prime row; opposite and
perpendicular pairs keep their type. The l1 isometry fixing u,v_B preserves each pair's shift. -/
def ReflectionPairLabelsStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n, ∀ i : Fin n, ∀ p ∈ responsePairs w i,
    pairCoefficient w i p = pairCoefficient (reflectWord w) i (p.image reflectSite) ∧
    responsePairType p = responsePairType (p.image reflectSite) ∧
    pairShift .B p = pairShift .B (p.image reflectSite)

/-- Derived node for `l:kernel-reflection`, lines 1045–1059: the live response-pair bijection, exact
coefficients, types and ambient shifts. Image under an involution preserves cardinalities;
reflection is an l1 isometry and fixes both B endpoints. No C-row shift claim is made. -/
def ReflectionPairsStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n, ∀ i : Fin n,
    (responsePairs w i).image (fun p => p.image reflectSite) = responsePairs (reflectWord w) i ∧
    ∀ p ∈ responsePairs w i,
      pairCoefficient w i p = pairCoefficient (reflectWord w) i (p.image reflectSite) ∧
      responsePairType p = responsePairType (p.image reflectSite) ∧
      pairShift .B p = pairShift .B (p.image reflectSite)

/-- `l:kernel-reflection`, lines 1060–1065: the ordering keys and tie breakers are
unchanged once straightness, revisits and h-rewards agree pointwise. This finite-list
congruence is separate from lattice geometry and also applies to non-trails. -/
def ReflectionOrderingAlgebraStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n,
    (∀ i : Fin n,
      wordStraight kernelIncoming w i = wordStraight kernelIncoming (reflectWord w) i ∧
      wordRevisit kernelStart w i = wordRevisit kernelStart (reflectWord w) i ∧
      witnessKappa w i = witnessKappa (reflectWord w) i) →
    trailWeight kernelStart kernelIncoming w = trailWeight kernelStart kernelIncoming (reflectWord w) ∧
      kernelOrdering w = kernelOrdering (reflectWord w) ∧
      closedContribution w = closedContribution (reflectWord w)

/-- Pair bijection and label transport are independent smaller reflection leaves. -/
theorem reflectionPairs_of_nodes (hLive : ReflectionLivePairsStatement)
    (hLabels : ReflectionPairLabelsStatement) : ReflectionPairsStatement :=
  fun n w i => ⟨hLive n w i, hLabels n w i⟩

/-- Immediate congruence of all finite ordering expressions once their inputs agree. -/
theorem reflectionOrderingAlgebra_proved : ReflectionOrderingAlgebraStatement := by
  intro n w h
  have hs : wordStraight kernelIncoming w = wordStraight kernelIncoming (reflectWord w) :=
    funext fun i => (h i).1
  have hr : wordRevisit kernelStart w = wordRevisit kernelStart (reflectWord w) :=
    funext fun i => (h i).2.1
  have hk : witnessKappa w = witnessKappa (reflectWord w) := funext fun i => (h i).2.2
  have hf : firstVisitList w = firstVisitList (reflectWord w) := by
    simp only [firstVisitList, hr]
  have ho : shortOrderLE w = shortOrderLE (reflectWord w) := by
    funext i j
    simp only [shortOrderLE, hs, hk]
  have hord : kernelOrdering w = kernelOrdering (reflectWord w) := by
    simp only [kernelOrdering, hf, ho, hs]
  have he : ∀ l : List (Fin n), exposureSum w (witnessKappa w) l =
      exposureSum (reflectWord w) (witnessKappa (reflectWord w)) l := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [exposureSum]
      rw [ih]
      simp only [hs, hk]
  refine ⟨?_, hord, ?_⟩
  · simp only [trailWeight, hs, hr]
  · unfold closedContribution
    simp only [trailBaseWeight, hr, hord, he]

end AKLT.Blueprint.H3
