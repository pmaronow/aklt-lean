module
public import AKLT.Blueprint.Rec.NodesKernel

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs

namespace AKLT.Blueprint.Rec

/-- `d:pairenv`, §7 lines 55–59. Positive finite probability laws and
the support norm bound give a bounded nonempty supremum (adjoin zero). -/
def EnvelopeBoundsStatement : Prop :=
  ∀ X : PairType, ∀ d : ℤ, 0 ≤ responseEnvelope X d ∧ responseEnvelope X d ≤ 2

/-- `d:pairenv`, §7 lines 36–59. Negative distances use d.toNat=0;
larger thresholds restrict the defining class. -/
def EnvelopeOrderStatement : Prop :=
  (∀ X : PairType, ∀ d : ℤ, d < 0 → responseEnvelope X d = responseEnvelope X 0) ∧
    ∀ X : PairType, Antitone (responseEnvelope X)

/-- `t:rec`, §7 lines 1047–1054. A nonempty finite G has a boundary
site, hence nonempty S. Every distance from an active site to original S is finite. -/
def ProtectedDistanceFiniteStatement : Prop :=
  ∀ G : Finset Plane, G.Nonempty → (protectedSites G).Nonempty ∧
    ∀ x : Plane, setDistance latticeDist x (↑(protectedSites G) : Set Plane) ≠ ⊤

/-- `l:recineq`, §7 lines 717–744. Deep pairs are interior at both
ends; choose a signed coordinate permutation sending the designated triple
to the canonical one. This preserves all factors, pins, and distances. -/
def PairCanonicalGeometryStatement : Prop :=
  ∀ p : PairData, ∃ φ : Plane ≃ Plane,
    φ p.c = kernelCentre ∧ φ p.u = kernelStart ∧ φ p.v = kernelTarget p.X ∧
    ∀ x y : Plane, latticeDist (φ x) (φ y) = latticeDist x y

/-- `l:recineq`, §7 lines 774–789. At each U departure, expose the
logarithmic response using the fixed ordering restricted to true U indices.
An arbitrary permutation of these indices is accepted in this statement. -/
def TraceExposureStatement : Prop :=
  ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ D : Network G, D.Auxiliary →
    ∀ u : Plane, D.AdmissibleStart u → ∀ T : Finset Plane, ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail D u T w →
    ∀ σ : Equiv.Perm (Fin n), ∀ x : Fin n → ℝ,
    (∀ i, 1 ≤ x i ∧ stepRatio (prefixNetwork D u w i.val) τ true
      (wordVertex u w i.val) (wordVertex u w (i.val+1)) ≤ x i) →
    |traceRatio D τ true (wordVertices u w) - traceRatio D τ false (wordVertices u w)| ≤
      ∑ k : Fin n,
        |Real.log (stepRatio (prefixNetwork D u w (σ k).val) τ false
          (wordVertex u w (σ k).val) (wordVertex u w ((σ k).val+1))) -
         Real.log (stepRatio (prefixNetwork D u w (σ k).val) τ true
          (wordVertex u w (σ k).val) (wordVertex u w ((σ k).val+1)))| *
        ∏ l ∈ Finset.univ.filter (fun l : Fin n => l.val ≤ k.val), x (σ l)

/-- `e:rec-pair-envelope`, §7 lines 796–815. Triangle inequalities
transfer a response pair's depth by the actual maximum shift. The integer
subtraction is in Z, so negative depths use the constant extension. -/
def PairEnvelopeShiftStatement : Prop :=
  ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ E : Network G,
    ∀ X : PairType, ∀ a b c : Plane, E.ResponsePair X a b c →
    ∀ u v : Plane, ∀ d : ℕ,
    (d : ℕ∞) ≤ min (setDistance latticeDist u (↑(protectedSites G) : Set Plane))
      (setDistance latticeDist v (↑(protectedSites G) : Set Plane)) →
    let s := max (min (latticeDist a u) (latticeDist a v))
      (min (latticeDist b u) (latticeDist b v))
    |E.expectation τ true (fun n => dot (n a) (n b)) -
      E.expectation τ false (fun n => dot (n a) (n b))| ≤ responseEnvelope X ((d : ℤ) - s)

/-- `l:recineq`, §7 lines 817–858. Compare one true trace to its lattice
trail: true U departures are first visits; extra initial D sites only lower
the base weight. Dead sites are actually removed; missing neighbors choose
beta-prime or the larger beta. The target remains live until the endpoint. -/
def TraceKernelLengthStatement : Prop :=
  Top.H1Statement → ∀ p : PairData, ∀ d : ℕ, 1 ≤ d → (d : ℕ∞) ≤ p.depth →
    ∀ n : ℕ, |firstLength p n| ≤
      ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2),
        (kernelLengthCoefficient p.X Y s n : ℝ) * responseEnvelope Y ((d : ℤ) - s)

/-- `e:rec-T1`, §7 lines 858–870. Sum the length bounds and exchange
nonnegative sums. H2 at theta=1 proves real-row summability before toReal. -/
def FirstTermBoundStatement : Prop :=
  Top.H1Statement → ∀ CV q : ℝ, OpenTrailBound CV q →
    ∀ p : PairData, ∀ d : ℕ, 1 ≤ d → (d : ℕ∞) ≤ p.depth →
      |firstTerm p| ≤ recursionSeries p.X d

/-- `l:recineq`, §7 lines 872–900. Apply the second pair expansion in
the terminal auxiliary network, with target e and stopping set exactly S.
The first lost arrival bond gives target degree≤3. Use the twelve exceptions
and the original distance from v to S. -/
def ResidualTargetBoundStatement : Prop :=
  Top.H1Statement → ∀ CV q : ℝ, OpenTrailBound CV q →
    ∀ p : PairData, p.u ∉ protectedSites p.G → p.v ∉ protectedSites p.G →
    ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w →
    wordVertex p.u w n ∈ protectedSites p.G → ∀ b : Bool,
    |(traceNetwork p.normalized (wordVertices p.u w)).expectation p.τ b
      (fun a => dot (a (wordVertex p.u w n)) (a p.v))| ≤
        onePointConstant CV q * q^(protectedDistance p.G p.v)

/-- `l:recineq`, §7 lines 902–924. Bound residuals uniformly, then
sum pointwise maxima in the first expansion enlarged to ALL first hits of S.
The two original depths give q^(2d) and exactly the retained C_T. -/
def SecondTermBoundStatement : Prop :=
  Top.H1Statement → ∀ CV q : ℝ, OpenTrailBound CV q →
    ∀ p : PairData, ∀ d : ℕ, 1 ≤ d → (d : ℕ∞) ≤ p.depth →
      |secondTerm p| ≤ sourceConstant CV q * q^(2*d)

/-- `l:recineq`, §7 lines 746–764. Subtract the two finite expansions,
using the same coefficient and pin-independent target factor in T₁. -/
def PairResponseSplitStatement : Prop :=
  ∀ p : PairData, p.u ∉ protectedSites p.G → p.v ∉ protectedSites p.G →
    p.response = firstTerm p + secondTerm p

/-- `d:pairenv`: the elementary least-upper-bound direction. It applies
to the empty class because zero was explicitly adjoined. -/
theorem envelope_le_of_pair_bounds (X : PairType) (d : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ p : PairData, p.X = X → (d : ℕ∞) ≤ p.depth → |p.response| ≤ B) :
    responseEnvelope X d ≤ B := by
  apply csSup_le
  · exact ⟨0, Or.inl (Set.mem_singleton 0)⟩
  · intro r hr
    rcases hr with hr | ⟨G, τ, D, u, v, c, hp, hd, rfl⟩
    · have hr0 : r = 0 := hr
      simpa [hr0] using hB
    · exact h ⟨G, τ, D, X, u, v, c, hp⟩ rfl (by simpa [PairData.depth] using hd)

/-- `t:rec`, §7 lines 1036–1054. Realize removals as an ordinary U/X
domain, with original pins and no hole pins. A distance-two pair has one of
the two types. Its protected distance is finite whenever the pair exists. -/
def RemovalEnvelopeStatement : Prop :=
  ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ Y : Finset Plane,
    Y ⊆ G \ protectedSites G → ∀ u v : Plane,
    u ∈ G \ Y → v ∈ G \ Y → latticeDist u v = 2 →
    (∃ c ∈ Y, Adjacent u c ∧ Adjacent v c) →
    ∃ X : PairType, ∃ d : ℕ,
      min (setDistance latticeDist u (↑(protectedSites G) : Set Plane))
        (setDistance latticeDist v (↑(protectedSites G) : Set Plane)) = (d : ℕ∞) ∧
      |pinnedExpectation G Y τ (fun n => dot (n u) (n v)) -
        freeExpectation G Y (fun n => dot (n u) (n v))| ≤ responseEnvelope X d

end AKLT.Blueprint.Rec
