import AKLT.Blueprint.Win.Defs

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Win

/-- `d:shells`, sec5-window.tex:423–425; app-topology.tex:4–8. Expand natAbs coordinate distances; omega proves comparison, positivity, symmetry and the nearest-neighbour implication. -/
def MetricFactsStatement : Prop :=
  (∀ x y : Plane, supDist x y ≤ latticeDist x y) ∧
    (∀ x y : Plane, Adjacent x y → StarAdjacent x y) ∧
    (∀ x y : Plane, Adjacent x y → Adjacent y x) ∧
    (∀ x y : Plane, StarAdjacent x y → StarAdjacent y x)

theorem metricFacts : MetricFactsStatement := by
  have hsub : ∀ a b : ℤ, (a - b).natAbs = (b - a).natAbs := by
    intro a b
    calc
      (a - b).natAbs = (-(a - b)).natAbs := (Int.natAbs_neg _).symm
      _ = (b - a).natAbs := by rw [neg_sub]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  · intro x y h
    unfold Adjacent latticeDist at h
    unfold StarAdjacent supDist
    omega
  · intro x y h
    simpa only [Adjacent, latticeDist, hsub x.1 y.1, hsub x.2 y.2] using h
  · intro x y h
    simpa only [StarAdjacent, supDist, hsub x.1 y.1, hsub x.2 y.2] using h

#print axioms metricFacts

/-- `l:thicken`, app-topology.tex:169–173. Choose an exterior site beyond a coordinate maximum. The infimum of natural distances is attained; identify its finite toNat value. -/
def FiniteDepthStatement : Prop :=
  ∀ G : Finset Plane, ∀ x : Plane,
    boundaryDepth G x ≠ ⊤ ∧
    (↑(boundaryDepth G x).toNat : ℕ∞) = boundaryDepth G x ∧
    (boundaryDepth G x = 0 ↔ x ∉ G) ∧
    ∀ y : Plane, (boundaryDepth G x).toNat ≤
      latticeDist x y + (boundaryDepth G y).toNat

/-- `l:boundaryconn`, app-topology.tex:10–15,126–128. The finite union of radius-one sup balls, minus U, is exactly the distance-one exterior boundary. The empty case gives both sides empty. -/
def BoundaryMembershipStatement : Prop :=
  ∀ U : Finset Plane, ∀ z : Plane,
    (z ∈ rawBoundary U ↔ z ∉ U ∧
      setDistance supDist z (↑U : Set Plane) = 1)

/-- `l:boundaryconn`, app-topology.tex:39–42. Take a maximum absolute endpoint coordinate over the finite support, enlarged to one. This includes the zero chain. -/
def ChainBoxStatement : Prop :=
  ∀ c : EdgeChain, ∃ R : ℤ, 1 ≤ R ∧ ChainInBox c R

/-- `l:boundaryconn`, app-topology.tex:28–34. Induct on diagonal edges of the finite support, adding the unique one-diagonal triangle at each step. The triangle correction lies in triangleSpan. -/
def DiagonalEliminationStatement : Prop :=
  ∀ c : EdgeChain, ChainStar c → ChainEven c →
    ∃ d : EdgeChain, ChainNN d ∧ ChainEven d ∧ c - d ∈ triangleSpan

/-- `l:boundaryconn`, app-topology.tex:47–53. Sum even vertex degrees on the finite supported portion of x₁≤i. Internal edges contribute twice and cancel in ZMod 2. -/
def ColumnFluxStatement : Prop :=
  ∀ c : EdgeChain, ChainNN c → ChainEven c → ∀ R : ℤ,
    1 ≤ R → ChainInBox c R → ∀ i : ℤ,
      ∑ r ∈ Finset.Icc (-R) R, horizontal c i r = 0

/-- `l:boundaryconn`, app-topology.tex:54–58. Only columns meeting the chain support contribute. Above R the tail is empty; below −R its value is the zero column flux. -/
def TailSupportStatement : Prop :=
  ∀ c : EdgeChain, ∀ R : ℤ, 1 ≤ R → ChainInBox c R →
    (∀ i : ℤ, ∑ r ∈ Finset.Icc (-R) R, horizontal c i r = 0) →
    ∃ P : Finset Plane, ∀ p : Plane, p ∉ P → tailCoefficient c R p.1 p.2 = 0

/-- `l:boundaryconn`, app-topology.tex:60–81. Compare horizontal coefficients by adjacent tail differences. Compare vertical coefficients by summing the even-degree relation over the finite interval and cancelling endpoints. -/
def PlaquetteReconstructionStatement : Prop :=
  ∀ c : EdgeChain, ChainNN c → ChainEven c → ∀ R : ℤ,
    1 ≤ R → ChainInBox c R →
    (∀ i : ℤ, ∑ r ∈ Finset.Icc (-R) R, horizontal c i r = 0) →
    ∀ P : Finset Plane, (∀ p : Plane, p ∉ P → tailCoefficient c R p.1 p.2 = 0) →
    c = ∑ p ∈ P, tailCoefficient c R p.1 p.2 • plaquette p

/-- `l:boundaryconn`, app-topology.tex:82–86. Split a unit square into its two diagonal triangles; their shared edge cancels in characteristic two. -/
def PlaquetteTrianglesStatement : Prop :=
  ∀ p : Plane, plaquette p ∈ triangleSpan

/-- `l:boundaryconn`, app-topology.tex:88–91. Choose a site of maximal first coordinate in A; its right neighbour is exterior and defines a crossing edge. -/
def CutEdgesNonemptyStatement : Prop :=
  ∀ A : Finset Plane, A.Nonempty → (cutEdges A).Nonempty

/-- `l:boundaryconn`, app-topology.tex:92–98. If two crossing edges are not reachable, take the finite linked component of one as E. Symmetry of Linked makes E closed. -/
def LinkedSeparationStatement : Prop :=
  ∀ A : Finset Plane,
    ¬ (∀ e ∈ cutEdges A, ∀ f ∈ cutEdges A,
      JoinedIn Linked (↑(cutEdges A) : Set LatticeEdge) e f) →
    ∃ E : Finset LatticeEdge, LinkClosed A E ∧
      ∃ e ∈ E, ∃ f ∈ cutEdges A, f ∉ E

/-- `l:boundaryconn`, app-topology.tex:99–107. A triangle has zero or two crossing edges. The two are linked and hence lie in the same selected component, so their parity cancels. -/
def TriangleCutParityStatement : Prop :=
  ∀ A : Finset Plane, ∀ E : Finset LatticeEdge, LinkClosed A E →
    ∀ x y z : Plane, IsTriangle x y z → cutParity E (triangle x y z) = 0

/-- `l:boundaryconn`, app-topology.tex:107–109. Extend the zero parity value from triangle generators to their span by linearity of the finite sum. -/
def SpanCutParityStatement : Prop :=
  ∀ E : Finset LatticeEdge,
    (∀ x y z : Plane, IsTriangle x y z → cutParity E (triangle x y z) = 0) →
    ∀ c ∈ triangleSpan, cutParity E c = 0

theorem spanCutParity : SpanCutParityStatement := by
  intro E h c hc
  induction hc using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x,y,z,ht,rfl⟩ := hz
    exact h x y z ht
  | zero => simp [cutParity]
  | add x y hx hy hpx hpy => simpa [cutParity, Finset.sum_add_distrib] using congrArg₂ (· + ·) hpx hpy
  | smul a x hx hpx =>
    simpa [cutParity, Finset.mul_sum] using congrArg (a * ·) hpx

#print axioms spanCutParity

/-- `l:boundaryconn`, app-topology.tex:111–122. Join the inside endpoints in A and the outside endpoints in Aᶜ. Concatenate the two crossing edges with these paths and keep the odd traversal multiplicities. -/
def TwoCrossingCycleStatement : Prop :=
  ∀ A : Finset Plane,
    ConnectedIn StarAdjacent (↑A) → ConnectedIn StarAdjacent {z | z ∉ A} →
    ∀ e ∈ cutEdges A, ∀ f ∈ cutEdges A, e ≠ f →
    ∃ c : EdgeChain, ChainStar c ∧ ChainEven c ∧ TwoCrossings A e f c

/-- `l:boundaryconn`, app-topology.tex:120–123. On E exactly e contributes one, since f is outside E. Evaluate the finite sum using sum_eq_single. -/
def TwoCrossingParityStatement : Prop :=
  ∀ A : Finset Plane, ∀ E : Finset LatticeEdge, E ⊆ cutEdges A →
    ∀ e ∈ E, ∀ f ∈ cutEdges A, f ∉ E → ∀ c : EdgeChain,
    TwoCrossings A e f c → cutParity E c = 1

/-- `l:boundaryconn`, app-topology.tex:126–135. Every crossing edge has exactly one exterior endpoint, and every raw-boundary vertex occurs. Linked edges give equal or star-adjacent exterior endpoints; map paths and suppress repeated vertices. -/
def OuterEndpointTransferStatement : Prop :=
  ∀ A : Finset Plane, (cutEdges A).Nonempty →
    (∀ e ∈ cutEdges A, ∀ f ∈ cutEdges A,
      JoinedIn Linked (↑(cutEdges A) : Set LatticeEdge) e f) →
    ConnectedIn StarAdjacent (↑(rawBoundary A))

/-- `l:thicken`, app-topology.tex:150–154. List the centre and four compass neighbours. Each neighbour joins the centre in one step, and the five coordinates are distinct. -/
def CrossFactsStatement : Prop :=
  ∀ x : Plane, (cross x).card = 5 ∧
    (∀ z : Plane, z ∈ cross x ↔ latticeDist z x ≤ 1) ∧
    ConnectedIn Adjacent (↑(cross x))

/-- `l:thicken`, app-topology.tex:155–162. For an axial star step the centres belong to both crosses; for a diagonal step choose one of the two common axial neighbours. -/
def CrossOverlapStatement : Prop :=
  ∀ x y : Plane, StarAdjacent x y → (cross x ∩ cross y).Nonempty

/-- `l:thicken`, app-topology.tex:162–167. Induct along the star path of centres, joining inside each cross through a shared point. Includes a singleton centre set. -/
def CrossUnionStatement : Prop :=
  ∀ X₀ : Finset Plane, ConnectedIn StarAdjacent (↑X₀) →
    (∀ x : Plane, ConnectedIn Adjacent (↑(cross x))) →
    (∀ x y : Plane, StarAdjacent x y → (cross x ∩ cross y).Nonempty) →
    ConnectedIn Adjacent (↑(thicken X₀))

/-- `l:thicken`, app-topology.tex:169–173. Finite complementary distances are 1-Lipschitz. For positive θ<1, moving one step multiplies θ^depth by at most θ⁻¹, including depth zero. -/
def NeighbourDecayStatement : Prop :=
  ∀ G : Finset Plane, ∀ θ : ℝ, 0 < θ → θ < 1 →
    ∀ x z : Plane, latticeDist z x ≤ 1 →
      decay θ (boundaryDepth G z) ≤ θ⁻¹ * decay θ (boundaryDepth G x)

/-- `l:thicken`, app-topology.tex:174–182. Overcount the union by its crosses and use five terms per cross. Only nonnegative weights are summed; no disjointness of crosses is assumed. -/
def CrossWeightSumStatement : Prop :=
  ∀ X₀ : Finset Plane, ∀ f : Plane → ℝ, (∀ z, 0 ≤ f z) → ∀ c : ℝ, 0 ≤ c →
    (∀ x : Plane, (cross x).card = 5) →
    (∀ x ∈ X₀, ∀ z ∈ cross x, f z ≤ c * f x) →
    ∑ z ∈ thicken X₀, f z ≤ 5 * c * ∑ x ∈ X₀, f x

/-- `l:Xconn`, sec5-window.tex:685–691. Order a finite connected set by graph distance from a root, breaking ties with any finite linear order. A nonroot vertex has a predecessor along a shortest path. -/
def ConnectedEnumerationStatement : Prop :=
  ∀ X : Finset Plane, ConnectedIn Adjacent (↑X) → Nonempty (RemovalEnumeration X)

end AKLT.Blueprint.Win
