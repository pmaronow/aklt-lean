from pathlib import Path
import json
root = Path('/home/ubuntu/aklt/wt/BP_WIN/AKLT/Blueprint/Win')
report = Path('/home/ubuntu/aklt/reports/BP_WIN')
entries=[]
files={}
# The author now reserves every new leaf-proof first attempt for a different,
# cheaper model. Only these five pre-rule proofs may be retained by this script.
RETAINED_LEAF_PROOFS={'MetricFacts','SpanCutParity','LogLipschitz','CutCostNonnegative','WindowCostArithmetic'}
def add(module,name,label,lines,difficulty,idea,statement,dependencies=(),proof=None):
    if proof is not None and name not in RETAINED_LEAF_PROOFS:
        raise ValueError('New leaf proofs belong to a different, cheaper model: '+name)
    doc=f'/-- `{label}`, {lines}. {idea} -/'
    text=doc+'\ndef '+name+'Statement : Prop :=\n  '+statement.strip()+'\n'
    if proof:
        text+='\ntheorem '+name[0].lower()+name[1:]+' : '+name+'Statement := by\n'+proof.rstrip()+'\n'
        text+='\n#print axioms '+name[0].lower()+name[1:]+'\n'
    files.setdefault(module,[]).append(text)
    entries.append(dict(lean_name='AKLT.Blueprint.Win.'+name+'Statement',module='AKLT.Blueprint.Win.'+module,paper_label=label,paper_lines=lines,difficulty=difficulty,dependencies=list(dependencies),suggested_proof_route=idea,status='proved' if proof else 'open'))

# Shared shell geometry. Each premise below is local geometric data, not a leaf name.
add('NodesShell','ShellScale','l:shellgeom','sec5-window.tex:50–58','easy',
 'Square the two square-root identities; use s≥16 to bound the low-degree terms and Int.floor bounds.',
 '''∀ l u : ℕ, 1 ≤ l → geometryThreshold l ≤ u →
    16 ≤ shellSpacing u ∧ 6 * ((l : ℝ) + 1) ≤ shellSpacing u ∧
    shellSpacing u ^ 4 = (u : ℝ) ∧
    shellSpacing u ^ 2 + 4 * shellSpacing u / 3 < (u : ℝ) ∧
    shellSpacing u ^ 2 + shellSpacing u < (u : ℝ) / 2 ∧
    2 * shellSpacing u / 3 < (⌊shellSpacing u⌋ : ℤ)''',
 ['geometryThreshold','shellSpacing','Real.sq_sqrt','Int.sub_one_lt_floor'])
add('NodesShell','CloseCorner','l:shellgeom','sec5-window.tex:40–76','medium',
 'Translate and use signed coordinate permutations to put the exterior site on the bottom edge. Only one corner can have radius below u.',
 '''∀ a y : Plane, ∀ u : ℕ,
    setDistance supDist y (↑(square a u) : Set Plane) = 1 →
    ((squareCorners a u).filter fun c => supDist c y < u).card ≤ 1''',
 ['squareCorners','setDistance','supDist','Int.natAbs_neg'])
add('NodesShell','ExceptionalLocalization','l:shellgeom','sec5-window.tex:58–70','easy',
 'Apply the sup-distance triangle inequality and k_i≤s²+s to every exceptional witness. Retain its radial error as well as its corner.',
 '''∀ a y : Plane, ∀ u : ℕ,
    shellSpacing u ^ 2 + 4 * shellSpacing u / 3 < (u : ℝ) →
    ∀ i ∈ exceptionalIndices a y u, ∃ c ∈ squareCorners a u,
      supDist c y < u ∧
      |(supDist c y : ℝ) - (shellRadius u i : ℝ)| < shellSpacing u / 3''',
 ['exceptionalIndices','Int.floor_le','supDist'])
add('NodesShell','RadiusGap','l:shellgeom','sec5-window.tex:72–76','easy',
 'Use floor(x+s)≥floor(x)+floor(s), and floor(s)>2s/3 for s≥16.',
 '''∀ u : ℕ, 16 ≤ shellSpacing u → ∀ i j : ℤ, i < j →
    2 * shellSpacing u / 3 < (shellRadius u j - shellRadius u i : ℝ)''',
 ['shellRadius','Int.le_floor_add'])
add('NodesShell','ExceptionalCount','l:shellgeom','sec5-window.tex:64–76','easy',
 'The unique close corner cannot approximate two radii separated by more than 2s/3. Apply Finset.card_le_one.',
 '''∀ a y : Plane, ∀ u : ℕ,
    ((squareCorners a u).filter fun c => supDist c y < u).card ≤ 1 →
    (∀ i ∈ exceptionalIndices a y u, ∃ c ∈ squareCorners a u,
      supDist c y < u ∧
      |(supDist c y : ℝ) - (shellRadius u i : ℝ)| < shellSpacing u / 3) →
    (∀ i j : ℤ, i < j →
      2 * shellSpacing u / 3 < (shellRadius u j - shellRadius u i : ℝ)) →
    (exceptionalIndices a y u).card ≤ 1''',
 ['Finset.card_le_one','abs_sub_le_iff'])
add('NodesShell','SideCornerWitness','l:shellgeom','sec5-window.tex:78–100','medium',
 'Normalize the exterior side. A vertical side with insufficient parallel clearance has a lowest shell point within s/3 of a bottom corner; horizontal sides already have large clearance.',
 '''∀ l : ℕ, ∀ a y : Plane, ∀ u : ℕ, ShellSetup l a y u →
    ∀ i : ℤ, 2 ≤ i → i ≤ lastShellIndex u →
    ¬ ParallelClearance a y u i → i ∈ exceptionalIndices a y u''',
 ['ParallelClearance','ShellSetup','shellRadius','exceptionalIndices'])
add('NodesShell','NearShellCount','l:shellgeom','sec5-window.tex:102–108','medium',
 'Cover the near layer by the eight intersections of shell sides with perpendicular exterior strips. Parallel intersections are excluded by clearance and s/3>l.',
 '''∀ l : ℕ, ∀ a y : Plane, ∀ u : ℕ, ShellSetup l a y u →
    ∀ i : ℤ, 2 ≤ i → i ≤ lastShellIndex u →
    ParallelClearance a y u i → (nearShell a y u l i).card ≤ 8 * l''',
 ['nearShell','ParallelClearance','Finset.card_biUnion_le'])
add('NodesShell','ShellInclusion','l:shellgeom','sec5-window.tex:110–111','easy',
 'For s≥2, floor(i s)≥i s−1>(i−1)s. Membership filters then give inclusion.',
 '''∀ a y : Plane, ∀ u : ℕ, 2 ≤ shellSpacing u →
    ∀ i : ℤ, 2 ≤ i → shell a y u i ⊆ farVolume a y u i''',
 ['shell','farVolume','Int.lt_floor_add_one'])
add('NodesShell','PredecessorShell','l:shellgeom','sec5-window.tex:112–123','easy',
 'Extract a distance-one witness in F_i. Sup-distance is 1-Lipschitz, so integrality pins the old radius to floor((i−1)s). Empty F_i has infinite distance.',
 '''∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, 2 ≤ i →
    ∀ x ∈ square a u \\ farVolume a y u i,
      setDistance supDist x (↑(farVolume a y u i) : Set Plane) ≤ 1 →
        x ∈ shell a y u (i - 1)''',
 ['setDistance','ENat','Int.floor_eq_iff'])
add('NodesShell','SeedSeparation','l:shellgeom','sec5-window.tex:120–123','easy',
 'Every remaining point has radius >(i−1)s≥s>1. The infimum over an empty set is top.',
 '''∀ a y : Plane, ∀ u : ℕ, 2 ≤ shellSpacing u → ∀ i : ℤ, 2 ≤ i →
    ¬ setDistance supDist y (↑(farVolume a y u i) : Set Plane) ≤ 1''',
 ['farVolume','setDistance','iInf_le'])

# Appendix B: finite F₂ chains and the actual star boundary.
add('NodesTopology','MetricFacts','d:shells','sec5-window.tex:423–425; app-topology.tex:4–8','easy',
 'Expand natAbs coordinate distances; omega proves comparison, positivity, symmetry and the nearest-neighbour implication.',
 '''(∀ x y : Plane, supDist x y ≤ latticeDist x y) ∧
    (∀ x y : Plane, Adjacent x y → StarAdjacent x y) ∧
    (∀ x y : Plane, Adjacent x y → Adjacent y x) ∧
    (∀ x y : Plane, StarAdjacent x y → StarAdjacent y x)''',
 ['latticeDist','supDist','Int.natAbs_neg'],
 '''  have hsub : ∀ a b : ℤ, (a - b).natAbs = (b - a).natAbs := by
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
    simpa only [StarAdjacent, supDist, hsub x.1 y.1, hsub x.2 y.2] using h''')
add('NodesTopology','FiniteDepth','l:thicken','app-topology.tex:169–173','easy',
 'Choose an exterior site beyond a coordinate maximum. The infimum of natural distances is attained; identify its finite toNat value.',
 '''∀ G : Finset Plane, ∀ x : Plane,
    boundaryDepth G x ≠ ⊤ ∧
    (↑(boundaryDepth G x).toNat : ℕ∞) = boundaryDepth G x ∧
    (boundaryDepth G x = 0 ↔ x ∉ G) ∧
    ∀ y : Plane, (boundaryDepth G x).toNat ≤
      latticeDist x y + (boundaryDepth G y).toNat''',
 ['boundaryDepth','setDistance','iInf','latticeDist'])
add('NodesTopology','BoundaryMembership','l:boundaryconn','app-topology.tex:10–15,126–128','easy',
 'The finite union of radius-one sup balls, minus U, is exactly the distance-one exterior boundary. The empty case gives both sides empty.',
 '''∀ U : Finset Plane, ∀ z : Plane,
    (z ∈ rawBoundary U ↔ z ∉ U ∧
      setDistance supDist z (↑U : Set Plane) = 1)''',
 ['rawBoundary','starBall','setDistance'])
add('NodesTopology','ChainBox','l:boundaryconn','app-topology.tex:39–42','easy',
 'Take a maximum absolute endpoint coordinate over the finite support, enlarged to one. This includes the zero chain.',
 '''∀ c : EdgeChain, ∃ R : ℤ, 1 ≤ R ∧ ChainInBox c R''',
 ['EdgeChain','ChainInBox','Finsupp.support'])
add('NodesTopology','DiagonalElimination','l:boundaryconn','app-topology.tex:28–34','medium',
 'Induct on diagonal edges of the finite support, adding the unique one-diagonal triangle at each step. The triangle correction lies in triangleSpan.',
 '''∀ c : EdgeChain, ChainStar c → ChainEven c →
    ∃ d : EdgeChain, ChainNN d ∧ ChainEven d ∧ c - d ∈ triangleSpan''',
 ['triangle','triangleSpan','Finsupp.support','ZMod 2'])
add('NodesTopology','ColumnFlux','l:boundaryconn','app-topology.tex:47–53','medium',
 'Sum even vertex degrees on the finite supported portion of x₁≤i. Internal edges contribute twice and cancel in ZMod 2.',
 '''∀ c : EdgeChain, ChainNN c → ChainEven c → ∀ R : ℤ,
    1 ≤ R → ChainInBox c R → ∀ i : ℤ,
      ∑ r ∈ Finset.Icc (-R) R, horizontal c i r = 0''',
 ['ChainEven','ChainInBox','horizontal','Finset.sum_comm'])
add('NodesTopology','TailSupport','l:boundaryconn','app-topology.tex:54–58','easy',
 'Only columns meeting the chain support contribute. Above R the tail is empty; below −R its value is the zero column flux.',
 '''∀ c : EdgeChain, ∀ R : ℤ, 1 ≤ R → ChainInBox c R →
    (∀ i : ℤ, ∑ r ∈ Finset.Icc (-R) R, horizontal c i r = 0) →
    ∃ P : Finset Plane, ∀ p : Plane, p ∉ P → tailCoefficient c R p.1 p.2 = 0''',
 ['tailCoefficient','ChainInBox','Finset.Icc'])
add('NodesTopology','PlaquetteReconstruction','l:boundaryconn','app-topology.tex:60–81','medium',
 'Compare horizontal coefficients by adjacent tail differences. Compare vertical coefficients by summing the even-degree relation over the finite interval and cancelling endpoints.',
 '''∀ c : EdgeChain, ChainNN c → ChainEven c → ∀ R : ℤ,
    1 ≤ R → ChainInBox c R →
    (∀ i : ℤ, ∑ r ∈ Finset.Icc (-R) R, horizontal c i r = 0) →
    ∀ P : Finset Plane, (∀ p : Plane, p ∉ P → tailCoefficient c R p.1 p.2 = 0) →
    c = ∑ p ∈ P, tailCoefficient c R p.1 p.2 • plaquette p''',
 ['Finsupp.ext','tailCoefficient','plaquette','Finset.sum_range_sub'])
add('NodesTopology','PlaquetteTriangles','l:boundaryconn','app-topology.tex:82–86','easy',
 'Split a unit square into its two diagonal triangles; their shared edge cancels in characteristic two.',
 '''∀ p : Plane, plaquette p ∈ triangleSpan''',
 ['triangleSpan','Submodule.subset_span','Sym2.eq_swap','ZMod 2'])
add('NodesTopology','CutEdgesNonempty','l:boundaryconn','app-topology.tex:88–91','easy',
 'Choose a site of maximal first coordinate in A; its right neighbour is exterior and defines a crossing edge.',
 '''∀ A : Finset Plane, A.Nonempty → (cutEdges A).Nonempty''',
 ['cutEdges','Finset.exists_max_image'])
add('NodesTopology','LinkedSeparation','l:boundaryconn','app-topology.tex:92–98','easy',
 'If two crossing edges are not reachable, take the finite linked component of one as E. Symmetry of Linked makes E closed.',
 '''∀ A : Finset Plane,
    ¬ (∀ e ∈ cutEdges A, ∀ f ∈ cutEdges A,
      JoinedIn Linked (↑(cutEdges A) : Set LatticeEdge) e f) →
    ∃ E : Finset LatticeEdge, LinkClosed A E ∧
      ∃ e ∈ E, ∃ f ∈ cutEdges A, f ∉ E''',
 ['JoinedIn','Linked','LinkClosed','Relation.ReflTransGen'])
add('NodesTopology','TriangleCutParity','l:boundaryconn','app-topology.tex:99–107','easy',
 'A triangle has zero or two crossing edges. The two are linked and hence lie in the same selected component, so their parity cancels.',
 '''∀ A : Finset Plane, ∀ E : Finset LatticeEdge, LinkClosed A E →
    ∀ x y z : Plane, IsTriangle x y z → cutParity E (triangle x y z) = 0''',
 ['LinkClosed','cutParity','triangle','ZMod 2'])
add('NodesTopology','SpanCutParity','l:boundaryconn','app-topology.tex:107–109','easy',
 'Extend the zero parity value from triangle generators to their span by linearity of the finite sum.',
 '''∀ E : Finset LatticeEdge,
    (∀ x y z : Plane, IsTriangle x y z → cutParity E (triangle x y z) = 0) →
    ∀ c ∈ triangleSpan, cutParity E c = 0''',
 ['Submodule.span_induction','cutParity','Finset.sum_add_distrib'])
add('NodesTopology','TwoCrossingCycle','l:boundaryconn','app-topology.tex:111–122','medium',
 'Join the inside endpoints in A and the outside endpoints in Aᶜ. Concatenate the two crossing edges with these paths and keep the odd traversal multiplicities.',
 '''∀ A : Finset Plane,
    ConnectedIn StarAdjacent (↑A) → ConnectedIn StarAdjacent {z | z ∉ A} →
    ∀ e ∈ cutEdges A, ∀ f ∈ cutEdges A, e ≠ f →
    ∃ c : EdgeChain, ChainStar c ∧ ChainEven c ∧ TwoCrossings A e f c''',
 ['JoinedIn','EdgeChain','ChainEven','TwoCrossings','Relation.ReflTransGen'])
add('NodesTopology','TwoCrossingParity','l:boundaryconn','app-topology.tex:120–123','easy',
 'On E exactly e contributes one, since f is outside E. Evaluate the finite sum using sum_eq_single.',
 '''∀ A : Finset Plane, ∀ E : Finset LatticeEdge, E ⊆ cutEdges A →
    ∀ e ∈ E, ∀ f ∈ cutEdges A, f ∉ E → ∀ c : EdgeChain,
    TwoCrossings A e f c → cutParity E c = 1''',
 ['TwoCrossings','cutParity','Finset.sum_eq_single'])
add('NodesTopology','OuterEndpointTransfer','l:boundaryconn','app-topology.tex:126–135','medium',
 'Every crossing edge has exactly one exterior endpoint, and every raw-boundary vertex occurs. Linked edges give equal or star-adjacent exterior endpoints; map paths and suppress repeated vertices.',
 '''∀ A : Finset Plane, (cutEdges A).Nonempty →
    (∀ e ∈ cutEdges A, ∀ f ∈ cutEdges A,
      JoinedIn Linked (↑(cutEdges A) : Set LatticeEdge) e f) →
    ConnectedIn StarAdjacent (↑(rawBoundary A))''',
 ['cutEdges','rawBoundary','JoinedIn','Sym2'])
add('NodesTopology','CrossFacts','l:thicken','app-topology.tex:150–154','easy',
 'List the centre and four compass neighbours. Each neighbour joins the centre in one step, and the five coordinates are distinct.',
 '''∀ x : Plane, (cross x).card = 5 ∧
    (∀ z : Plane, z ∈ cross x ↔ latticeDist z x ≤ 1) ∧
    ConnectedIn Adjacent (↑(cross x))''',
 ['cross','Compass.step','JoinedIn'])
add('NodesTopology','CrossOverlap','l:thicken','app-topology.tex:155–162','easy',
 'For an axial star step the centres belong to both crosses; for a diagonal step choose one of the two common axial neighbours.',
 '''∀ x y : Plane, StarAdjacent x y → (cross x ∩ cross y).Nonempty''',
 ['cross','StarAdjacent','Int.natCast_natAbs'])
add('NodesTopology','CrossUnion','l:thicken','app-topology.tex:162–167','easy',
 'Induct along the star path of centres, joining inside each cross through a shared point. Includes a singleton centre set.',
 '''∀ X₀ : Finset Plane, ConnectedIn StarAdjacent (↑X₀) →
    (∀ x : Plane, ConnectedIn Adjacent (↑(cross x))) →
    (∀ x y : Plane, StarAdjacent x y → (cross x ∩ cross y).Nonempty) →
    ConnectedIn Adjacent (↑(thicken X₀))''',
 ['JoinedIn','thicken','Relation.ReflTransGen'])
add('NodesTopology','NeighbourDecay','l:thicken','app-topology.tex:169–173','easy',
 'Finite complementary distances are 1-Lipschitz. For positive θ<1, moving one step multiplies θ^depth by at most θ⁻¹, including depth zero.',
 '''∀ G : Finset Plane, ∀ θ : ℝ, 0 < θ → θ < 1 →
    ∀ x z : Plane, latticeDist z x ≤ 1 →
      decay θ (boundaryDepth G z) ≤ θ⁻¹ * decay θ (boundaryDepth G x)''',
 ['boundaryDepth','decay',"pow_le_pow_right_of_le_one'"])
add('NodesTopology','CrossWeightSum','l:thicken','app-topology.tex:174–182','easy',
 'Overcount the union by its crosses and use five terms per cross. Only nonnegative weights are summed; no disjointness of crosses is assumed.',
 '''∀ X₀ : Finset Plane, ∀ f : Plane → ℝ, (∀ z, 0 ≤ f z) → ∀ c : ℝ, 0 ≤ c →
    (∀ x : Plane, (cross x).card = 5) →
    (∀ x ∈ X₀, ∀ z ∈ cross x, f z ≤ c * f x) →
    ∑ z ∈ thicken X₀, f z ≤ 5 * c * ∑ x ∈ X₀, f x''',
 ['thicken','Finset.sum_le_sum','Finset.sum_le_sum'])
add('NodesTopology','ConnectedEnumeration','l:Xconn','sec5-window.tex:685–691','medium',
 'Order a finite connected set by graph distance from a root, breaking ties with any finite linear order. A nonroot vertex has a predecessor along a shortest path.',
 '''∀ X : Finset Plane, ConnectedIn Adjacent (↑X) → Nonempty (RemovalEnumeration X)''',
 ['RemovalEnumeration','JoinedIn','SimpleGraph.Reachable.exists_isPath'])

# d:thickcut and the physical site geometry.
add('NodesTaper','CutScales','l:cutgeom','sec5-window.tex:419–439','easy',
 'Use s≥390 and u=s⁴ to establish every inequality in e:sitecutscales; retain the strict predecessor-shell clearance.',
 '''∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    390 ≤ shellSpacing u ∧
    2 * shellSpacing u - 1 ≤ (shellRadius u i : ℝ) ∧
    (shellRadius u i : ℝ) ≤ shellSpacing u ^ 2 ∧
    (shellRadius u i : ℝ) ≤ (u : ℝ) - 31 ∧
    (i - 1 : ℝ) * shellSpacing u <
      (shellRadius u i : ℝ) - shellSpacing u / 12 - 1''',
 ['CutSetup','shellSpacing','shellRadius','Real.sq_sqrt'])
add('NodesTaper','CoreConnected','l:cutgeom','sec5-window.tex:463–486','medium',
 'Intersect the inner square h≥32 with the shell. Each coordinate interval contains a shell endpoint, giving a shell corner; join all remaining side segments to that corner.',
 '''∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    ConnectedIn Adjacent (↑(core a y u i)) ∧ core a y u i ⊆ taper a y u i''',
 ['core','taper','squareDepth','Finset.Icc'])
add('NodesTaper','RadialPaths','l:cutgeom','sec5-window.tex:441–461','medium',
 'Induct on the natural radial offset. Above k move all maximal coordinates inward; below k move one maximal coordinate outward. Both moves reduce t while preserving h−t≥32.',
 '''∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    ∀ z ∈ taper a y u i, ∃ w ∈ core a y u i,
      JoinedIn StarAdjacent (↑(taper a y u i)) z w''',
 ['radialOffset','squareDepth','core','JoinedIn'])
add('NodesTaper','SquareExterior','l:cutgeom','sec5-window.tex:488–494','easy',
 'Join each exterior site to the row at height a₂+u+1 along coordinate segments outside the square, then join on that row.',
 '''∀ a : Plane, ∀ u : ℕ, ConnectedIn Adjacent {z | z ∉ square a u}''',
 ['square','JoinedIn','Finset.mem_Icc'])
add('NodesTaper','ComplementEscape','l:cutgeom','sec5-window.tex:494–512','medium',
 'Use the three cases ρ>k+T, ρ<k−T, or h−t<32. Move outward from y, inward to exterior y, or outward from a respectively, with a decreasing termination measure.',
 '''∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    ∀ z : Plane, z ∉ taper a y u i → ∃ w : Plane, w ∉ square a u ∧
      JoinedIn Adjacent {v | v ∉ taper a y u i} z w''',
 ['radialOffset','squareDepth','JoinedIn','latticeDist'])
add('NodesTaper','WindowBuffer','l:cutgeom','sec5-window.tex:514–529','easy',
 'Window sites have t=0 and h≥65, their neighbours have t≤1 and h≥64. Every tapered site and its neighbours remain beyond the previous radius and inside C.',
 '''∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    window a y u 64 i ⊆ taper a y u i ∧
    taper a y u i ⊆ farVolume a y u i ∧
    (∀ z ∈ window a y u 64 i, ∀ w, Adjacent z w → w ∈ taper a y u i) ∧
    NoBond (↑(taper a y u i)) {z | z ∉ farVolume a y u i} ∧
    cutRaw a y u i ⊆ cutVolume a y u i''',
 ['taper','window','NoBond','cutRaw'])
add('NodesTaper','RawRange','l:cutgeom','sec5-window.tex:523–558','easy',
 'Compare a raw-boundary site to a star neighbour in U using the one-Lipschitz h and t. In the near case failure of U forces 30+t≤h<32+t.',
 '''∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    ∀ x ∈ cutRaw a y u i,
    (radialOffset y u i x : ℝ) ≤ shellSpacing u / 12 + 1 ∧
    ((radialOffset y u i x : ℝ) ≤ shellSpacing u / 12 →
      30 + (radialOffset y u i x : ℤ) ≤ squareDepth a u x ∧
      squareDepth a u x < 32 + (radialOffset y u i x : ℤ))''',
 ['rawBoundary','squareDepth','radialOffset'])
add('NodesTaper','RawDistanceObstructions','l:cutgeom','sec5-window.tex:531–548','easy',
 'Use Gᶜ=B∪Cᶜ∪(C\\F): the three sup-distance lower bounds are max(t,65−h), h, and s−1−t. The lattice distance dominates sup-distance.',
 '''∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    ∀ x ∈ cutRaw a y u i,
    min (max (radialOffset y u i x : ℝ) (65 - (squareDepth a u x : ℝ)))
      (min (squareDepth a u x : ℝ)
        (shellSpacing u - 1 - (radialOffset y u i x : ℝ))) ≤
      ((boundaryDepth (cutVolume a y u i) x).toNat : ℝ)''',
 ['cutVolume','boundaryDepth','squareDepth','supDist'])
add('NodesTaper','RawDepthArithmetic','l:cutgeom','sec5-window.tex:550–572','easy',
 'Treat t≤T and t>T separately. The integer near depth uses max(t,16)−2, and the far lower bound is T−1; both exceed or equal 14.',
 '''∀ s t h b : ℝ, 390 ≤ s → 0 ≤ t → t ≤ s / 12 + 1 →
    (t ≤ s / 12 → 30 + t ≤ h ∧ h < 32 + t) →
    30 + t ≤ h →
    min (max t (65 - h)) (min h (s - 1 - t)) ≤ b →
    14 ≤ b ∧ (t ≤ s / 12 → max t 16 - 2 ≤ b) ∧
      (s / 12 < t → s / 12 - 1 ≤ b)''',
 ['min_le_iff','max_le_iff','linarith'])
add('NodesTaper','RawHeight','l:cutgeom','sec5-window.tex:523–525','easy',
 'A star neighbour of U has h≥30+t, by comparing both one-Lipschitz functions to its neighbour in U. State this separately so the far-depth arithmetic does not silently require the near-range premise.',
 '''∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    ∀ x ∈ cutRaw a y u i, 30 + (radialOffset y u i x : ℤ) ≤ squareDepth a u x''',
 ['rawBoundary','taper','squareDepth'])
add('NodesTaper','SignedSideExclusion','l:cutgeom','sec5-window.tex:574–616','medium',
 'Use signed depth, separating a shell side inside C, beyond the selected exterior side, or beyond the opposite side. ParallelClearance excludes equality in the first case, and the scale bounds exclude it in the other two.',
 '''∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    ParallelClearance a y u i → NoCoincidence a y u i''',
 ['NoCoincidence','ParallelClearance','coord','SignedUnit'])
add('NodesTaper','SquareIntersection','l:cutgeom','sec5-window.tex:618–622','easy',
 'Cover one square boundary by four sides; each meets at most the two perpendicular sides of the other. Coincident parallel sides are explicitly excluded.',
 '''∀ a y : Plane, ∀ r R : ℤ, 0 < r → 0 < R →
    (∀ axis : Fin 2, ∀ ε δ : ℤ, SignedUnit ε → SignedUnit δ →
      coord axis y + ε * r ≠ coord axis a + δ * R) →
    (sphere y r ∩ sphere a R).card ≤ 8''',
 ['sphere','Finset.card_biUnion_le','coord'])
add('NodesTaper','RawLayerCount','l:cutgeom','sec5-window.tex:574–624','medium',
 'At t=j, use radii k±j and at most three integer h-levels in [30+j,32+j). Bound the union of the six sphere intersections by 6×8.',
 '''∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    NoCoincidence a y u i →
    (∀ x ∈ cutRaw a y u i, (radialOffset y u i x : ℝ) ≤ shellSpacing u / 12 →
      30 + (radialOffset y u i x : ℤ) ≤ squareDepth a u x ∧
      squareDepth a u x < 32 + (radialOffset y u i x : ℤ)) →
    (∀ a y : Plane, ∀ r R : ℤ, 0 < r → 0 < R →
      (∀ axis : Fin 2, ∀ ε δ : ℤ, SignedUnit ε → SignedUnit δ →
        coord axis y + ε * r ≠ coord axis a + δ * R) →
      (sphere y r ∩ sphere a R).card ≤ 8) →
    ∀ j : ℕ, (j : ℝ) ≤ shellSpacing u / 12 →
      ((cutRaw a y u i).filter fun x => radialOffset y u i x = j).card ≤ 48''',
 ['sphere','NoCoincidence','squareDepth','Finset.card_biUnion_le'])
add('NodesTaper','NearSeries','l:cutgeom','sec5-window.tex:626–634','easy',
 'Split j≤16 from the geometric tail starting at 17. Use summability for θ∈(0,1) and θ/(1−θ)≤1/(1−θ).',
 '''∀ θ : ℝ, 0 < θ → θ < 1 →
    Summable (fun j : ℕ => θ ^ (max j 16 - 2)) ∧
    48 * (∑' j : ℕ, θ ^ (max j 16 - 2)) ≤ nearCost θ''',
 ['hasSum_geometric_of_lt_one','Summable.tsum_le_tsum','nearCost'])
add('NodesTaper','RawWeightSum','l:cutgeom','sec5-window.tex:626–639','medium',
 'Group the near finite sum by the natural offset and compare with the nonnegative infinite series. Bound far sites by the containing square cardinality and the real-power depth estimate.',
 '''∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    cutRaw a y u i ⊆ square a u →
    (∀ x ∈ cutRaw a y u i,
      ((radialOffset y u i x : ℝ) ≤ shellSpacing u / 12 →
        (max (radialOffset y u i x) 16 - 2 : ℕ) ≤
          (boundaryDepth (cutVolume a y u i) x).toNat) ∧
      (shellSpacing u / 12 < (radialOffset y u i x : ℝ) →
        shellSpacing u / 12 - 1 ≤
          ((boundaryDepth (cutVolume a y u i) x).toNat : ℝ))) →
    (∀ j : ℕ, (j : ℝ) ≤ shellSpacing u / 12 →
      ((cutRaw a y u i).filter fun x => radialOffset y u i x = j).card ≤ 48) →
    ∀ θ : ℝ, 0 < θ → θ < 1 →
    Summable (fun j : ℕ => θ ^ (max j 16 - 2)) →
    48 * (∑' j : ℕ, θ ^ (max j 16 - 2)) ≤ nearCost θ →
    ∑ x ∈ cutRaw a y u i, decay θ (boundaryDepth (cutVolume a y u i) x) ≤
      nearCost θ + tailCost θ u''',
 ['decay','Real.rpow_natCast','Finset.sum_fiberwise','nearCost','tailCost'])
add('NodesTaper','ThickDepth','l:cutgeom','sec5-window.tex:641–646','easy',
 'Apply finite-depth Lipschitz at a centre of each cross. Depth at least 13 forces membership in G and excludes its protected layer.',
 '''∀ G X₀ : Finset Plane, (∀ x ∈ X₀, 14 ≤ boundaryDepth G x) →
    thicken X₀ ⊆ G ∧ ∀ z ∈ thicken X₀, 13 ≤ boundaryDepth G z''',
 ['boundaryDepth','protectedSites','cross','thicken'])
add('NodesTaper','CutSeparation','l:cutgeom','sec5-window.tex:657–667','easy',
 'The specified pieces partition G\\X. Any edge crossing U meets its raw boundary, hence X; the two boundary pin restrictions follow from the two buffers.',
 '''∀ F B U X : Finset Plane,
    B ⊆ U → U ⊆ F →
    (∀ z ∈ B, ∀ w, Adjacent z w → w ∈ U) → NoBond (↑U) {z | z ∉ F} →
    rawBoundary U ⊆ X → X ⊆ F \\ B →
    SeparatingCut F B X ((U \\ B) \\ X) ((F \\ B) \\ (U ∪ X))''',
 ['SeparatingCut','rawBoundary','NoBond','Finset.ext'])

# Removal steps and their scalar estimates.
add('NodesRemoval','OriginalPositivity','l:finitefacts','sec5-window.tex:175–177,278–279','medium',
 'Reindex G\\Y by Fin n, orient each bond once, and use FiniteFactsStatement for the U network. Zero U atoms disappear; the empty product equals one.',
 '''AKLT.Blueprint.Top.FiniteFactsStatement →
    ∀ G Y : Finset Plane, ∀ τ : PinAssignment G,
    0 < pinnedSum G Y τ (fun _ => 1) ∧ 0 < freeSum G Y (fun _ => 1)''',
 ['Top.FiniteFactsStatement','FiniteSpinNetwork.Valid','pinnedSum','freeSum','Fintype.equivFin'])
add('NodesRemoval','PartLawBridge','l:finitefacts','sec5-window.tex:276–301','easy',
 'Move the positive scalar normalizer through the finite sum. This identifies partMean with expectation under its actual normalized product weight.',
 '''AKLT.Blueprint.Top.MomentsStatement →
    ∀ G Y : Finset Plane, ∀ τ : PinAssignment G, ∀ pinned : Bool,
    0 < partSum pinned G Y τ (fun _ => 1) →
    Probability (partLaw pinned G Y τ) ∧
    ∀ f : (Plane → Vec3) → ℝ,
      partMean pinned G Y τ f =
        expectation (partLaw pinned G Y τ) (fun σ => f (extendIcoSpins σ))''',
 ['Top.MomentsStatement','partLaw','partMean','normalize','Finset.sum_div'])
add('NodesRemoval','EnumerationSteps','l:removal','sec5-window.tex:248–255','easy',
 'Injectivity identifies each prefix update with insertion of the next site. The original-depth bound keeps all prefixes outside S(G); predecessor adjacency supplies the missing bond after the seed.',
 '''∀ G X : Finset Plane, X ⊆ G → (∀ x ∈ X, 3 ≤ boundaryDepth G x) →
    ∀ e : RemovalEnumeration X,
    removedPrefix e 0 = ∅ ∧ removedPrefix e (e.last + 1) = X ∧
    ∀ j : Fin (e.last + 1),
      removedPrefix e (j.val + 1) = insert (e.site j) (removedPrefix e j.val) ∧
      RemovalStep G (removedPrefix e j.val) (e.site j) ∧
      (0 < j.val → ∃ c ∈ removedPrefix e j.val, Adjacent (e.site j) c)''',
 ['RemovalEnumeration','removedPrefix','protectedSites','Finset.mem_image'])
add('NodesRemoval','SurvivorGeometry','l:removal','sec5-window.tex:251–255,287–292,321–327','easy',
 'All four neighbours of a depth-three site are original interior sites. After removal they are pairwise at distance two, have at most three surviving bonds, and are at original depth at least two.',
 '''∀ G Y : Finset Plane, ∀ x : Plane, RemovalStep G Y x →
    (survivors G Y x).card ≤ 4 ∧
    (Y = ∅ → (survivors G Y x).card = 4) ∧
    ((∃ c ∈ Y, Adjacent x c) → (survivors G Y x).card ≤ 3) ∧
    (∀ z ∈ survivors G Y x, 2 ≤ boundaryDepth G z) ∧
    (∀ z ∈ survivors G Y x, ∀ w ∈ survivors G Y x, z ≠ w → latticeDist z w = 2)''',
 ['survivors','RemovalStep','neighbours','Compass'])
add('NodesRemoval','RemovalIntegral','e:removalpolynomial','sec5-window.tex:257–279','medium',
 'Sum the removed site first. Odd tensors vanish, the second tensor supplies pairSum/3, and only all four surviving neighbours create quartic/15. Other sites retain their original legs.',
 '''AKLT.Blueprint.Top.MomentsStatement →
    ∀ G Y : Finset Plane, ∀ τ : PinAssignment G, ∀ x : Plane, RemovalStep G Y x →
    ∀ pinned : Bool,
      partSum pinned G Y τ (fun _ => 1) =
        partSum pinned G (insert x Y) τ (removalPolynomial x (survivors G Y x))''',
 ['Top.MomentsStatement','partSum','removalPolynomial','Fintype.prod_sum'])
add('NodesRemoval','NeighbourFibres','l:removal','sec5-window.tex:287–301','medium',
 'Freeze the other spins on a positive fibre. Nonadjacency of the neighbours factors that fibre into one-site laws with at most three unit fields. Apply the three-factor mean bound and retain only positive fibres.',
 '''AKLT.Blueprint.Top.MomentsStatement → AKLT.Blueprint.Top.ThreeFactorMeanStatement →
    ∀ G Y : Finset Plane, ∀ τ : PinAssignment G, ∀ x : Plane, RemovalStep G Y x →
    ∀ pinned : Bool,
      NeighbourControl (partLaw pinned G (insert x Y) τ) (survivors G Y x)''',
 ['Top.MomentsStatement','Top.ThreeFactorMeanStatement','NeighbourControl','restEvent'])
add('NodesRemoval','PairMeanAveraging','l:removal','sec5-window.tex:303–310','easy',
 'On every positive fibre use 2∑mᵣ·mₜ=|∑mᵣ|²−∑|mᵣ|². Average the resulting lower bound; zero-mass fibres contribute zero.',
 '''∀ D V : Finset Plane, V ⊆ D → ∀ p : Weight (PlaneConfiguration D),
    Probability p → NeighbourControl p V →
    -(9 / 50 : ℝ) * (V.card : ℝ) ≤
      expectation p (fun σ => pairSum V (extendIcoSpins σ))''',
 ['NeighbourControl','fibreMean','normSq','Finset.sum_comm'])
add('NodesRemoval','QuarticMeanBound','l:removal','sec5-window.tex:311–315,345','easy',
 'Each scalar product of support vectors has absolute value at most one by Cauchy–Schwarz. The three products in quartic sum to at most three; average with a probability law.',
 '''AKLT.Blueprint.Top.MomentsStatement →
    ∀ D : Finset Plane, ∀ p : Weight (PlaneConfiguration D), Probability p →
    ∀ x : Plane, |expectation p (fun σ => quartic x (extendIcoSpins σ))| ≤ 3''',
 ['Top.MomentsStatement','dot','normSq','quartic','Finset.abs_sum_le_sum_abs'])
add('NodesRemoval','PolynomialLower','l:removal','sec5-window.tex:309–317','easy',
 'Linearity of expectation gives 1−3k/50, with an extra worst-case 3/15 only when k=4. Recover 41/50 or 14/25, both above one half.',
 '''∀ D V : Finset Plane, ∀ p : Weight (PlaneConfiguration D), Probability p →
    ∀ x : Plane, V.card ≤ 4 →
    -(9 / 50 : ℝ) * (V.card : ℝ) ≤ expectation p (fun σ => pairSum V (extendIcoSpins σ)) →
    |expectation p (fun σ => quartic x (extendIcoSpins σ))| ≤ 3 →
    (if V.card = 4 then (14 / 25 : ℝ) else 41 / 50) ≤
      expectation p (fun σ => removalPolynomial x V (extendIcoSpins σ))''',
 ['removalPolynomial','expectation','Probability','Finset.sum_add_distrib'])
add('NodesRemoval','RemovedPairResponse','h:P','sec5-window.tex:321–337','easy',
 'The pair has its common removed neighbour x in insert x Y. Lipschitz depth gives distance to the original S(G) at least b_G(x)−3; convert finite ENat depth before the natural subtraction.',
 '''∀ A θ : ℝ, ResponseProperty A θ →
    ∀ G Y : Finset Plane, ∀ τ : PinAssignment G, ∀ x : Plane, RemovalStep G Y x →
    ∀ z ∈ survivors G Y x, ∀ w ∈ survivors G Y x, z ≠ w →
    |partMean true G (insert x Y) τ (fun n => dot (n z) (n w)) -
      partMean false G (insert x Y) τ (fun n => dot (n z) (n w))| ≤
      A * θ ^ depthShift G x''',
 ['ResponseProperty','protectedSites','depthShift','decay','survivors'])
add('NodesRemoval','PairDifference','l:removal','sec5-window.tex:341–350','easy',
 'Expand pairSum over ordered unequal pairs and divide by two. There are at most six unordered pairs for k=4 and at most three for k≤3.',
 '''∀ G Y : Finset Plane, ∀ τ : PinAssignment G, ∀ _x : Plane,
    ∀ V : Finset Plane, V.card ≤ 4 → ∀ d : ℝ, 0 ≤ d →
    (∀ z ∈ V, ∀ w ∈ V, z ≠ w →
      |partMean true G Y τ (fun n => dot (n z) (n w)) -
        partMean false G Y τ (fun n => dot (n z) (n w))| ≤ d) →
    |partMean true G Y τ (pairSum V) - partMean false G Y τ (pairSum V)| ≤
      (if V.card = 4 then 6 else 3) * d''',
 ['pairSum','partMean','Finset.offDiag','Finset.abs_sum_le_sum_abs'])
add('NodesRemoval','LogLipschitz','l:removal','sec5-window.tex:339–340','easy',
 'Apply the mean value estimate for log on [1/2,∞), where its derivative is bounded by two.',
 '''∀ a b : ℝ, (1 / 2 : ℝ) ≤ a → (1 / 2 : ℝ) ≤ b →
    |Real.log a - Real.log b| ≤ 2 * |a - b|''',
 ['Real.log_le_sub_one_of_pos','Real.log_div','abs_sub_comm'])
add('NodesRemoval','LogStepIdentity','e:removaltelescope','sec5-window.tex:276–285','easy',
 'Divide the two integration identities by their positive after-removal partition sums and expand log of the pinned/free ratio.',
 '''∀ G Y : Finset Plane, ∀ τ : PinAssignment G, ∀ x : Plane,
    (∀ pinned : Bool, 0 < partSum pinned G Y τ (fun _ => 1) ∧
      0 < partSum pinned G (insert x Y) τ (fun _ => 1)) →
    (∀ pinned : Bool, partSum pinned G Y τ (fun _ => 1) =
      partSum pinned G (insert x Y) τ (removalPolynomial x (survivors G Y x))) →
    logRatio G Y τ - logRatio G (insert x Y) τ =
      Real.log (partMean true G (insert x Y) τ (removalPolynomial x (survivors G Y x))) -
      Real.log (partMean false G (insert x Y) τ (removalPolynomial x (survivors G Y x)))''',
 ['Real.log_div','Real.log_mul','partMean','partitionRatio'])
add('NodesRemoval','LocalLogEstimate','l:removal','sec5-window.tex:339–350','easy',
 'Use linearity of partMean, the pair difference, the quartic bound, and the supplied log Lipschitz estimate. The seed costs at most 4d+4/5≤1+4d; a nonseed costs at most 2d.',
 '''(∀ a b : ℝ, (1 / 2 : ℝ) ≤ a → (1 / 2 : ℝ) ≤ b →
      |Real.log a - Real.log b| ≤ 2 * |a - b|) →
    ∀ G Y : Finset Plane, ∀ τ : PinAssignment G, ∀ x : Plane,
    ∀ V : Finset Plane, V.card ≤ 4 → ∀ d : ℝ, 0 ≤ d →
    (∀ pinned : Bool, 0 < partSum pinned G Y τ (fun _ => 1) ∧
      (1 / 2 : ℝ) ≤ partMean pinned G Y τ (removalPolynomial x V) ∧
      |partMean pinned G Y τ (quartic x)| ≤ 3) →
    |partMean true G Y τ (pairSum V) - partMean false G Y τ (pairSum V)| ≤
      (if V.card = 4 then 6 else 3) * d →
    |Real.log (partMean true G Y τ (removalPolynomial x V)) -
      Real.log (partMean false G Y τ (removalPolynomial x V))| ≤
      if V.card = 4 then 1 + 4 * d else 2 * d''',
 ['partMean','removalPolynomial','Real.log','abs_add_le'])
add('NodesRemoval','RemovalTelescope','e:removaltelescope','sec5-window.tex:280–285,352–356','easy',
 'Telescope the original-volume logRatio over all prefixes, bound the absolute sum, and isolate index zero. Enumeration injectivity gives the one-seed convention also for a singleton cut.',
 '''∀ G X : Finset Plane, ∀ τ : PinAssignment G, ∀ e : RemovalEnumeration X,
    removedPrefix e 0 = ∅ → removedPrefix e (e.last + 1) = X →
    ∀ A θ : ℝ,
    (∀ j : Fin (e.last + 1),
      |logRatio G (removedPrefix e j.val) τ - logRatio G (removedPrefix e (j.val + 1)) τ| ≤
      if j.val = 0 then 1 + 4 * A * θ ^ depthShift G (e.site j)
      else 2 * A * θ ^ depthShift G (e.site j)) →
    |cutError G X τ| ≤ 1 + 4 * A * θ ^ depthShift G (e.site 0) +
      2 * A * ∑ j : Fin e.last, θ ^ depthShift G (e.site j.succ)''',
 ['Fin.sum_univ_succ','Finset.sum_range_sub','Finset.abs_sum_le_sum_abs','cutError'])
add('NodesRemoval','RemovalCostSum','t:cutMOS','sec5-window.tex:746–752','easy',
 'Bound the seed decay by one. Use b≥3 before converting θ^(b−3)=θ^(-3)θ^b and enlarge the nonseed sum to all X.',
 '''∀ G X : Finset Plane, ∀ τ : PinAssignment G, ∀ e : RemovalEnumeration X,
    (∀ x ∈ X, 3 ≤ boundaryDepth G x) → ∀ A θ : ℝ, 0 ≤ A → 0 < θ → θ < 1 →
    |cutError G X τ| ≤ 1 + 4 * A * θ ^ depthShift G (e.site 0) +
      2 * A * ∑ j : Fin e.last, θ ^ depthShift G (e.site j.succ) →
    |cutError G X τ| ≤ 1 + 4 * A +
      2 * A * θ ^ (-3 : ℤ) * ∑ z ∈ X, decay θ (boundaryDepth G z)''',
 ['RemovalEnumeration','depthShift','decay','zpow_sub₀','Finset.sum_le_sum_of_subset_of_nonneg'])

# Partition factorization, quadrature only on summed sites, common minorization.
add('NodesCut','FrameFibreSum','e:windowfactor','sec5-window.tex:154–174','medium',
 'Split configurations on F into configurations on B and G=F\\B. With no exterior neighbour of B, products factor into the actual W_B and the complementary frame partition sum.',
 '''AKLT.Blueprint.Top.ThreeFramesStatement →
    ∀ κ : Plane → Fin 3, ProperPlaneColouring κ →
    ∀ F B : Finset Plane, B ⊆ F → NoBond (↑B) {z | z ∉ F} →
    ∀ unit : ∀ j a, normSq (frameVector j a) = 1,
    ∀ η : FrameBoundary F, ∀ s : PlaneConfiguration B,
    marginalNumerator κ F B η s = windowWeight κ B s *
      framePinnedSum κ (F \\ B) ∅ (cutPins κ (F \\ B) F B unit η s)''',
 ['Top.ThreeFramesStatement','marginalNumerator','framePinnedSum','Equiv.piCongrLeft'])
add('NodesCut','ComplementQuadrature','l:exact','sec5-window.tex:171–174,775–778','medium',
 'Represent the complementary partition integrand as a polynomial with separate degree at most four. Apply the actual frame moment laws; the window configuration is held fixed.',
 '''AKLT.Blueprint.Top.ThreeFramesStatement → AKLT.Blueprint.Top.ExactStatement →
    ∀ κ : Plane → Fin 3, ∀ G Y : Finset Plane, ∀ τ : PinAssignment G,
    framePinnedSum κ G Y τ = pinnedSum G Y τ (fun _ => 1)''',
 ['Top.ThreeFramesStatement','Top.ExactStatement','SeparateDegreeFour','framePinnedSum'])
add('NodesCut','MarginalNormalization','e:windowfactor','sec5-window.tex:166–177','easy',
 'Sum the unnormalized fibre numerators over the nonempty finite window product and move the positive original normalizer through each sum.',
 '''∀ κ : Plane → Fin 3, ∀ F B : Finset Plane, B ⊆ F →
    ∀ η : FrameBoundary F, 0 < ∑ σ : PlaneConfiguration F, planeWeight κ F η σ →
    planeMarginal κ F B η = normalize (marginalNumerator κ F B η)''',
 ['planeMarginal','marginalNumerator','normalize','Finset.sum_comm'])
add('NodesCut','OriginalFactorization','e:cutfactorization','sec5-window.tex:179–191','medium',
 'Use the partition of G\\X and absence of interpiece bonds to split the finite product sum. Component sums remove G\\H from original G and therefore carry no new legs into X.',
 '''∀ F B X G₁ G₂ : Finset Plane, SeparatingCut F B X G₁ G₂ →
    ∀ τ : PinAssignment (F \\ B),
    pinnedSum (F \\ B) X τ (fun _ => 1) =
      componentSum (F \\ B) G₁ τ * componentSum (F \\ B) G₂ τ ∧
    freeSum (F \\ B) X (fun _ => 1) =
      freeSum (F \\ B) ((F \\ B) \\ G₁) (fun _ => 1) *
      freeSum (F \\ B) ((F \\ B) \\ G₂) (fun _ => 1)''',
 ['SeparatingCut','componentSum','pinnedSum','freeSum','Fintype.prod_sum'])
add('NodesCut','ComponentPins','l:cut','sec5-window.tex:179–184','easy',
 'On G₁ all retained original pins end in B; on G₂ all end outside F. Compare the component products term by term, discarding pins whose tails were removed.',
 '''∀ κ : Plane → Fin 3, ∀ F B X G₁ G₂ : Finset Plane,
    SeparatingCut F B X G₁ G₂ →
    ∀ unit : ∀ j a, normSq (frameVector j a) = 1,
    ∀ η ξ : FrameBoundary F, ∀ s t : PlaneConfiguration B,
    componentSum (F \\ B) G₁ (cutPins κ (F \\ B) F B unit η s) =
      componentSum (F \\ B) G₁ (cutPins κ (F \\ B) F B unit ξ s) ∧
    componentSum (F \\ B) G₂ (cutPins κ (F \\ B) F B unit η s) =
      componentSum (F \\ B) G₂ (cutPins κ (F \\ B) F B unit η t)''',
 ['SeparatingCut','cutPins','componentSum','originalLegs'])
add('NodesCut','WindowWeightPositive','l:cut','sec5-window.tex:155–163','easy',
 'Every actual frame bond of a proper colouring is bounded below by positive frameBound; finite site and bond products are positive, including an empty window.',
 '''AKLT.Blueprint.Top.ThreeFramesStatement →
    ∀ κ : Plane → Fin 3, ProperPlaneColouring κ →
    ∀ B : Finset Plane, ∀ s : PlaneConfiguration B, 0 < windowWeight κ B s''',
 ['Top.ThreeFramesStatement','windowWeight','Finset.prod_pos'])
add('NodesCut','WindowRewrite','l:cut','sec5-window.tex:192–213','medium',
 'Choose fixed exterior and window assignments. Factor the removed partition ratio, absorb the exterior-only positive factors into the normalizer, and take w(s)=W_B(s)Z_G₁(s). Expand logs only of positive partition sums.',
 '''∀ κ : Plane → Fin 3, ∀ F B X G₁ G₂ : Finset Plane,
    SeparatingCut F B X G₁ G₂ →
    ∀ unit : ∀ j a, normSq (frameVector j a) = 1,
    (∀ G Y : Finset Plane, ∀ τ : PinAssignment G,
      0 < pinnedSum G Y τ (fun _ => 1) ∧ 0 < freeSum G Y (fun _ => 1)) →
    (∀ s : PlaneConfiguration B, 0 < windowWeight κ B s) →
    (∀ η : FrameBoundary F,
      planeMarginal κ F B η = normalize (fun s => windowWeight κ B s *
        pinnedSum (F \\ B) ∅ (cutPins κ (F \\ B) F B unit η s) (fun _ => 1))) →
    (∀ τ : PinAssignment (F \\ B),
      pinnedSum (F \\ B) X τ (fun _ => 1) =
        componentSum (F \\ B) G₁ τ * componentSum (F \\ B) G₂ τ) →
    (∀ η ξ : FrameBoundary F, ∀ s t : PlaneConfiguration B,
      componentSum (F \\ B) G₁ (cutPins κ (F \\ B) F B unit η s) =
        componentSum (F \\ B) G₁ (cutPins κ (F \\ B) F B unit ξ s) ∧
      componentSum (F \\ B) G₂ (cutPins κ (F \\ B) F B unit η s) =
        componentSum (F \\ B) G₂ (cutPins κ (F \\ B) F B unit η t)) →
    ∃ w : Weight (PlaneConfiguration B), (∀ s, 0 < w s) ∧
      ∀ η : FrameBoundary F, planeMarginal κ F B η = normalize (fun s =>
        w s * Real.exp (-cutError (F \\ B) X (cutPins κ (F \\ B) F B unit η s)))''',
 ['Real.exp_log','Real.log_div','normalize','componentSum','cutError'])
add('NodesCut','BoundedTilt','l:cut','sec5-window.tex:202–217','easy',
 'Normalize the positive base weight. The tilted normalizer is between exp(−E) and exp(E) times the base normalizer, which proves both comparisons and full support.',
 '''∀ (Ω : Type) [Fintype Ω] [Nonempty Ω],
    ∀ w : Weight Ω, (∀ s, 0 < w s) → ∀ E : ℝ, 0 ≤ E →
    PositiveProbability (normalize w) ∧
    ∀ e : Ω → ℝ, (∀ s, |e s| ≤ E) →
    PositiveProbability (normalize (fun s => w s * Real.exp (-e s))) ∧
    ∀ s, Real.exp (-2 * E) * normalize w s ≤
      normalize (fun s => w s * Real.exp (-e s)) s ∧
      normalize (fun s => w s * Real.exp (-e s)) s ≤ Real.exp (2 * E) * normalize w s''',
 ['normalize','PositiveProbability','Real.exp_le_exp','Finset.sum_pos'])
add('NodesCut','OverlapMinorization','l:cut','sec5-window.tex:219–228','easy',
 'Use |a−b|=a+b−2min(a,b), sum both probability laws, and lower-bound their overlap by p₀ times the common reference probability.',
 '''∀ Ω : Type, ∀ _ : Fintype Ω, ∀ p q ν : Weight Ω,
    Probability p → Probability q → Probability ν → ∀ p₀ : ℝ, 0 ≤ p₀ →
    (∀ s, p₀ * ν s ≤ p s) → (∀ s, p₀ * ν s ≤ q s) →
    totalVariation p q ≤ 1 - p₀''',
 ['totalVariation','Probability','min_le_min','abs_sub'])

# Tail threshold and the displayed constants.
add('NodesTail','TailExponential','t:cutMOS','sec5-window.tex:714–724','easy',
 'Write θ^(s/12−1) using exp(log θ·(s/12−1)), use (2u+1)²≤9u² and u=s⁴, then exp(r)≥r¹⁰/10! for r>0.',
 '''∀ θ : ℝ, 0 < θ → θ < 1 → ∀ u : ℕ, 1 ≤ u →
    tailCost θ u ≤ tailConstant θ * shellSpacing u ^ (-2 : ℤ)''',
 ['tailConstant','tailCost','Real.rpow_def_of_pos','Real.pow_div_factorial_le_exp'])
add('NodesTail','TailThreshold','t:cutMOS','sec5-window.tex:725–733','easy',
 'Take a natural ceiling dominating 390⁴, K², and one. Positivity of K and s then gives K/s²≤1 uniformly at all larger integer radii.',
 '''∀ θ : ℝ, 0 < θ → θ < 1 →
    (∀ u : ℕ, 1 ≤ u → tailCost θ u ≤ tailConstant θ * shellSpacing u ^ (-2 : ℤ)) →
    ∃ M : ℕ, 1 ≤ M ∧ geometryThreshold 64 ≤ M ∧
      ∀ u : ℕ, M ≤ u → tailCost θ u ≤ 1''',
 ['tailConstant','Nat.ceil_le','Real.sq_sqrt','geometryThreshold'])
add('NodesTail','CutCostNonnegative','t:cutMOS','sec5-window.tex:704–706,770–771','easy',
 'All displayed terms are nonnegative because A≥2, θ>0 and 1−θ>0.',
 '''∀ A θ : ℝ, 2 ≤ A → 0 < θ → θ < 1 → 0 ≤ cutCost A θ''',
 ['cutCost','zpow_pos','div_nonneg'],
 '''  intro A θ hA hθ hθ1
  have hA0 : 0 ≤ A := by linarith
  have hden : 0 ≤ 1 - θ := by linarith
  unfold cutCost
  positivity''')
add('NodesTail','WindowCostArithmetic','t:cutMOS','sec5-window.tex:746–755','easy',
 'Substitute the two cut-sum bounds and the tail≤1 estimate. Positive θ permits θ^(-3)θ⁻¹=θ^(-4); preserve the retained seed term 1+4A.',
 '''∀ A θ raw thick e tail : ℝ, 2 ≤ A → 0 < θ → θ < 1 →
    raw ≤ nearCost θ + tail → tail ≤ 1 → thick ≤ 5 * θ⁻¹ * raw →
    |e| ≤ 1 + 4 * A + 2 * A * θ ^ (-3 : ℤ) * thick → |e| ≤ cutCost A θ''',
 ['nearCost','cutCost','zpow_neg','zpow_add₀','mul_le_mul_of_nonneg_left'])

add('NodesCut','FrameWeightPositive','l:threeframes','sec5-window.tex:163–177','easy',
 'Every internal or exterior edge has differently coloured endpoints. Apply the positive lower bound from ThreeFramesStatement to every factor, then multiply.',
 '''AKLT.Blueprint.Top.ThreeFramesStatement →
    ∀ κ : Plane → Fin 3, ProperPlaneColouring κ → ∀ F : Finset Plane,
    ∀ η : FrameBoundary F, ∀ σ : PlaneConfiguration F, 0 < planeWeight κ F η σ''',
 ['Top.ThreeFramesStatement','planeWeight','ProperPlaneColouring','Finset.prod_pos'])

# Immediate scalar and linear algebra nodes, checked during blueprint construction.
immediate_proofs = {'LogLipschitz': "  have ordered : ∀ a b : ℝ, (1 / 2 : ℝ) ≤ a → (1 / 2 : ℝ) ≤ b → b ≤ a →\n      |Real.log a - Real.log b| ≤ 2 * |a - b| := by\n    intro a b ha hb hba\n    have ha0 : 0 < a := by linarith\n    have hb0 : 0 < b := by linarith\n    have hlog : Real.log a - Real.log b ≤ (a - b) / b := by\n      rw [← Real.log_div ha0.ne' hb0.ne']\n      convert Real.log_le_sub_one_of_pos (div_pos ha0 hb0) using 1\n      field_simp\n    have hdiv : (a - b) / b ≤ 2 * (a - b) := by\n      apply (div_le_iff₀ hb0).mpr\n      nlinarith\n    simpa only [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb0 hba)),\n      abs_of_nonneg (sub_nonneg.mpr hba)] using hlog.trans hdiv\n  intro a b ha hb\n  rcases le_total b a with h | h\n  · exact ordered a b ha hb h\n  · simpa only [abs_sub_comm] using ordered b a hb ha h", 'WindowCostArithmetic': '  intro A θ raw thick e tail hA hθ hθ1 hr ht hth he\n  have hA0 : 0 ≤ A := by linarith\n  have hcoef : 0 ≤ 2 * A * θ ^ (-3 : ℤ) := by positivity\n  have hmul : θ ^ (-3 : ℤ) * θ⁻¹ = θ ^ (-4 : ℤ) := by\n    rw [zpow_neg, zpow_neg]\n    simp only [zpow_ofNat, ← mul_inv_rev]\n    congr 1\n    ring\n  have hu : |e| ≤ 1 + 4 * A + 2 * A * θ ^ (-3 : ℤ) *\n      (5 * θ⁻¹ * (nearCost θ + 1)) := by\n    apply he.trans\n    gcongr\n    exact hth.trans (mul_le_mul_of_nonneg_left (hr.trans (by linarith)) (by positivity))\n  calc\n    |e| ≤ 1 + 4 * A + 2 * A * θ ^ (-3 : ℤ) *\n        (5 * θ⁻¹ * (nearCost θ + 1)) := hu\n    _ = 1 + 4 * A + 10 * A * (θ ^ (-3 : ℤ) * θ⁻¹) * (nearCost θ + 1) := by ring\n    _ = cutCost A θ := by rw [hmul]; rfl', 'SpanCutParity': '  intro E h c hc\n  induction hc using Submodule.span_induction with\n  | mem z hz =>\n    obtain ⟨x,y,z,ht,rfl⟩ := hz\n    exact h x y z ht\n  | zero => simp [cutParity]\n  | add x y hx hy hpx hpy => simpa [cutParity, Finset.sum_add_distrib] using congrArg₂ (· + ·) hpx hpy\n  | smul a x hx hpx =>\n    simpa [cutParity, Finset.mul_sum] using congrArg (a * ·) hpx'}
assert set(immediate_proofs) <= RETAINED_LEAF_PROOFS
for e in entries:
    stem=e['lean_name'].split('.')[-1].removesuffix('Statement')
    if stem in immediate_proofs:
        e['status']='proved'
        module=e['module'].split('.')[-1]
        theorem=stem[0].lower()+stem[1:]
        for j,body in enumerate(files[module]):
            if 'def '+stem+'Statement : Prop' in body:
                files[module][j]=body+'\ntheorem '+theorem+' : '+stem+'Statement := by\n'+immediate_proofs[stem]+'\n\n#print axioms '+theorem+'\n'
                break

header='''import AKLT.Blueprint.Win.Defs

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Win

'''
for module,body in files.items():
    (root/(module+'.lean')).write_text(header+'\n'.join(body)+'\nend AKLT.Blueprint.Win\n')
(report/'nodes_inventory.json').write_text(json.dumps(entries,indent=2,ensure_ascii=False)+'\n')
print(f'Generated {len(entries)} nodes in {len(files)} modules; {sum(e["status"]=="open" for e in entries)} open.')
