module
public import AKLT.Blueprint.Win.Leaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Proved conditional assemblies for §5 and Appendix B. All global inputs
are closed Props. WindowLeaves is an explicit conjunction of open obligations;
no proof of an open leaf is asserted here. -/

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Win

private theorem joined_mono {α : Type*} {R T : α → α → Prop} {S U : Set α}
    (hS : S ⊆ U) (hR : ∀ x y, R x y → T x y) {x y : α}
    (h : JoinedIn R S x y) : JoinedIn T U x y := by
  apply Relation.ReflTransGen.mono (r := fun v w => v ∈ S ∧ w ∈ S ∧ R v w)
    (p := fun v w => v ∈ U ∧ w ∈ U ∧ T v w)
    (fun _ _ h => ⟨hS h.1, hS h.2.1, hR _ _ h.2.2⟩)
  exact h

private theorem joined_symm {α : Type*} {R : α → α → Prop} {S : Set α}
    (hR : ∀ x y, R x y → R y x) {x y : α}
    (h : JoinedIn R S x y) : JoinedIn R S y x := by
  apply Relation.ReflTransGen.mono (r := Function.swap (fun v w => v ∈ S ∧ w ∈ S ∧ R v w))
    (fun v w h => ⟨h.2.1, h.1, hR _ _ h.2.2⟩)
  exact Relation.ReflTransGen.swap _ _ h

private theorem connected_relation {α : Type*} {R T : α → α → Prop} {S : Set α}
    (hR : ∀ x y, R x y → T x y) (h : ConnectedIn R S) : ConnectedIn T S :=
  ⟨h.1, fun _ hx _ hy => joined_mono (fun _ h => h) hR (h.2 _ hx _ hy)⟩

private theorem connected_via {α : Type*} {R : α → α → Prop} {S K : Set α}
    (hR : ∀ x y, R x y → R y x) (hK : ConnectedIn R K) (hKS : K ⊆ S)
    (h : ∀ x ∈ S, ∃ y ∈ K, JoinedIn R S x y) : ConnectedIn R S := by
  refine ⟨hK.1.mono hKS, ?_⟩
  intro x hx y hy
  obtain ⟨v, hv, hxv⟩ := h x hx
  obtain ⟨w, hw, hyw⟩ := h y hy
  exact hxv.trans ((joined_mono hKS (fun _ _ h => h) (hK.2 v hv w hw)).trans
    (joined_symm hR hyw))

private theorem subset_thicken (X₀ : Finset Plane) : X₀ ⊆ thicken X₀ := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_insert_self _ _⟩

private theorem decay_nonnegative (θ : ℝ) (hθ : 0 ≤ θ) (r : ℕ∞) : 0 ≤ decay θ r := by
  unfold decay
  split_ifs
  · exact le_rfl
  · exact pow_nonneg hθ _

/-- `l:shellgeom`, sec5-window.tex:27–123. Compose the ten independent
geometric nodes; no response or frame property is used. -/
theorem shellGeometry_of_leaves : ShellLeaves → AKLT.Blueprint.Top.ShellGeometryStatement := by
  intro h l hl a y u hu hy
  have hs := h.shellScale l u hl hu
  have setup : ShellSetup l a y u := ⟨hl, hu, hy⟩
  have s2 : 2 ≤ shellSpacing u := le_trans (by norm_num) hs.1
  refine ⟨h.exceptionalCount a y u (h.closeCorner a y u hy)
    (h.exceptionalLocalization a y u hs.2.2.2.1) (h.radiusGap u hs.1), ?_, ?_, ?_⟩
  · intro i hi _
    exact h.shellInclusion a y u s2 i hi
  · intro i hi hi₁ hnon
    have hc : ParallelClearance a y u i := by
      by_contra hn
      exact hnon (h.sideCornerWitness l a y u setup i hi hi₁ hn)
    exact ⟨h.nearShellCount l a y u setup i hi hi₁ hc, hc⟩
  · intro i hi
    exact ⟨h.predecessorShell a y u i hi, h.seedSeparation a y u s2 i hi⟩

/-- Appendix B, app-topology.tex:28–86. Fill an even star-edge chain with
triangles by eliminating diagonals and reconstructing the remaining plaquettes. -/
theorem evenChain_of_leaves (h : TopologyLeaves) :
    ∀ c : EdgeChain, ChainStar c → ChainEven c → c ∈ triangleSpan := by
  intro c hc he
  obtain ⟨d, hd, hde, hcd⟩ := h.diagonalElimination c hc he
  obtain ⟨R, hR, hbox⟩ := h.chainBox d
  have hf := h.columnFlux d hd hde R hR hbox
  obtain ⟨P, hP⟩ := h.tailSupport d R hR hbox hf
  have hrepr := h.plaquetteReconstruction d hd hde R hR hbox hf P hP
  have hdin : d ∈ triangleSpan := by
    rw [hrepr]
    exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (h.plaquetteTriangles p)
  simpa only [sub_add_cancel] using Submodule.add_mem triangleSpan hcd hdin

/-- `l:boundaryconn`, app-topology.tex:88–135. A disconnected crossing-edge
component would give both zero and one as the parity of a two-crossing cycle. -/
theorem boundaryConnectivity_of_leaves (h : TopologyLeaves) :
    ∀ A : Finset Plane, ConnectedIn StarAdjacent (↑A) →
    ConnectedIn StarAdjacent {z | z ∉ A} →
    ConnectedIn StarAdjacent (↑(rawBoundary A)) ∧
    ∀ z : Plane, z ∈ rawBoundary A ↔ z ∉ A ∧
      setDistance supDist z (↑A : Set Plane) = 1 := by
  classical
  intro A hA hAc
  have hnon : A.Nonempty := hA.1
  have hlinks : ∀ e ∈ cutEdges A, ∀ f ∈ cutEdges A,
      JoinedIn Linked (↑(cutEdges A) : Set LatticeEdge) e f := by
    by_contra hn
    obtain ⟨E, hE, e, he, f, hf, hnf⟩ := h.linkedSeparation A hn
    have hef : e ≠ f := fun hh => hnf (hh ▸ he)
    obtain ⟨c, hc, hce, hcross⟩ := h.twoCrossingCycle A hA hAc e (hE.1 he) f hf hef
    have hz := spanCutParity E (h.triangleCutParity A E hE) c
      (evenChain_of_leaves h c hc hce)
    have ho := h.twoCrossingParity A E hE.1 e he f hf hnf c hcross
    exact zero_ne_one (hz.symm.trans ho)
  exact ⟨h.outerEndpointTransfer A (h.cutEdgesNonempty A hnon) hlinks,
    h.boundaryMembership A⟩

/-- `l:thicken`, app-topology.tex:138–182. Chains of intersecting crosses
give nearest-neighbor connectivity; overcounting gives the exact factor 5/θ. -/
theorem thickening_of_leaves (h : TopologyLeaves) :
    ∀ X₀ : Finset Plane, ConnectedIn StarAdjacent (↑X₀) →
    ConnectedIn Adjacent (↑(thicken X₀)) ∧
    ∀ G : Finset Plane, ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∑ z ∈ thicken X₀, decay θ (boundaryDepth G z) ≤
        5 * θ⁻¹ * ∑ x ∈ X₀, decay θ (boundaryDepth G x) := by
  intro X₀ hX
  refine ⟨h.crossUnion X₀ hX (fun x => (h.crossFacts x).2.2) h.crossOverlap, ?_⟩
  intro G θ hθ hθ1
  exact h.crossWeightSum X₀ (fun z => decay θ (boundaryDepth G z))
    (fun z => decay_nonnegative θ hθ.le _) θ⁻¹ (inv_nonneg.mpr hθ.le)
    (fun x => (h.crossFacts x).1)
    (fun x _ z hz => h.neighbourDecay G θ hθ hθ1 x z ((h.crossFacts x).2.1 z |>.mp hz))

/-- `l:cutgeom`, sec5-window.tex:441–512. Assemble radial paths, the inner
shell core, and escape paths to the connected exterior square. -/
theorem taperConnectivity_of_leaves (h : WindowLeaves) :
    ∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i →
    ConnectedIn StarAdjacent (↑(taper a y u i)) ∧
    ConnectedIn StarAdjacent {z | z ∉ taper a y u i} := by
  intro a y u i hs
  have hcore := h.taper.coreConnected a y u i hs
  have hU : ConnectedIn StarAdjacent (↑(taper a y u i)) :=
    connected_via metricFacts.2.2.2
      (connected_relation metricFacts.2.1 hcore.1) hcore.2
      (h.taper.radialPaths a y u i hs)
  have hsubset : taper a y u i ⊆ square a u := Finset.filter_subset _ _
  have hcomp : ConnectedIn Adjacent {z | z ∉ taper a y u i} :=
    connected_via metricFacts.2.2.1 (h.taper.squareExterior a u)
      (fun _ hz hmem => hz (hsubset hmem)) (h.taper.complementEscape a y u i hs)
  exact ⟨hU, connected_relation metricFacts.2.1 hcomp⟩

/-- The local conclusion of l:cutgeom and l:Xconn. All distances refer to
the original cutVolume; this record is a conclusion, not an open leaf. -/
structure CutGeometryResult (a y : Plane) (u : ℕ) (i : ℤ) : Prop where
  separation : SeparatingCut (farVolume a y u i) (window a y u 64 i)
    (cutSet a y u i) (insidePiece a y u i) (outsidePiece a y u i)
  connected : ConnectedIn Adjacent (↑(cutSet a y u i))
  deep : ∀ z ∈ cutSet a y u i, 13 ≤ boundaryDepth (cutVolume a y u i) z
  rawMass : ∀ θ : ℝ, 0 < θ → θ < 1 →
    ∑ x ∈ cutRaw a y u i, decay θ (boundaryDepth (cutVolume a y u i) x) ≤
      nearCost θ + tailCost θ u
  thickMass : ∀ θ : ℝ, 0 < θ → θ < 1 →
    ∑ z ∈ cutSet a y u i, decay θ (boundaryDepth (cutVolume a y u i) z) ≤
      5 * θ⁻¹ * ∑ x ∈ cutRaw a y u i, decay θ (boundaryDepth (cutVolume a y u i) x)

/-- `l:cutgeom` and `l:Xconn`, sec5-window.tex:382–691. Compose depth,
layer counts, signed-side exclusion, boundary topology, and thickening. -/
theorem cutGeometry_of_leaves (h : WindowLeaves) :
    ∀ a y : Plane, ∀ u : ℕ, ∀ i : ℤ, CutSetup a y u i → CutGeometryResult a y u i := by
  classical
  intro a y u i hs
  have hbuf := h.taper.windowBuffer a y u i hs
  have hc := taperConnectivity_of_leaves h a y u i hs
  have hb := boundaryConnectivity_of_leaves h.topology (taper a y u i) hc.1 hc.2
  have ht := thickening_of_leaves h.topology (cutRaw a y u i) hb.1
  have hscale := h.taper.cutScales a y u i hs
  have hraw : ∀ x ∈ cutRaw a y u i,
      14 ≤ ((boundaryDepth (cutVolume a y u i) x).toNat : ℝ) ∧
      ((radialOffset y u i x : ℝ) ≤ shellSpacing u / 12 →
        max (radialOffset y u i x : ℝ) 16 - 2 ≤
          ((boundaryDepth (cutVolume a y u i) x).toNat : ℝ)) ∧
      (shellSpacing u / 12 < (radialOffset y u i x : ℝ) →
        shellSpacing u / 12 - 1 ≤ ((boundaryDepth (cutVolume a y u i) x).toNat : ℝ)) := by
    intro x hx
    have hr := h.taper.rawRange a y u i hs x hx
    apply h.taper.rawDepthArithmetic (shellSpacing u) (radialOffset y u i x : ℝ)
      (squareDepth a u x : ℝ) ((boundaryDepth (cutVolume a y u i) x).toNat : ℝ)
      hscale.1 (Nat.cast_nonneg _) hr.1
    · intro hn
      exact ⟨by exact_mod_cast (hr.2 hn).1, by exact_mod_cast (hr.2 hn).2⟩
    · exact_mod_cast h.taper.rawHeight a y u i hs x hx
    · exact h.taper.rawDistanceObstructions a y u i hs x hx
  have hdeep : ∀ x ∈ cutRaw a y u i, 14 ≤ boundaryDepth (cutVolume a y u i) x := by
    intro x hx
    have hn : 14 ≤ (boundaryDepth (cutVolume a y u i) x).toNat := by
      exact_mod_cast (hraw x hx).1
    rw [← (h.topology.finiteDepth _ x).2.1]
    exact_mod_cast hn
  have hthick := h.taper.thickDepth (cutVolume a y u i) (cutRaw a y u i) hdeep
  have hi₁ : i ≤ lastShellIndex u := by
    unfold lastShellIndex
    have hi := Int.lt_floor_add_one (shellSpacing u)
    exact_mod_cast (lt_of_le_of_lt hs.2.2.1 hi).le
  have hgeom := shellGeometry_of_leaves h.shell 64 (by norm_num) a y u hs.1.2.1 hs.1.2.2
  have hclear := (hgeom.2.2.1 i hs.2.1 hi₁ hs.2.2.2).2
  have hnc := h.taper.signedSideExclusion a y u i hs hclear
  have hlayers := h.taper.rawLayerCount a y u i hs hnc
    (fun x hx hn => (h.taper.rawRange a y u i hs x hx).2 hn) h.taper.squareIntersection
  refine ⟨?_, ht.1, hthick.2, ?_, ht.2 (cutVolume a y u i)⟩
  · exact h.taper.cutSeparation (farVolume a y u i) (window a y u 64 i)
      (taper a y u i) (cutSet a y u i) hbuf.1 hbuf.2.1 hbuf.2.2.1
      hbuf.2.2.2.1 (subset_thicken _) hthick.1
  · intro θ hθ hθ1
    have hser := h.taper.nearSeries θ hθ hθ1
    apply h.taper.rawWeightSum a y u i hs
      (fun x hx => (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hbuf.2.2.2.2 hx)).1).1)
      (fun x hx => ⟨?_, (hraw x hx).2.2⟩) hlayers θ hθ hθ1 hser.1 hser.2
    intro hn
    have hh := (hraw x hx).2.1 hn
    have hm : 2 ≤ max (radialOffset y u i x) 16 := by omega
    have he : ((max (radialOffset y u i x) 16 - 2 : ℕ) : ℝ) =
        max (radialOffset y u i x : ℝ) 16 - 2 := by
      rw [Nat.cast_sub hm, Nat.cast_max]
      norm_num
    rw [← he] at hh
    exact_mod_cast hh

/-- `l:removal`, sec5-window.tex:233–356, and e:windowcutcost's first
enlargement. The seed keeps its quartic cost and all later sites have ≤3 bonds. -/
theorem removalEstimate_of_leaves (h : RemovalLeaves)
    (hMom : AKLT.Blueprint.Top.MomentsStatement)
    (hFacts : AKLT.Blueprint.Top.FiniteFactsStatement)
    (hMean : AKLT.Blueprint.Top.ThreeFactorMeanStatement) :
    ∀ A θ : ℝ, ResponseProperty A θ → ∀ G X : Finset Plane,
    X ⊆ G → (∀ x ∈ X, 3 ≤ boundaryDepth G x) →
    ∀ _e : RemovalEnumeration X, ∀ τ : PinAssignment G,
    |cutError G X τ| ≤ 1 + 4 * A +
      2 * A * θ ^ (-3 : ℤ) * ∑ z ∈ X, decay θ (boundaryDepth G z) := by
  classical
  intro A θ hP G X hX hdepth e τ
  have hpos := h.originalPositivity hFacts
  have hp : ∀ Y : Finset Plane, ∀ p : Bool, 0 < partSum p G Y τ (fun _ => 1) := by
    intro Y p
    cases p <;> simp only [partSum, Bool.false_eq_true, ↓reduceIte]
    · exact (hpos G Y τ).2
    · exact (hpos G Y τ).1
  have he := h.enumerationSteps G X hX hdepth e
  have hlocal : ∀ j : Fin (e.last + 1),
      |logRatio G (removedPrefix e j.val) τ - logRatio G (removedPrefix e (j.val + 1)) τ| ≤
      if j.val = 0 then 1 + 4 * A * θ ^ depthShift G (e.site j)
      else 2 * A * θ ^ depthShift G (e.site j) := by
    intro j
    let Y := removedPrefix e j.val
    let x := e.site j
    let V := survivors G Y x
    have hstep : RemovalStep G Y x := (he.2.2 j).2.1
    have hsurv := h.survivorGeometry G Y x hstep
    have hbridge := fun p => h.partLawBridge hMom G (insert x Y) τ p (hp _ p)
    have hq := fun p => h.quarticMeanBound hMom (G \ insert x Y) _ (hbridge p).1 x
    have hpair := fun p => h.pairMeanAveraging (G \ insert x Y) V
      (fun z hz => (Finset.mem_inter.mp hz).2) _ (hbridge p).1
      (h.neighbourFibres hMom hMean G Y τ x hstep p)
    have hlo : ∀ p : Bool, (1 / 2 : ℝ) ≤ partMean p G (insert x Y) τ (removalPolynomial x V) := by
      intro p
      rw [(hbridge p).2]
      have hh := h.polynomialLower (G \ insert x Y) V _ (hbridge p).1 x hsurv.1
        (hpair p) (hq p)
      split_ifs at hh <;> linarith
    have hqb : ∀ p : Bool, |partMean p G (insert x Y) τ (quartic x)| ≤ 3 := by
      intro p
      rw [(hbridge p).2]
      exact hq p
    have hd : 0 ≤ A * θ ^ depthShift G x := by
      exact mul_nonneg (by linarith [hP.1]) (pow_nonneg hP.2.1.le _)
    have hdiff := h.pairDifference G (insert x Y) τ x V hsurv.1
      (A * θ ^ depthShift G x) hd
      (h.removedPairResponse A θ hP G Y τ x hstep)
    have hcost := h.localLogEstimate logLipschitz G (insert x Y) τ x V hsurv.1
      (A * θ ^ depthShift G x) hd (fun p => ⟨hp _ p, hlo p, hqb p⟩) hdiff
    have hident := h.logStepIdentity G Y τ x
      (fun p => ⟨hp _ p, hp _ p⟩) (h.removalIntegral hMom G Y τ x hstep)
    rw [(he.2.2 j).1]
    change |logRatio G Y τ - logRatio G (insert x Y) τ| ≤ _
    rw [hident]
    by_cases hj : j.val = 0
    · have hY : Y = ∅ := by simpa only [Y, hj] using he.1
      have hk : V.card = 4 := hsurv.2.1 hY
      simp only [hk, ↓reduceIte] at hcost
      simp only [hj, ↓reduceIte]
      convert hcost using 1
      ring
    · have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj
      have hk : V.card ≠ 4 := by
        have hh := hsurv.2.2.1 ((he.2.2 j).2.2 hjpos)
        change V.card ≤ 3 at hh
        omega
      simp only [hk, ↓reduceIte] at hcost
      simp only [hj, ↓reduceIte]
      convert hcost using 1
      ring
  exact h.removalCostSum G X τ e hdepth A θ (by linarith [hP.1]) hP.2.1 hP.2.2.1
    (h.removalTelescope G X τ e he.1 he.2.1 A θ hlocal)

/-- `l:cut`, sec5-window.tex:128–229. The base law keeps the actual
window weights, while quadrature is applied only to the complementary sum. -/
theorem cutMinorization_of_leaves (h : WindowLeaves)
    (hFacts : AKLT.Blueprint.Top.FiniteFactsStatement)
    (hFrames : AKLT.Blueprint.Top.ThreeFramesStatement)
    (hExact : AKLT.Blueprint.Top.ExactStatement) :
    ∀ κ : Plane → Fin 3, ProperPlaneColouring κ →
    ∀ F B X G₁ G₂ : Finset Plane, SeparatingCut F B X G₁ G₂ →
    ∀ E : ℝ, 0 ≤ E →
    (∀ τ : PinAssignment (F \ B), |cutError (F \ B) X τ| ≤ E) →
    ∃ ν : Weight (PlaneConfiguration B), PositiveProbability ν ∧
      (∀ η : FrameBoundary F, PositiveProbability (planeMarginal κ F B η) ∧
        ∀ s, Real.exp (-2 * E) * ν s ≤ planeMarginal κ F B η s ∧
          planeMarginal κ F B η s ≤ Real.exp (2 * E) * ν s) ∧
      ∀ η ξ : FrameBoundary F,
        totalVariation (planeMarginal κ F B η) (planeMarginal κ F B ξ) ≤ 1 - Real.exp (-2 * E) := by
  classical
  intro κ hκ F B X G₁ G₂ hsep E hE herr
  let unit : ∀ j a, normSq (frameVector j a) = 1 :=
    fun j => (hFrames.2.2.2.2.2.2.1 j).2.1
  have hnormal : ∀ η : FrameBoundary F,
      planeMarginal κ F B η = normalize (fun s => windowWeight κ B s *
        pinnedSum (F \ B) ∅ (cutPins κ (F \ B) F B unit η s) (fun _ => 1)) := by
    intro η
    have hz : 0 < ∑ σ : PlaneConfiguration F, planeWeight κ F η σ :=
      Finset.sum_pos (fun σ _ => h.cut.frameWeightPositive hFrames κ hκ F η σ)
        Finset.univ_nonempty
    rw [h.cut.marginalNormalization κ F B hsep.1 η hz]
    congr 1
    funext s
    rw [h.cut.frameFibreSum hFrames κ hκ F B hsep.1 hsep.2.1 unit η s,
      h.cut.complementQuadrature hFrames hExact]
  obtain ⟨w, hw, hrewrite⟩ := h.cut.windowRewrite κ F B X G₁ G₂ hsep unit
    (h.removal.originalPositivity hFacts) (h.cut.windowWeightPositive hFrames κ hκ B)
    hnormal (fun τ => (h.cut.originalFactorization F B X G₁ G₂ hsep τ).1)
    (h.cut.componentPins κ F B X G₁ G₂ hsep unit)
  have htilt := h.cut.boundedTilt (PlaneConfiguration B) w hw E hE
  have hν := htilt.1
  have hcompare : ∀ η : FrameBoundary F, PositiveProbability (planeMarginal κ F B η) ∧
      ∀ s, Real.exp (-2 * E) * normalize w s ≤ planeMarginal κ F B η s ∧
        planeMarginal κ F B η s ≤ Real.exp (2 * E) * normalize w s := by
    intro η
    rw [hrewrite η]
    exact htilt.2 _ (fun s => herr _)
  refine ⟨normalize w, hν, hcompare, ?_⟩
  intro η ξ
  exact h.cut.overlapMinorization (PlaneConfiguration B) inferInstance _ _ _
    ⟨fun s => ((hcompare η).1.1 s).le, (hcompare η).1.2⟩
    ⟨fun s => ((hcompare ξ).1.1 s).le, (hcompare ξ).1.2⟩
    ⟨fun s => (hν.1 s).le, hν.2⟩ _ (Real.exp_pos _).le
    (fun s => ((hcompare η).2 s).1) (fun s => ((hcompare ξ).2 s).1)

/-- `t:cutMOS`, sec5-window.tex:696–781. This is the requested Top export,
with l₀=64 and exactly cutProbability. Every input is a closed Prop. -/
theorem cutMOS_of_leaves : WindowLeaves →
    AKLT.Blueprint.Top.MomentsStatement → AKLT.Blueprint.Top.FiniteFactsStatement →
    AKLT.Blueprint.Top.ThreeFactorMeanStatement → AKLT.Blueprint.Top.ThreeFramesStatement →
    AKLT.Blueprint.Top.ExactStatement → AKLT.Blueprint.Top.CutMOSStatement := by
  intro h hMom hFacts hMean hFrames hExact A θ hP
  have hE := cutCostNonnegative A θ hP.1 hP.2.1 hP.2.2.1
  obtain ⟨M, hM, hMg, htail⟩ := h.tail.tailThreshold θ hP.2.1 hP.2.2.1
    (h.tail.tailExponential θ hP.2.1 hP.2.2.1)
  refine ⟨M, by norm_num, hM, Real.exp_pos _, ?_, ?_⟩
  · apply Real.exp_le_one_iff.mpr
    linarith
  · intro κ hκ a u hu y hy i hi his hnon η ξ
    have hs : CutSetup a y u i := ⟨⟨by norm_num, le_trans hMg hu, hy⟩, hi, his, hnon⟩
    have hg := cutGeometry_of_leaves h a y u i hs
    obtain ⟨e⟩ := h.topology.connectedEnumeration (cutSet a y u i) hg.connected
    have herr : ∀ τ : PinAssignment (cutVolume a y u i),
        |cutError (cutVolume a y u i) (cutSet a y u i) τ| ≤ cutCost A θ := by
      intro τ
      have hrem := removalEstimate_of_leaves h.removal hMom hFacts hMean A θ hP
        (cutVolume a y u i) (cutSet a y u i) hg.separation.2.2.1
        (fun z hz => le_trans (by norm_num) (hg.deep z hz)) e τ
      exact windowCostArithmetic A θ _ _ _ _ hP.1 hP.2.1 hP.2.2.1
        (hg.rawMass θ hP.2.1 hP.2.2.1) (htail u hu)
        (hg.thickMass θ hP.2.1 hP.2.2.1) hrem
    obtain ⟨ν, hν, hminor, htv⟩ := cutMinorization_of_leaves h hFacts hFrames hExact
      κ hκ (farVolume a y u i) (window a y u 64 i) (cutSet a y u i)
      (insidePiece a y u i) (outsidePiece a y u i) hg.separation (cutCost A θ) hE herr
    exact htv η ξ

#print axioms shellGeometry_of_leaves
#print axioms evenChain_of_leaves
#print axioms boundaryConnectivity_of_leaves
#print axioms thickening_of_leaves
#print axioms taperConnectivity_of_leaves
#print axioms cutGeometry_of_leaves
#print axioms removalEstimate_of_leaves
#print axioms cutMinorization_of_leaves
#print axioms cutMOS_of_leaves

end AKLT.Blueprint.Win
