STATUS: COMPLETE

All eight leaves are **TRUE** as written and self-sufficient for the paper’s argument. No corrected statements or additional premises are required. The difficulty ratings describe expected Lean work. All full names have the prefix `AKLT.Blueprint.Gap.`.

| Leaf | Module / source | Paper label | Verdict | Difficulty | Reason |
|---|---|---|---|---|---|
| `FrameSpecEnergyStatement` | [NodesPeriodic.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesPeriodic.lean:155) | `l:planeenergy` | **TRUE** | easy | Assignment bound transfers along the site inclusion. |
| `FrameWindowTransferStatement` | [NodesPeriodic.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesPeriodic.lean:166) | `d:W` | **TRUE** | medium | The allowed indices imply Bᵢ ⊆ Fᵢ. |
| `ShellNestingStatement` | [NodesShell.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesShell.lean:14) | `l:stopped` | **TRUE** | easy | Positive spacing and the floor bound give both containments. |
| `FiniteEnergyChainStatement` | [NodesShell.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesShell.lean:22) | `l:stopped` | **TRUE** | medium | Positive partial fibres and the finite chain rule suffice. |
| `ShellRowStatement` | [NodesShell.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesShell.lean:33) | `l:stopped` | **TRUE** | hard | All geometric, energy, consistency and window inputs are present. |
| `TraceMarginalsStatement` | [NodesShell.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesShell.lean:44) | `l:surgery` | **TRUE** | medium | Stochastic conditional resampling preserves both marginals. |
| `TrialCountStatement` | [NodesShell.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesShell.lean:54) | `l:stopped` | **TRUE** | easy | One exceptional integer removes at most two of h−1 candidates. |
| `ShellAbsorptionStatement` | [NodesShell.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesShell.lean:61) | `l:stopped` | **TRUE** | medium | A successful trial and its successor force persistent agreement. |

The source checkout is `main` at `7a3393531c12080d76aefbdab300ac0c2df834b7`. This assessment uses each leaf’s quantified hypotheses and the definitions below; it does not assume that any other named blueprint leaf has been proved. No proofs were written, no sub-agents were launched, and the repository was not modified.

For the shell discussion, write C=`square a u`, s=`shellSpacing u`, Fᵢ=`farVolume a y u i`, Dᵢ=`shell a y u i`, Aᵢ=`nearShell a y u l i`, and Bᵢ=`window a y u l i`. The physical surgery index of row j is i=j.val+2.

**1. `AKLT.Blueprint.Gap.FrameSpecEnergyStatement` — TRUE; easy.**

This is a reindexing of the supplied assignment bound. Every finite set of sites of the subtype W embeds injectively into Plane, preserving disjointness and cardinality. Total extensions of the two subtype configurations turn its events into exactly those in AssignmentBound for (frameSpec κ).law W η. No positivity or proper-colouring premise is needed for this implication.

**Two-line proof route:**

Map U,J : Finset W into Plane by Subtype.val and extend a,b : W → IcoLetter by the default letter off W.  
Apply the supplied bound with the restricted boundary η; rewrite the two events and the image cardinality.

**Lean traps:** The U,J in AssignmentBound are finsets of the subtype W, whereas the premise uses finsets of Plane. Use the injective Subtype.val map, including its cardinality identity. The exponent counts U, the prescribed sites; J is the conditioning set. Off-volume default letters do not enter either event. A proper-colouring hypothesis is unnecessary because the needed bound is already a premise.

**2. `AKLT.Blueprint.Gap.FrameWindowTransferStatement` — TRUE; medium.**

WindowProperty has exactly the parameter bounds and colouring/translate/index quantifiers required by SpecWindow. Its indices satisfy 2 ≤ i ≤ s, hence s ≥ 2 and floor(i*s) > (i-1)*s, so B_i ⊆ D_i ⊆ F_i. On B_i the fill-based specMarginal agrees with the extendLetters-based planeMarginal after restricting each total boundary to exteriorSites F_i. The containment follows from these local inequalities without a geometry-threshold premise.

**Two-line proof route:**

Copy the four parameter inequalities; for each allowed index derive window ⊆ shell ⊆ farVolume from 2 ≤ i ≤ shellSpacing u.  
Restrict η,ξ to FrameBoundary F_i, identify both marginal maps on B_i, and specialize WindowProperty to κ.

**Lean traps:** specMarginal fills off-volume sites from η, while planeMarginal uses the fixed default (0,0,0) there. Their equality requires Bᵢ ⊆ Fᵢ; it is derivable from 2 ≤ i ≤ s and is not definitional. FrameBoundary Fᵢ is indexed by the finite exteriorSites Fᵢ, so each total boundary must be restricted to that subtype. The floor and inequalities are in ℤ/ℝ, not ℕ.

**3. `AKLT.Blueprint.Gap.ShellNestingStatement` — TRUE; easy.**

Writing s = shellSpacing u, s ≥ 16 is positive and i+2 ≤ j gives (j-1)*s ≥ (i+1)*s > i*s. Thus F_j ⊆ F_(i+1). Also floor((j-1)*s) > (j-1)*s-1 ≥ (i+1)*s-1 > i*s, so D_(j-1) ⊆ F_(i+1). All indices are integers; the argument also covers negative indices and empty shells.

**Two-line proof route:**

Unfold farVolume and shell membership and retain membership in the common square.  
Compare the real thresholds using i+2 ≤ j and s ≥ 16; for the shell use the strict floor lower bound x-1 < floor x.

**Lean traps:** The shell indices are arbitrary integers. Keep shellRadius as Int.floor, and cast integer addition/subtraction before comparing real thresholds. The distance is the natural-valued maximum of coordinate natAbs values, then cast to ℝ or ℤ. No exterior-site or nonempty-shell hypothesis is needed for these two containments.

**4. `AKLT.Blueprint.Gap.FiniteEnergyChainStatement` — TRUE; medium.**

Nonempty alphabets and compatible prescriptions make each partial assignment event nonempty; strict positivity gives it positive mass. A conditional one-site probability given only J is a convex average of the full one-site fibre probabilities and hence is at least α. Applying this successively to the distinct prescribed sites U gives α^U.card. The explicit finite, nonempty dependent alphabets suffice, including empty site sets and singleton alphabets.

**Two-line proof route:**

Group the finite sums by complete assignments off x to express each partially conditioned one-site probability as a positive weighted average of full fibres.  
Induct over U, adjoining its prescribed letters to J; multiply the bounds, with the empty assignment giving probability one.

**Lean traps:** The first event argument of conditionalProbability is the conditioning event. A nonempty event has positive mass here because p is strictly positive, not merely nonnegative. The elaborated statement retains [Fintype ι], [DecidableEq ι], [∀ x, Fintype (S x)] and [∀ x, Nonempty (S x)]; no alphabet instance was dropped. For U=∅ the denominator is positive and both the conditional probability and α^0 are one.

**5. `AKLT.Blueprint.Gap.ShellRowStatement` — TRUE; hard.**

RegularSpec supplies positivity, consistency and range one; SpecEnergy supplies all conditional assignment bounds; SpecWindow supplies valid p and the B_i bound; ShellGeometry supplies the separator and |A_i| ≤ 8*l. For i=j.val+2, h ≤ s gives i ≤ h+1 ≤ floor(s)+1. If the predecessor shell agrees, range one makes the F_i laws equal. Otherwise maximal B_i coupling, conditional completion and independent conditional A_i resampling give success at least p*α^(2*|A_i|) ≥ p*α^(16*l) when i ≤ h. No success bound is required for i=h+1; skipped rows are point masses.

**Two-line proof route:**

At a skipped index take the identity row; otherwise identify the two full fibres with specification laws on F_i, and use identical resampling when D_(i-1) agrees.  
For the other branch couple B_i maximally, complete conditionally and resample A_i independently; lift back to the square with fixed complements and bound agreement using |A_i| ≤ 8*l.

**Lean traps:** A row j : Fin h has physical surgery index i=j.val+2, so the rows are 2,…,h+1. Geometry is needed through h+1, but the success guard i ≤ h deliberately excludes the last row. In the identical branch, agreement on the predecessor shell and the two separator clauses of ShellGeometry give equality of the induced Fᵢ laws by range one. In the other branch, resampling Aᵢ preserves Bᵢ because nearShell and window are disjoint. The exponent 16*l counts both independent assignments, since 2*|Aᵢ| ≤ 16*l. PositiveProbability and the nonempty alphabets in PlaneSpec cover empty Aᵢ, Bᵢ and Fᵢ as well.

**6. `AKLT.Blueprint.Gap.TraceMarginalsStatement` — TRUE; medium.**

The initial product of the two positive volume laws is a probability coupling. Every R.kernel row is stochastic; unskipped row marginals are the full conditional fibre laws, which preserve their original volume law after averaging. Skipped rows are exactly the identity. Iteration therefore gives a normalized nonnegative path law and the required full-law endpoint coupling, even for h=0 and pair-dependent row couplings. Only the positivity part of RegularSpec is needed; no extra assumptions on scalar p, α, boundary differences or geometry are missing.

**Two-line proof route:**

Sum the finite trace inductively in time, using stochasticity for total mass and conditional-fibre stationarity for each coordinate marginal; use the identity formula at skipped indices.  
Define c.mass by the endpoint marginal of that trace; nonnegativity and the two preserved marginals give the Coupling fields.

**Lean traps:** PairTrace Ω h has h+1 coordinates; Fin.castSucc and Fin.succ refer to the input and output time of one transition. At h=0 there is one time coordinate and an empty transition product, giving the initial product law. Pair dependence of the joint row does not affect either coordinate marginal. Coupling does not contain a separate normalization field; the endpoint trace is a probability and its two preserved marginals are the original normalized laws.

**7. `AKLT.Blueprint.Gap.TrialCountStatement` — TRUE; easy.**

The candidates j : Fin h with j.val+2 ≤ h correspond bijectively to i=2,...,h, so there are h-1. An exceptional integer e removes only candidates with i=e or i=e-1. A set of at most one exceptional index therefore removes at most two candidates. Under h ≥ 4 this yields the stated natural-number bound h-3 with no subtraction or endpoint error.

**Two-line proof route:**

Identify the candidate Fin h indices with the h-1 integers 2,...,h.  
Bound the rejected candidates by two per exceptional integer and use its cardinality bound together with h ≥ 4.

**Lean traps:** Fin h contains h indices, but j.val+2 ≤ h leaves h−1 candidates. The exception tests use integers j.val+2 and j.val+3, whereas the bound on j.val+2 is a natural-number inequality. The rejected physical trial indices are e and e−1 for an exception e. Keep h−3 as natural subtraction and use h ≥ 4 when converting the cardinal estimate.

**8. `AKLT.Blueprint.Gap.ShellAbsorptionStatement` — TRUE; medium.**

A positive trace makes every transition entry nonzero, hence positive by R.stochastic. A trial with physical index i=j.val+2 has an existing, unskipped next surgery i+1, whose identical field gives agreement on F_(i+1). For any later surgery k ≥ i+2, spacing ≥16 gives F_k ⊆ F_(i+1) and D_(k-1) ⊆ F_(i+1); its identical and fixed_exterior fields preserve agreement there, and a skipped row is the identity by marginals. The terminal target is Q_h=F_(h+1) ⊆ F_(i+1). RegularSpec, success probabilities and h ≤ s are unnecessary for this deterministic support argument.

**Two-line proof route:**

Extract positive row weights from the positive trace; the successor of a successful trial uses R.identical and gives agreement throughout F_(i+1).  
Induct through the remaining rows using shell nesting, R.fixed_exterior and the skipped identity; restrict the final agreement to farSites at radius h*s.

**Lean traps:** The trial-success event is tested at t j.succ, after surgery i=j.val+2. Its next row exists because i ≤ h; that row performs surgery i+1, not i+2. The skipped identity comes from R.marginals, while R.fixed_exterior alone would not prevent a skipped row from changing its interior. No RegularSpec premise is needed: even without assuming that the initial weights are nonnegative, a positive trace forces every transition factor to be nonzero, and R.stochastic makes it positive. The absence of h ≤ s is also harmless because the assumed kernel fields already supply all the required behavior.

**Definition coverage.**

Read both leaf modules and the complete [Gap vocabulary](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:1). The relevant closure includes Config, restrict, AgreeOn, AssignmentBound, PlaneSpec and its instances, PlaneConfig, fill, specMarginal, RegularSpec, SpecEnergy, SpecWindow, frameSpec, ShellGeometry, farSites, PairTrace, traceLaw, SurgeryKernels (every field), RowConditions (every conjunct), independentPairs, surgeryTrace, trialTimes and shellAgreement.

Read the [geometry definitions](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:1), including Plane, latticeDist, supDist, adjacency/neighbours and bond sets, setDistance, square, squareCorners, shellSpacing, shellRadius, lastShellIndex, farVolume, shell, nearShell, window, exceptionalIndices and geometryThreshold. Read [Specification.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Specification.lean:1), including sitesInVolume and the induced-boundary conventions.

Read the [probability primitives](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:1) and [finite conditioning definitions](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:35): Weight, normalize, PositiveProbability, Probability, totalVariation, AgreeOutside, Coupling, conditionalProbability, conditionOn and eventMass. Read the frame law closure in [FrameModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:1), [Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:32) and [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:7): ProperPlaneColouring, PlaneConfiguration, FrameBoundary, exteriorSites, extendLetters/extendBoundary, planeWeight/planeLaw, marginal/planeMarginal, WindowProperty, frameEnergy/frameRatio/frameBound, frameVector/frameRotation, IcoLetter/icoVector, signValue, goldenRatio, icoRadius, Vec3 and dot.

Compared the mathematical arguments with [l:planeenergy](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:691), [d:W](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:31), [l:stopped](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:56) and [l:surgery](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:132), including their proofs.

**Shared Lean and boundary-case checks.**

- `W : Finset Plane` coerces to the finite type `↥W`; all finite sums over configurations use that subtype. No `Fintype Plane` is needed. `sitesInVolume W V` is a finset of `↥W`, so conversions to physical-site sets must preserve membership and cardinality.
- The files use classical propositional decidability and classical equality. Writers should enter `classical` when forming event indicators, finite products of dependent functions, or equality tests between configurations. This adds decidability, not a mathematical premise.
- `setDistance` takes values in `ℕ∞`; its value for the empty set is `⊤`. In particular, an empty volume cannot satisfy a distance-at-most-one condition. The row construction and finite probability formulas handle its unique empty configuration.
- `shellSpacing` is the real quantity sqrt(sqrt(u)); `shellRadius` uses an integer floor. The energy constants and probabilities are real, and all assignment exponents are natural numbers. There is no unintended rational/integer division in these leaves.
- `conditionalProbability` is a quotient with no built-in positive-denominator premise. The chain and row arguments obtain positive denominators from strict positivity and compatible assignments; the two frame transfers simply identify the supplied inequalities.
- Empty assignment sets, singleton alphabets, h=0 for trace marginals, α=1 and p=1 are compatible with the statements. Trials are empty for very short traces, so the absorption antecedent then cannot assert a successful trial; this does not make the general leaf vacuous. No global inconsistency or forced-empty-domain defect was found.

**Validation.**

A single Lean 4.35.0-rc2 inspection module imported the existing read-only build and printed all eight elaborated statements plus the principal structures and predicates. It exited successfully. The explicit nonempty alphabet binder and all other finite-instance arguments of FiniteEnergyChainStatement were retained; PlaneSpec retains its finite and inhabited fields. The inspection contains only imports, printing commands and formatting options: [inspect.lean](/home/ubuntu/aklt/reports/TS_GAP_06/scratch/inspect.lean), [output](/home/ubuntu/aklt/reports/TS_GAP_06/scratch/inspect.out). Mathlib packages are linked under `scratch/.lake/packages`; no dependency or repository module was rebuilt.

Exact finite/rational diagnostics in [diagnostics.py](/home/ubuntu/aklt/reports/TS_GAP_06/scratch/diagnostics.py) passed: 5,450 assignment inequalities on small products (including empty and singleton products and nonuniform correlated laws), 9,125 trial-count cases for h=4,…,128, 588 nesting threshold cases including negative indices, 25 window-containment threshold cases, 963 conservative agreement-propagation cases with all short skip patterns, and endpoint normalization/marginal checks for traces of lengths 0,…,3 with pair-dependent conditional couplings and an identity step. For h=4 an exception at physical index 3 leaves only trial row j=2, attaining the lower bound h−3=1. Results are in [diagnostics.json](/home/ubuntu/aklt/reports/TS_GAP_06/scratch/diagnostics.json). These diagnostics support the boundary and indexing audit; the universal verdicts rest on the mathematical arguments above.
