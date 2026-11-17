STATUS: COMPLETE

| Leaf | Verdict | Difficulty | Reason |
| --- | --- | --- | --- |
| [AKLT.Blueprint.Q.FrameWeightsPositiveStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesEnergy.lean:11) | TRUE | easy | Every site weight and every properly coloured interaction factor is positive. |
| [AKLT.Blueprint.Q.PlaneConditioningStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesEnergy.lean:27) | TRUE | hard | The fixed-complement fibre is exactly the smaller configuration space with the induced boundary. |
| [AKLT.Blueprint.Q.TorusMarkovStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesEnergy.lean:35) | TRUE | hard | Exterior factors cancel; crossing factors see precisely the stated exterior neighbour set. |
| [AKLT.Blueprint.Q.PlaneOneSiteEnergyStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesEnergy.lean:45) | TRUE | medium | Twelve fibre weights and four incident factors give the stated energy bound. |
| [AKLT.Blueprint.Q.TorusOneSiteEnergyStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesEnergy.lean:53) | TRUE | medium | Four distinct incident frozen bonds give the same bound, including period three. |
| [AKLT.Blueprint.Q.PartialAssignmentStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesEnergy.lean:62) | TRUE | hard | Average over full fibres, then multiply conditional bounds along the assignment. |
| [AKLT.Blueprint.Q.PlaneAssignmentReindexStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesEnergy.lean:74) | TRUE | easy | Subtype lifting preserves both events, disjointness, and the exponent. |
| [AKLT.Blueprint.Q.PlaneProductReferenceStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesEnergy.lean:86) | TRUE | medium | Positive normalized site laws form a positive normalized finite product. |

All eight leaves are **TRUE** as written and self-sufficient. No correction or additional premise is needed. No leaf has unintended vacuity; the empty-volume cases included in the paper behave correctly. The difficulty ratings concern producing the Lean argument from these definitions, not the length of the informal argument. No proofs were written.

Reviewed repository branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The repository was clean before and after the review. The paper sources are [Definition d:framemodel](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:490) and [Lemma l:planeenergy and its proof](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:691).

The definition trace covers [Q.Definitions](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/Definitions.lean:44) (`interactionBounds`, `planeSiteWeight`, `planeProductReference`, `fullFibreEvent`); [FrameModel](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:10) (proper colourings, configuration types, finite exterior sites and boundaries, extensions, plane/torus weights and laws, and `marginal`); [Specification](/home/ubuntu/aklt/repo/AKLT/Defs/Specification.lean:10) (`inducedBoundary`, both conditional laws, and the available subtype-set construction); [FiniteNetwork](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:36) (the conditional quotient and `conditionOn`); and [Probability](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:9) (`Weight`, `normalize`, `PositiveProbability`, `AgreeOutside`).

Their geometric and numerical dependencies were also read: [Geometry](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8) (`Plane`, `latticeDist`, `Adjacent`, `Compass` and its steps, `neighbours`, `positiveNeighbours`, `internalBonds`, `originalLegs`); [Challenge.Main](/home/ubuntu/aklt/repo/AKLT/Challenge/Main.lean:17) (`Size`, its nonzero-modulus instance, `Site`, `Direction`, `Bond`, `nextSite`); [Quantum](/home/ubuntu/aklt/repo/AKLT/Defs/Quantum.lean:10) (`torusNeighbours`); [Frame](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:33) (`frameRotation`, `frameVector`, `frameBound`, `frameRatio`, `frameEnergy`); and [Moment](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9) (`Vec3`, `dot`, `IcoLetter`, `signValue`, `goldenRatio`, `icoRadius`, `icoVector`). No facts about spinors or frame moment identities are needed for these leaves.

Write b = `frameBound` and r = `frameRatio`. Although `interactionBounds` does not separately assert their signs, b = (5 - sqrt(5))/505 directly gives 0 < b < 1, and r = b/(2-b) gives 0 < r < 1. These facts can be established from the definitions within each leaf; no unproved sibling leaf is needed as an extra premise.

**FrameWeightsPositiveStatement.** Proper colouring separates the frame indices on every internal plane edge, boundary leg, and frozen torus bond. interactionBounds bounds the corresponding plus/minus factor below by frameBound = (5 - sqrt 5)/505 > 0; the site factors are positive. Empty plane volumes have weight 1. No additional moment, unit-vector, or scalar-bound hypothesis is needed because the scalar is explicit.

1. Derive frameBound > 0 from sqrt(5)^2 = 5 and sqrt(5) >= 0; extract the appropriate interactionBounds lower bound using proper colouring on each indexed edge.
2. Apply positivity of finite products and of (1/12)^W.card, including the empty product.

Lean details: Use the lower bound for the plus sign on plane edges/legs and the minus sign on torus bonds. Membership in the indexing finsets supplies adjacency. The factor (1/12 : ℝ) is real division; it is not natural-number division. Prove the explicit scalar bound b > 0 before applying product positivity.

**PlaneConditioningStatement.** For V subset W, restriction identifies the W\V fibre with PlaneConfiguration V. Factoring planeWeight on that fibre gives a strictly positive constant times the V weight with inducedBoundary; neighbours of V outside W necessarily lie in exteriorSites W. Thus both normalizations and the marginal cancel the same constant. W and V may be empty.

1. Identify the fixed-complement fibre with V configurations and split internal bonds/original legs into factors meeting V and constant factors; reverse crossing orientations with symmetry of dot.
2. Prove the constant and normalizers positive from interactionBounds and explicit frameBound, then cancel them in conditionOn and marginal.

Lean details: Equality is between weights on PlaneConfiguration V, after a pushforward; it is not equality of weights on the old W configurations. Internal edges use positive orientation while new boundary legs point outward, so some crossing factors require symmetry of dot. If z is a neighbour of V outside W, V ⊆ W shows z belongs to exteriorSites W: extendBoundary never uses its fallback there.

**TorusMarkovStatement.** After fixing all coordinates outside U, torusWeight factors into a positive exterior constant and a block weight involving only internal bonds and crossings. Every exterior endpoint of a crossing belongs to (U.biUnion torusNeighbours) \ U, where sigma and xi agree. Constants cancel after conditionOn and marginal. Size encodes periods >= 3, excluding loops and duplicate unoriented bonds; empty/full U are valid.

1. Parametrize each AgreeOutside fibre by U -> IcoLetter and factor the weight into internal/crossing factors and a strictly positive exterior constant.
2. Use the boundary-agreement hypothesis on each crossing endpoint and cancel the constants in normalized pushforwards; handle empty/full blocks by the same formula.

Lean details: The agreement hypothesis is only on (U.biUnion torusNeighbours) \ U. The inside letters of sigma/xi and their farther exterior letters may differ. Each crossing is one frozen Bond; do not count both orientations. Size already contains 3 ≤ L.val and 3 ≤ N.val and supplies nonzero moduli; neither evenness nor bipartiteness is assumed.

**PlaneOneSiteEnergyStatement.** A site x in W has four lattice neighbours; each contributes exactly one internal-edge or original-leg factor involving x. On fullFibreEvent x sigma all other factors are fixed and positive. The twelve fibre weights therefore have conditional ratio at least (1/12)*(frameBound/(2-frameBound))^4 = frameEnergy. The fibre is nonempty (sigma itself), so its denominator is positive. For W empty the site quantifier has no cases, as intended.

1. Reindex the fully fixed fibre by the twelve updates at x and cancel the positive normalization and exterior factors.
2. Bound the remaining d <= 4 plus-sign factors between frameBound and 2-frameBound, giving (1/12)*frameRatio^d >= frameEnergy using 0 < frameRatio < 1.

Lean details: Here x is a subtype element of W, so the one-site fibre contains all twelve replacements of its actual coordinate. There are four factors in total, combining internal bonds and original legs, rather than four of each. Cancel a positive fibre mass, including the common plane normalizer; normalize is a total real quotient, so cancellation needs the nonzero proof. For W = ∅ there is no x, an intended special case.

**TorusOneSiteEnergyStatement.** Size means both periods are >= 3, so every site has exactly four distinct incident frozen bonds and none is a loop, including on a 3-by-3 torus. Proper colouring and interactionBounds bound all four minus-sign factors. The fixed-exterior fibre contains twelve updates, has positive mass, and gives the claimed lower bound frameEnergy after cancellation. No parity or bipartiteness premise is needed.

1. Identify the one-site fibre with IcoLetter and split frozen bonds into its four incident bonds and the constant exterior product.
2. Cancel positive constants and bound the letter numerator below by frameBound^4 and the twelve-term denominator above by 12*(2-frameBound)^4.

Lean details: Count the two outgoing and two incoming bonds, rather than only the two positive directions at x. At period three the positive and negative neighbours are distinct. The cardinality is twelve labels (Fin 3 × Fin 2 × Fin 2), independently of any theorem about injectivity of the geometric frame vectors.

**PartialAssignmentStatement.** PositiveProbability gives positive mass to every realized partial assignment, and disjoint U,J allow all prescribed letters to be realized simultaneously. Averaging the one-site fibre lower bound over any off-site partial event preserves alpha; adjoining the sites of U one at a time then gives alpha^U.card. The empty product/site cases give probability 1. Lean printing confirms the explicit family of Fintype instances is used in Pi.instFintype in every probability sum; the Nonempty premise is retained.

1. For any positive event determined off x, sum the full-fibre inequalities to obtain conditionalProbability(x = t | event) >= alpha.
2. Induct over the distinct sites of U, adjoining each prescribed letter to the J event; use full support for all denominators and the chain rule to multiply the bounds.

Lean details: The explicit family (_ : ∀ x, Fintype (S x)) is actually used: Lean prints Pi.instFintype with that family in PositiveProbability and both conditionalProbability occurrences. The explicit Nonempty premise remains an implication; a proof can install its values locally when choosing configurations. Alphabet equality need not be assumed decidable: use classical decidability for event sums and dependent coordinate updates. Fintype ι and DecidableEq ι are retained. With ι empty there is one dependent function, not an empty configuration space.

**PlaneAssignmentReindexStatement.** For U,J subset W, lifting membership to the subtype W preserves their disjointness and cardinalities. Restrict a,b to W; on all queried sites extendLetters evaluates to the actual subtype coordinate. Thus the two event predicates and the exponent are unchanged. Positivity/normalization of p and sign bounds on alpha are unnecessary because this is an exact reindexing implication.

1. Lift U and J to finite subsets of W (e.g. sitesInVolume W U and sitesInVolume W J), preserving disjointness and U.card using the subset hypotheses.
2. Apply the premise to the restrictions of a,b and rewrite each event using extendLetters on members of W and subtype proof irrelevance.

Lean details: A Finset Plane and a Finset W are different types. Lift U,J to subtype finsets using their subset hypotheses, and prove equality of their cardinalities; an arbitrary image-card inequality is insufficient. Subtype proof irrelevance identifies coordinate evaluations. No positivity, normalization, or sign condition on alpha is missing: the premise transfers through identical events, even for totalized quotients.

**PlaneProductReferenceStatement.** Each filtered original leg joins distinct colours, so its plus-sign factor is >= frameBound > 0. Hence planeSiteWeight is strictly positive on the twelve-letter alphabet and has positive normalizer. The product of these normalized site weights is pointwise positive and sums to the product of the site sums, namely 1; for W empty the configuration space has one point of weight 1.

1. Use proper colouring and interactionBounds to prove each site weight positive, then normalize over the nonempty twelve-letter alphabet.
2. Use positivity of finite products and factor the sum over W -> IcoLetter into the product of the normalized one-site sums; include the empty product.

Lean details: A finite volume W has a finite subtype even though Plane has no Fintype. Sum over functions W → IcoLetter and factor the finite product sum; do not assume independence as a separate premise. The alphabet is nonempty, so each one-site normalizer is positive. For W = ∅ the local-site assertion has no cases, but the product-law assertion still requires, and has, total mass one on its unique configuration.

**Checks performed.** [Inspect.lean](/home/ubuntu/aklt/reports/TS_Q_07/scratch/Inspect.lean) was checked with Lean `v4.35.0-rc2`, importing the existing compiled modules without rebuilding or writing into the repository. [inspect.log](/home/ubuntu/aklt/reports/TS_Q_07/scratch/inspect.log) contains the printed forms of all eight statements, the explicit instance expansion of PartialAssignmentStatement, and the finite evaluations. They confirm: twelve letters; zero empty-volume internal edges; four singleton boundary legs; one internal edge and six boundary legs for an adjacent pair; one empty-volume configuration; and four neighbours on a 3-by-3 torus. Exactly one Lean process was used.

[checks.py](/home/ubuntu/aklt/reports/TS_Q_07/scratch/checks.py) passed the following diagnostics:

- Exact rational arithmetic in Q(sqrt(5)) checked all 1,728 signed interaction factors with distinct frame indices. Both endpoint bounds are attained (32 occurrences each). The common squared icosahedron radius is (5 + sqrt(5))/2 > 0. Thus there is no contradiction concealed in the supplied numerical antecedent.
- All 19,683 pairs V ⊆ W within a 3-by-3 plane board have the required retained-edge sets, valid induced exterior sites, preserved subtype cardinality, and four total incident interactions per site.
- Full finite sums for 27 plane conditioning cases across six shapes, including the empty, singleton, adjacent-pair, disconnected-pair, three-site corner and three-site line volumes, agreed to absolute error at most 1.11e-16. Their product references are positive and normalize to one; all their one-site fibres satisfy the energy bound.
- For all 25 pairs of torus periods from three through seven, frozen bonds have distinct endpoints, no duplicate unordered edges, and four incidences per site. All 512 blocks on the 3-by-3 torus have exactly the exterior neighbour boundary used in the statement. Twenty-five numerical conditional comparisons across five period pairs agreed to absolute error at most 2.78e-16; sampled torus one-site fibres satisfy the energy bound.
- Exact rational sums checked 5,197 partial-assignment inequalities for finite products with sizes (), (2), (2,3), (2,3,1), and (2,3,2), including empty sites, singleton alphabets, empty assignments, and empty conditioning.

The finite diagnostics supplement the mathematical definition review. Floating-point conditional checks cover the stated examples and are not formal proofs of the universal leaves. No sub-agents were launched and no repository files were modified.
