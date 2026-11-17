STATUS: COMPLETE

All eight leaves are **TRUE** as written and self-sufficient. No statement correction or additional premise is needed. The repository was read on branch `main`; all generated files are in this report directory. No leaf proofs were written.

Every name in the table has namespace `AKLT.Blueprint.Q`. Full names, reasons, fixes, two-line proof routes, and difficulties are recorded in [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_Q_05/verdicts.jsonl). Difficulty estimates concern Lean formalization.

| Leaf | Paper label | Verdict | Difficulty |
| --- | --- | --- | --- |
| [CentreDegreeCancellationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesSplits.lean:47) | `l:divisibility` | TRUE | medium |
| [IncidentProductDegreeStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesSplits.lean:55) | `l:divisibility` | TRUE | medium |
| [StateCentreDegreeStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesSplits.lean:61) | `d:poly` | TRUE | easy |
| [StarEdgeEnumerationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesSplits.lean:76) | `l:star` | TRUE | medium |
| [StarCasimirChartStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesSplits.lean:83) | `l:star` | TRUE | hard |
| [StarProjectorTransportStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesSplits.lean:91) | `l:star` | TRUE | medium |
| [DeterminantModulusStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesQuantum.lean:11) | `l:qmod` | TRUE | easy |
| [GroundProductWeightStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesQuantum.lean:17) | `e:frame-ground-weight` | TRUE | easy |

**Definition and hypothesis audit.** The exact declarations were read from both leaf modules and inspected with Lean `#print`. The following project definitions were followed through their concrete implementations, rather than inferred from their names or comments:

| Definitions | Source and semantic consequence |
| --- | --- |
| `Size`, `size_neZero`, `Site`, `Direction`, `Bond`, `nextSite`, `bondSites` | [Challenge/Main.lean](/home/ubuntu/aklt/repo/AKLT/Challenge/Main.lean:17): periods are natural numbers at least three; coordinates are `ZMod`; bonds are site/direction indices; endpoint sets are finsets. |
| `Configuration`, `Hilbert`, `SpinorPolynomial`, `singlet`, `vbsPolynomial`, `monomialDegree`, `B` | [Challenge/Main.lean](/home/ubuntu/aklt/repo/AKLT/Challenge/Main.lean:62): the Hilbert coordinates are functions to `Fin 5`, the polynomial coefficient ring is ℂ, and the binomial square roots convert orthonormal to monomial coordinates. |
| `statePolynomial`, `independentAt`, `incidentProduct`, `groundScale` | [Q/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/Definitions.lean:72) and [groundScale](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/Definitions.lean:162): independence means both centre exponents vanish on support; the incident product includes every bond once, with factor one for nonincident bonds. |
| `starEdge`, `casimirCopies` | [NodesSplits.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesSplits.lean:65): west/south bonds start at neighbours; the intertwining identity quantifies over all vectors, rows, and star coordinates. |
| `spinZ`, `spinPlus`, `spinMinus`, `atSite`, `onBond`, `bondCasimir`, `spin4Space`, `P` | [Challenge/Main.lean](/home/ubuntu/aklt/repo/AKLT/Challenge/Main.lean:49): concrete spin matrices, finite matrix lifts, the stated Casimir expression, and the orthogonal projector onto eigenvalue 20. |
| `StarHilbert`, `starAtSite`, `starCasimir` | [Defs/Quantum.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Quantum.lean:23): the same matrix-lift and Casimir expressions, on centre 0 and leaf `j.val + 1`. |
| `compatible`, `determinant`; `Spinor`, `pauli`, `spinDensity`; `Vec3`, `dot` | [Q/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/Definitions.lean:12), [Defs/Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:50), [Defs/Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9): compatibility includes normalization and the conjugated outer-product identity with the standard Pauli signs. |
| `TorusConfiguration`, `torusWeight`, `torusReference`, `frameEval`; `Weight`, `physicalEval` | [Defs/FrameModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:59), [Defs/Probability.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:9), [Defs/Polynomial.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Polynomial.lean:33): weights take real values; the reference weight has factor `5/12` per site; evaluation uses the orthonormal-to-monomial factors. |
| `frameSpinor`, `frameVector`, `frameRotation`, `icoVector`, `IcoLetter`, `signValue`, `goldenRatio`, `icoRadius` | [Defs/Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:33) and [Defs/Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:24): the explicit rotated finite alphabets and spinor formula, including its pole branch. The weight leaf supplies its needed modulus identity as a premise. |

The standard Mathlib meanings of `EuclideanSpace`, the finite matrix action, eigenspaces, and `starProjection` were also checked. In particular, `starProjection` is the ambient-space orthogonal projection, and projection transport along a linear isometry is available as `LinearIsometry.map_starProjection` / `Submodule.starProjection_map_apply`.

**CentreDegreeCancellationStatement — TRUE.** The relevant grading gives weight one to `(x,0)` and `(x,1)` and weight zero to every other variable. A nonzero homogeneous degree-four factor shifts each homogeneous component of χ to a distinct degree. Multiplication is injective because the polynomial ring over ℂ is an integral domain. This is the single-site specialization of the paper's multigrading argument at [sec3 lines 176ff.](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:176).

Proof route:

1. Decompose χ into its finitely many components for the centre grading; p and pχ lie in degree four by hypothesis.
2. Every positive-degree component has zero product with p, hence is zero; all supported centre exponents therefore vanish.

Lean traps: use the centre grading, since χ may depend on spectator variables. `support_mul` gives a containment and cannot justify cancellation of individual terms. χ = 0 and pχ = 0 cause no missing-premise problem: p ≠ 0 forces χ = 0 in the latter case.

**IncidentProductDegreeStatement — TRUE.** The four incident oriented indices are `(x,0)`, `((x.1-1,x.2),0)`, `(x,1)`, and `((x.1,x.2-1),1)`. Each selected determinant has two distinct monomials and centre degree one. Exactly four such nonzero factors occur; every other factor is one. The period-three case is covered by the [paper's neighbour argument](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:147).

Proof route:

1. Establish the four incident indices and distinct endpoints from the period bounds stored in `Size`.
2. Multiply their nonzero degree-one determinants in the integral domain to obtain a nonzero degree-four product.

Lean traps: the product is over the `Fintype` of oriented bond indices, whereas incidence uses membership in an endpoint `Finset`. These are reconciled by the four-index calculation. Neither primality nor an additional graph-simplicity hypothesis is needed.

**StateCentreDegreeStatement — TRUE.** Each summand has exponent vector `monomialDegree σ`. At x its centre exponents sum to `(4 - (σ x).val) + (σ x).val = 4`. Scalar coefficients and addition can remove monomials but cannot add a monomial of another centre degree. This implements [Definition d:poly](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:14).

Proof route:

1. Expand `monomialDegree` and apply the bound `(σ x).val < 5` to the natural-number subtraction.
2. Bound the support of each scalar-multiplied monomial and then the support of their finite sum.

Lean traps: the subtraction is in ℕ, so the `Fin 5` bound is essential. No cancellation or nonvanishing of the square-root factors is needed for this support assertion. The zero state's empty support is an intended case, not vacuity of the leaf.

**StarEdgeEnumerationStatement — TRUE.** The two directions distinguish horizontal and vertical bonds; within each direction the two origins differ. Expanding endpoint membership gives exactly the four `starEdge` cases. This matches [the incident-star counting in the paper](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:245).

Proof route:

1. Split the four `Fin 4` indices and two bond directions to establish injectivity.
2. Expand `bondSites` and `nextSite`, and solve the start/terminal endpoint equations to establish finset equality.

Lean traps: west/south are incoming positive-direction bonds. Their coordinate subtraction is in `ZMod`, so it wraps rather than truncates. A finset image alone forgets multiplicities; the statement explicitly supplies the injectivity required for later sums.

**StarCasimirChartStatement — TRUE.** Let (S=\operatorname{card}(\mathrm{Site}\ L\ N)\). There are five distinct distinguished sites and (S\ge9\). One may take (n=5^{S-5}\), enumerate the spectator configurations by `Fin n`, and split each physical configuration into its spectator label and five ordered spin labels. The resulting permutation of the orthonormal coordinate basis gives U. The two finite matrix-lift definitions then agree on each row. Edges between neighbours at period three are irrelevant because they occur in none of the four Casimirs being transported, exactly as the [paper explains](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:245).

Proof route:

1. Split and enumerate configurations in the order centre/east/west/north/south plus spectators; use the induced Euclidean coordinate isometry.
2. Reindex the matrix-action sums for `atSite` and preserve the additions, scalar factors, and compositions in the Casimir formula.

Lean traps: `Fin 5 → Fin 5` indexes (5^5\) basis configurations. The target is the Euclidean space on `Fin n × (Fin 5 → Fin 5)`; each row must be wrapped with `WithLp.toLp 2`, as the statement does. Check (S\ge5\) before the subtraction in the proposed n. Incoming bonds interchange the two site summands in `onBond`; commutativity of addition removes that ordering difference.

**StarProjectorTransportStatement — TRUE.** For each j, the intertwining hypothesis and U's inverse identify the transported eigenvalue-20 space with the subspace of arrays whose every row belongs to the corresponding fixed-star eigenspace. The Euclidean inner product is the sum of the row inner products. Its orthogonal projection is consequently the rowwise star projection. The projector `P` is defined on precisely the source eigenspace.

Proof route:

1. Use `casimirCopies` in both directions to identify the image eigenspace as the subspace of rowwise star eigenvectors.
2. Transport the orthogonal projection along U and characterize its target by rowwise membership and orthogonality; evaluate at `(r,s)`.

Lean traps: both linearity and the isometry of U matter; surjectivity supplies the reverse eigenspace inclusion. Finite dimension supplies orthogonal projections, so there is no missing completeness hypothesis. Self-adjointness of the Casimirs is unnecessary for this transport argument. Although `n = 0` has no rows, it also admits no such U from the positive-dimensional physical space; this does not make the whole leaf vacuous.

**DeterminantModulusStatement — TRUE.** The density matrices have entries `(1+a₂)/2`, `(a₀-i a₁)/2`, `(a₀+i a₁)/2`, `(1-a₂)/2`, with the expected conjugation. The determinant Gram identity and the trace of the product of the two density matrices give the claimed formula, matching [Lemma l:qmod](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:458). Compatibility already forces a and b to be unit Bloch vectors; that condition need not be repeated.

Proof route:

1. Expand the two-coordinate determinant to express its squared modulus as the product of squared spinor norms minus the squared overlap.
2. Substitute the compatibility densities and evaluate the overlap square as `(1 + dot a b)/2`; use the two norm-one equalities.

Lean traps: `Vec3` has real coordinates, whereas `Spinor` and `spinDensity` are complex. Preserve the conjugation in `z k * star (z l)`, particularly the sign of the Pauli-y entry. `Complex.normSq` and the conclusion's division by two are real. The hypotheses are consistent: `(a,z)=((0,0,1),(1,0))` is an example.

**GroundProductWeightStatement — TRUE.** Write (S=|\mathrm{Site}|\), (E=|\mathrm{Bond}|\), and let W denote the product of the bond interactions. The supplied premises reduce the left side to ((5/12)^S 2^{-E}W\). The right side is ((5^S/2^E)(1/12)^S W\). These agree exactly with [equation e:frame-ground-weight](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:583).

Proof route:

1. Rewrite by the product-evaluation premise, distribute `Complex.normSq` over the finite product, and apply the modulus premise to every bond.
2. Expand the three real weight/scale definitions and collect constant products as powers, using `2^E ≠ 0`.

Lean traps: `torusReference` is an unnormalized product reference weight, not a probability measure. The factors `5/12`, `1/12`, and `1/2` here are real divisions. Proper colouring, positive weights, and nowhere-zero evaluations are unnecessary for this algebraic identity; zero interactions are allowed. The two bridge identities are explicit hypotheses, so the writer need not establish them within this leaf.

**Validation.** [diagnostics.lean](/home/ubuntu/aklt/reports/TS_Q_05/diagnostics.lean) ran successfully with Lean `v4.35.0-rc2`, importing the two compiled repository modules through `LEAN_PATH`. It prints all eight closed declarations, the row-coordinate types, and the relevant projection transport signatures; `Fintype` instances for general `Site L N` and `Bond L N` synthesize. No expected premise was silently dropped. See [diagnostics.log](/home/ubuntu/aklt/reports/TS_Q_05/diagnostics.log).

[checks.py](/home/ubuntu/aklt/reports/TS_Q_05/checks.py) passed using only the Python standard library. Its [results](/home/ubuntu/aklt/reports/TS_Q_05/checks.json) cover all 36 ordered period pairs in `3..8`, all 1,089 sites and 2,178 bonds: no loops or repeated unordered edges, the four-index enumeration, five distinct star sites, and explicit nonzero incident-product expansions with centre degree four. It also checks all five physical centre-exponent choices, exact symbolic Gram/Pauli expansions over rational coefficients, and 192 exact rational normalization cases. These diagnostics support the definition audit; the general verdicts use the arguments above, rather than extrapolation from small cases.

General elaboration notes: local `classical` may be useful for finite configuration equivalences, polynomial supports, and subspace constructions, but adds no mathematical premise. All eight leaves are closed `Prop` declarations; the geometry bounds come from the explicit `Size` subtype, not an omitted typeclass variable. No repository build or repository write was performed; one scratch Lean process was used.
