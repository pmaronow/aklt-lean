STATUS: COMPLETE

| Leaf (`AKLT.Blueprint.Win.` prefix) | Verdict | Difficulty | Main finding |
| --- | --- | --- | --- |
| `RemovedPairResponseStatement` | TRUE | medium | The enlarged removal satisfies (P); original-layer distance is at least `depthShift`. |
| `PairDifferenceStatement` | TRUE | easy | Ordered-pair triangle bound; no positivity is needed. |
| `LogStepIdentityStatement` | TRUE | easy | Explicit positive partition sums justify every log quotient. |
| `LocalLogEstimateStatement` | TRUE | easy | Constants give `2d` or `4d+4/5 <= 1+4d`. |
| `RemovalTelescopeStatement` | TRUE | medium | Exact finite telescope; singleton and empty successor sum work. |
| `RemovalCostSumStatement` | TRUE | medium | Finite depths justify the power shift; injectivity permits summing over `X`. |
| `FrameFibreSumStatement` | TRUE | medium | The configuration fibre and all site, crossing, and exterior factors match. |
| `ComplementQuadratureStatement` | TRUE | hard | The supplied frame moments and exactness cover the partition polynomial's separate degree. |

All eight leaves are true as written and self-sufficient. No statement correction or additional premise is required. There is no identified unintended vacuity. Difficulty measures the expected Lean work, including finite reindexing and degree bookkeeping, rather than the length of the paper argument. No proofs were written and no sub-agents were launched.

The audit used repository branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The repository was not modified. The exact leaf declarations were read in [NodesRemoval.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesRemoval.lean:82) and [NodesCut.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesCut.lean:10), with the following definition closure checked:

- [Win/Defs.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/Defs.lean:72): `pairSum`, `quartic`, `removalPolynomial`, `partSum`, `partMean`, `logRatio`, `cutError`, `RemovalEnumeration`, `removedPrefix`, `RemovalStep`, `survivors`, `depthShift`, `NoBond`, `cutPins`, `windowWeight`, `frameSpins`, `framePinnedSum`, and `marginalNumerator`.
- [PinModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/PinModel.lean:9): `PinAssignment`, `extendIcoSpins`, pinned and free sums and expectations, `partitionRatio`, and the full `ResponseProperty`, including `2 <= A`, `0 < theta`, and `theta < 1`.
- [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:10): the ambient integer plane, Manhattan distance and adjacency, compass steps, neighbours, positive bond orientation, original legs, set distance, boundary depth, protected sites, and extended-natural decay.
- [FrameModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:10): proper colouring, finite configuration and boundary types, their extensions, and `planeWeight`.
- [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:10) and [Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:10): real three-vectors and dot products, unit-vector subtypes, the twelve explicit icosahedral labels/vectors and moment sum, status-dependent atom weights and product functional, degree predicates, `FrameData`, `MomentLaw`, the frozen rotation, frame vectors, and frame constants.
- [Top/Common.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Top/Common.lean:61) and [Top/Quantum.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Top/Quantum.lean:13): the complete `ExactStatement` and `ThreeFramesStatement` hypotheses. Ordinary finite-sum linearity and lattice facts below are derivable from these concrete definitions; they are not extra blueprint assumptions.

The paper comparison used [the original pin model and (P)](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:97), [quadrature, l:exact](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:297), [the frame moment identities](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:341), [e:windowfactor](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:154), [l:removal and e:removaltelescope](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:233), and [the removal-cost summation in t:cutMOS](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:740).

For `AKLT.Blueprint.Win.RemovedPairResponseStatement` ([exact declaration](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesRemoval.lean:82), paper h:P), the verdict is **TRUE**.

`RemovalStep G Y x` places `Y` outside the original protected layer and gives `x in G \\ Y` with depth at least three. Thus `insert x Y` is still an allowed removal in (P). The two distinct survivors belong to the remaining volume, lie at Manhattan distance two, and share the removed neighbour `x`. Write `b = (boundaryDepth G x).toNat`. Finite `G` has an exterior lattice point, so this depth is finite. For either survivor `u` and every original protected site `v`, the distance inequalities give `b <= 1 + latticeDist u v + 2`. Hence each distance to the protected set is at least `b - 3`, exactly the natural exponent in `depthShift`. The numerical constraints inside (P) allow weakening its decay bound to the requested bound.

Proof route:

1. Check all hypotheses of (P) for removal `insert x Y` and the survivor pair, using the four compass steps.
2. Establish the original protected-layer distance lower bound, compare decreasing decay, and unfold the pinned/free means.

Lean traps: `ENat.toNat top = 0`; prove the original depth is finite before converting its lower bound to a natural one. `depthShift` uses truncated natural subtraction, not integer subtraction. `decay theta top = 0`, so an empty protected set would not invalidate the decay comparison. Distances and protected sites always refer to `G`, not the punctured volume. The scalar restrictions on `A` and `theta` are present inside `ResponseProperty`; they have not been omitted. A square of radius two with its centre removed provides a nonempty instance of the pair geometry.

For `AKLT.Blueprint.Win.PairDifferenceStatement` ([exact declaration](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesRemoval.lean:91), paper l:removal), the verdict is **TRUE**.

`pairSum` is one half the sum over ordered unequal pairs. If `k = V.card`, there are `k*(k-1)` such pairs, giving the coefficient `k*(k-1)/2`. This is six when `k=4` and at most three when `k<=3`. Both partition means are linear in the inserted function. That linearity survives a zero normalizer because Lean's real division by zero is zero; no positivity or probability assumption is missing here. It is also harmless that `V` need not be contained in the surviving volume: its observables use the defined zero extension.

Proof route:

1. Move the two means and their difference through the finite double sum; apply the triangle inequality and the supplied pair bounds.
2. Count unequal ordered pairs, divide by two in the reals, and use `V.card <= 4` and `d >= 0`.

Lean traps: preserve the real factor `1/2` and count ordered pairs before halving. `V.card` is a natural number and needs the corresponding real cast during arithmetic. The unused `_x` parameter is redundant, not a missing geometric hypothesis. Empty and singleton `V` have zero pair sum.

For `AKLT.Blueprint.Win.LogStepIdentityStatement` ([exact declaration](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesRemoval.lean:128), paper e:removaltelescope), the verdict is **TRUE**.

The two explicit integration equalities identify each after-removal polynomial mean with the quotient of the corresponding before- and after-removal partition sums. The hypotheses give positivity of all four normalizers, hence also of these two means. Expanding the logarithms of the positive pinned/free and before/after quotients gives precisely the asserted identity. A `RemovalStep` premise is unnecessary because the needed integration identities are already assumed.

Proof route:

1. Rewrite each after-removal polynomial mean as its positive before-removal partition sum divided by its after-removal normalizer.
2. Expand the positive quotient logarithms on both sides and rearrange the four log terms.

Lean traps: split or simplify the Boolean branches of `partSum` before matching pinned/free definitions. Supply nonzero or positive hypotheses for the log division identities. `Real.log 0` and division by zero are total in Lean, but the explicit positivity hypotheses exclude their problematic use here. The sign agrees with the paper's before-minus-after step.

For `AKLT.Blueprint.Win.LocalLogEstimateStatement` ([exact declaration](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesRemoval.lean:139), paper l:removal), the verdict is **TRUE**.

Positive normalizers give `partMean pinned ... 1 = 1`. After cancelling these constants, the difference of polynomial means is at most `d` when `V.card != 4`. For `V.card = 4` it is at most `6d/3 + (3+3)/15 = 2d+2/5`. The supplied log estimate and the supplied half-lower-bounds therefore give `2d` or `4d+4/5 <= 1+4d`. No moment law, probability premise, or geometric relation between `V` and `x` is needed beyond the bounds explicitly assumed.

Proof route:

1. Expand the means of `removalPolynomial`, cancel the constant means, and bound the pair difference and optional quartic difference.
2. Apply the supplied log Lipschitz inequality and simplify its two branches to the stated bounds.

Lean traps: constant-mean cancellation needs each Boolean normalizer to be nonzero; this is supplied. The quartic branch depends on `V.card`, while `quartic x` uses the four compass neighbours of `x`; the independently assumed quartic bound makes this distinction harmless. The fractions are real fractions. In the nonquartic branch no quartic term should be introduced.

For `AKLT.Blueprint.Win.RemovalTelescopeStatement` ([exact declaration](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesRemoval.lean:154), paper e:removaltelescope), the verdict is **TRUE**.

The endpoint assumptions identify the sum of consecutive prefix differences with `-cutError`. The absolute finite-sum inequality and the given per-step bounds supply the desired total. Splitting off index zero leaves exactly the terms indexed by `j : Fin e.last` with site `e.site j.succ`. No sign restriction on `A` or `theta` is required for this algebraic implication; no inequality is multiplied by them during the summation and factoring step.

Proof route:

1. Telescope the consecutive log differences, use the two endpoints, and remove the sign inside the absolute value.
2. Bound the absolute sum, split zero from successor indices, and factor out `2*A` from the successor sum.

Lean traps: `cutError` is after-minus-before, opposite to the summed step orientation. `e.site 0` has type `Fin (e.last+1)` and always exists. If `e.last=0`, the successor sum is over `Fin 0` and equals zero, leaving one seed. `RemovalEnumeration` deliberately excludes empty `X`; that matches the paper's `p>=1` convention and is not unintended vacuity. Its injectivity and predecessor-adjacency fields are stronger than this pure telescope requires.

For `AKLT.Blueprint.Win.RemovalCostSumStatement` ([exact declaration](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesRemoval.lean:166), paper t:cutMOS), the verdict is **TRUE**.

Every depth is finite because `G` is finite. On `X` the depth assumption gives the exact identity `theta ^ depthShift G z = theta ^ (-3 : Z) * decay theta (boundaryDepth G z)`. The seed power is at most one because its exponent is natural and `0<theta<1`. The injective enumeration has image exactly `X`, so its nonseed decay sum can be enlarged to the sum over all of `X`. All coefficients multiplying inequalities are nonnegative. The absent explicit premise `X subset G` is derivable: a site outside `G` has boundary depth zero.

Proof route:

1. Establish finite depths and the shifted-power identity on `X`, and bound the seed power by one.
2. Add the nonnegative seed contribution to the nonseed sum, reindex the full enumeration onto `X`, and multiply by the nonnegative coefficients.

Lean traps: exclude `top` before using depth conversion or natural subtraction identities. The exponent of the seed is natural; the exponent `(-3 : Z)` is an integer power, whose inverse factor requires `theta != 0`. Use enumeration injectivity when converting an indexed sum to a `Finset.image` sum, or multiplicities would be lost. The predecessor-adjacency field is unused here. `A=0` and singleton cuts work without changes.

For `AKLT.Blueprint.Win.FrameFibreSumStatement` ([exact declaration](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesCut.lean:10), paper e:windowfactor), the verdict is **TRUE**.

Since `B subset F`, configurations on `F` whose restriction equals `s` are in bijection with configurations on `G=F \\ B`. Internal bonds divide into bonds within `B`, within `G`, and between the two pieces. A crossing bond is the corresponding original leg of `G` with its endpoint letter fixed by `s`. Every other original leg of `G` ends outside `F` and receives the appropriate frame boundary vector. The `NoBond` premise prevents exterior legs from `B`, so `windowWeight` contains all factors depending only on the fixed window. Site weights split using `F.card=B.card+G.card`. This is the actual frame-weight identity; it does not replace the window alphabet by the unrotated icosahedral alphabet.

Proof route:

1. Reindex the restriction fibre by configurations on `F \\ B`, keeping `s` fixed.
2. Split site and bond products, match crossing/exterior factors to `cutPins` using dot symmetry, and factor out `windowWeight`.

Lean traps: configuration types are functions on finite-site subtypes, so the restriction and gluing maps need consistent membership transports. Internal bonds use positive orientations once; pin legs point out from the complementary volume, sometimes reversing a crossing bond. `cutPins` correctly uses the colour of the endpoint and chooses the window letter precisely when that endpoint lies in `B`. Otherwise that endpoint is a genuine exterior neighbour of `F`, so the boundary extension is not using its default label. Products over original legs appear both as subtype `Fintype` products and as `Finset` products and need matching. The explicit `unit` argument only supplies a subtype proof; arbitrary choices of that proof do not change any vector. Proper colouring and the global frame statement are stronger than this algebraic identity needs. Empty volumes and windows use their unique empty configurations.

For `AKLT.Blueprint.Win.ComplementQuadratureStatement` ([exact declaration](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesCut.lean:20), paper l:exact), the verdict is **TRUE**.

For each colour, `ThreeFramesStatement` gives unit norms and equality of all polynomial moments through degree four with `moment`. Uniform weights `1/12` are positive and sum to one over the twelve labels; after relabelling by `Fin 12`, this is the required `MomentLaw`. On the surviving sites, the partition integrand is a polynomial. Each variable appears in at most one factor for each original compass direction: a retained internal bond or a retained original pin. A direction toward a removed site contributes no factor. Thus its separate degree is at most four, including at sites carrying original pins. Applying `ExactStatement` with every status `.U` yields exactly the two partition sums.

Proof route:

1. Represent the retained partition integrand as a polynomial on the finite surviving sites and bound each site's separate degree by four via compass-direction counting.
2. Extract the frame `MomentLaw`s, apply `ExactStatement` with all statuses `.U`, and reindex the finite sums while removing zero-weight atoms.

Lean traps: `ExactStatement` uses sites `Fin n` and labels `Option (Fin (k x))`; the concrete sums use the subtype `G \\ Y` and `IcoLetter = Fin 3 x Fin 2 x Fin 2`. Both site and atom relabellings are necessary. At status `.U`, every `none` atom has zero weight, and the `.U` product functional on the other side likewise reduces to the twelve-label icosahedral sum. The relevant bound is separate degree four, not total degree four over all sites. Proper colouring is not required for moment quadrature. Nor is `Y subset G` needed: only `G \\ Y` and the retained original tails occur in either sum. The pins remain those of original `G`; creating pins at holes would change the statement. With no surviving sites both sides equal one. No claim of equality for arbitrary observables or for the unsummed window laws is used.

The Lean inspection in [Inspect.lean](/home/ubuntu/aklt/reports/TS_WIN_08/scratch/Inspect.lean:1) completed successfully with Lean `4.35.0-rc2`; [its output](/home/ubuntu/aklt/reports/TS_WIN_08/scratch/lean-inspection.log:1) confirms all eight names have closed type `Prop`, the enumeration fields and successor index types are retained, and the required finite-configuration, decidable-equality, and finite-original-leg instances exist. No silently dropped instance hypothesis was found. Noncomputable set distances and finite configuration equality can be handled with ordinary local `classical`; they do not require mathematical premises. Coefficients and sums are real, while cardinalities are natural and the negative decay power is explicitly integer-valued.

The independent [small-case script](/home/ubuntu/aklt/reports/TS_WIN_08/scratch/check_small_cases.py:1) also passed. It checked all 35 three-variable monomials through total degree four under the three actual frames, 21 direct partition comparisons with empty/removal cases and arbitrary unit pins, three frame-fibre identities including a fixed centre in a five-site cross, 1,362 survivor pairs in 58 finite lattice volumes, and 1,464 exact rational comparisons for the cost enlargement. Maximum floating residuals were `1.12e-16` for moments, `4.45e-16` for partition quadrature, and `1.12e-16` for fibre factorization; full results are in [small-case-results.json](/home/ubuntu/aklt/reports/TS_WIN_08/scratch/small-case-results.json:1). These computations are diagnostics, not proofs of the universal claims or of global (P). Only one scratch Lean module was elaborated, with one Lean process; existing repository/package artifacts were read without rebuilding them.
