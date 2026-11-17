STATUS: COMPLETE

| Leaf | Paper label | Verdict | Difficulty | Required fix |
| --- | --- | --- | --- | --- |
| `AKLT.Blueprint.Mom.OneSiteConditionalReductionStatement` | `l:35` | **TRUE** | medium | None |

The [exact leaf](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesConsequences.lean:26) is self-sufficient. It expresses the reduction of a conditional mean to a local product law with at most three ball fields. This is the reduction used in [the final paragraph of Lemma l:35](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:290), with the finite factorization explained in [Lemma l:finitefacts](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:159). The leaf itself does not assert the subsequent 3/5 bound.

Every user-defined dependency of the leaf was read through to its finite sums, products, or explicit vector coordinates:

| Definitions inspected | Meaning relevant to the verdict |
| --- | --- |
| [FiniteSpinNetwork, Valid, weight](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:10) | Sites are `Fin n`; bonds are a `Finset` of ordered endpoint pairs; pins are dependent families of `UnitVector`. `Valid` requires U/D status, `e.1 < e.2` for every bond, and incident bond count plus pin count at most four. The weight multiplies all site masses, bond factors, and the pin factors selected by `pinned`. |
| [Vec3, dot, normSq, UnitVector](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9) | Three real coordinates, scalar product equal to the sum of coordinate products, squared Euclidean norm, and a subtype with squared norm exactly one. |
| [goldenRatio, icoRadius, IcoLetter, signValue, icoVector](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:24) | Explicit twelve labels `Fin 3 × Fin 2 × Fin 2`, independent signs, and the paper's coordinate vectors divided by `sqrt (goldenRatio + 2)`. That denominator is positive, and these vectors have squared norm one. |
| [Status, SpinLetter, spinVector, spinWeight, siteFunctional](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:50) | The alphabet is `Option IcoLetter`, including zero. U assigns mass 1/12 to each nonzero label and zero to `none`; D assigns 1/20 to each nonzero label and 2/5 to `none`. X assigns zero everywhere and is excluded by `Valid`. The site functional is the weighted sum over all thirteen labels. |
| [Weight, normalize](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:9) and [eventMass](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:47) | A weight is an arbitrary real-valued function; normalization divides by the sum over every configuration. Event mass is the finite indicator sum. Positivity is not built into these definitions. |
| [oneSiteFibre, conditionalSpinMean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesConsequences.lean:10) | Every coordinate except `x` is fixed as a letter. The conditional mean divides the three spin-coordinate indicator sums by this same event mass. |
| [localProduct, localMean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:52) | The local product is the product of `1 + dot n (a j)` over `Fin k`; the local mean divides each site-functional numerator by the common local normalizer. |

There is no missing premise. `Valid` excludes loops, so every incident factor is affine in the spin at `x`. `D.pinCount x = 0` removes every pin factor there for either Boolean setting. The other endpoint of each incident bond is fixed on the fibre and supplies one field. Every `spinVector`, including zero and zero-mass letters, belongs to the Euclidean unit ball. All site masses and all bond/pin factors are nonnegative. Consequently, the positive normalized event mass rules out a zero global partition sum and forces the off-site multiplier and local normalizer to be positive. No additional assumption of positive full-configuration weight, a moment law, or a global positivity theorem is needed. The unit-vector and nonnegativity facts are consequences of the concrete definitions, rather than unspecified laws of an abstract input.

The requested two-line proof route is:

1. Enumerate the incident-bond `Finset` by `Fin k`, use the fixed spin at each other endpoint as `a j`, and separate the fibre weight into an off-site constant times `spinWeight` times `localProduct`.
2. Reindex the fibre by `SpinLetter` using `Function.update`, obtain positive normalizers from nonnegativity and the positive event mass, and cancel the common factors coordinatewise.

Difficulty is **medium**: finite-product splitting, the dependent empty pin family, and fibre reindexing are the main formal bookkeeping. The reduction needs neither fourth-moment algebra nor the three-factor mean estimate.

Lean traps and boundary cases checked:

- Real division is total in Lean. Positivity of the event mass must be used before cancellation, together with nonnegativity of the network weights. It also supplies nonvanishing of the local denominator; merely unfolding `normalize` is insufficient.
- `SpinLetter` has thirteen labels. Do not discard `none`: it has positive D mass and zero U mass. The fixed value `σ x` is irrelevant to the fibre, so the full configuration `σ` need not itself have positive weight.
- The bond count is a `Finset.card`; the local product is indexed by the `Fintype` `Fin k`. An enumeration of bonds preserves all factors. Distinct neighbours can have equal spin vectors, so deduplicating the field values with a `Finset.image` would change the product. Symmetry of `dot` handles bonds where `x` is the second endpoint.
- `D.pinCount x = 0` makes `Fin (D.pinCount x)` empty. The dependent product then equals one, regardless of `pinned`; the hypothesis is effective and is not silently dropped.
- The configuration and spin alphabets have their standard finite instances. No arbitrary instance parameter or hidden finiteness assumption is lost. Classical decidability can be used for the indicator predicates and the finite enumeration, consistently with the definitions' `noncomputable section` and `classical` blocks.
- `normSq` is the intended Euclidean sum of squares. The default norm on the function type `Fin 3 → ℝ` should not be substituted for it. All site masses and quotients here are real; there is no natural-number division or subtraction trap.
- `k = 0` is permitted and gives the empty local product one. A one-site U or D network with no bonds or pins satisfies the premises, has event mass one and local normalizer one, and has mean zero. Thus the leaf is nonvacuous. The `n = 0` case has no `x : Fin 0`, as intended.

Numerical sanity checks in [check_fibres.py](/home/ubuntu/aklt/reports/TS_MOM_05/check_fibres.py) passed for 20 valid network/root/pin-setting cases and all 7,304 positive fibres in those cases; 2,268 zero fibres were excluded. Cases cover U/D roots, zero through three incident bonds, both endpoint orientations, neighbouring zero atoms, repeated field values, off-site bonds, and off-site pins. The maximum coordinate discrepancy was `2.22e-16`. These are floating-point checks with explicit roundoff tolerances, not formal verification; [checks.json](/home/ubuntu/aklt/reports/TS_MOM_05/checks.json) records the details. No Lean proofs were written and no Lean processes were launched. The repository was not modified.
