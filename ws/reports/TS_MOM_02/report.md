STATUS: COMPLETE

| Leaf (prefix `AKLT.Blueprint.Mom.`) | Verdict | Difficulty |
|---|---|---|
| [OrthogonalTensorStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesCore.lean:61) | TRUE | hard |
| [PolynomialExpansionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesCore.lean:84) | TRUE | medium |
| [BallDotBoundsStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesFinite.lean:11) | TRUE | easy |
| [LetterAvoidanceStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesFinite.lean:17) | TRUE | medium |
| [GreedyAssignmentStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesFinite.lean:25) | TRUE | hard |
| [FreeCoefficientsStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesFinite.lean:46) | TRUE | medium |
| [FreeDegreeStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesFinite.lean:52) | TRUE | hard |
| [TwoSiteFactorizationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesFinite.lean:84) | TRUE | medium |

All eight leaves are true as written and self-sufficient. No fixes or additional premises are needed. The verdicts are mathematical audits, not completed Lean proofs. [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_MOM_02/verdicts.jsonl) contains exactly one record per leaf.

Checked repository revision `7a3393531c12080d76aefbdab300ac0c2df834b7`. The corresponding paper arguments are [l:moments](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:35), [l:finitefacts](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:126), and [l:exact](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:297). No proofs or sub-agents were created and no repository files were modified.

The definition closure was checked as follows. The [Lean inspection log](/home/ubuntu/aklt/reports/TS_MOM_02/checks/inspect.log) preserves the elaborated statements and all the project definitions in this table.

| Definitions | Checked meaning and source |
|---|---|
| `mono`, `finiteFunctional`, `productSum`, `TensorLaw` | Coordinate-power products, actual weighted sums, dependent product alphabets, and constant/first/third/second/fourth tensor clauses: [NodesCore.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesCore.lean:14). |
| `Vec3`, `dot`, `normSq`, `UnitVector` | Three real coordinates, the sum of coordinate products, its self-product, and the subtype with squared norm one: [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9). |
| `IcoLetter`, `signValue`, `goldenRatio`, `icoRadius`, `icoVector` | Exactly twelve labels and the paper’s three signed coordinate groups divided by a positive radius: [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:23). |
| `Status`, `SpinLetter`, `spinVector`, `spinWeight` | U/D/X statuses; optional unit labels with zero at none; U masses 0 and 1/12, D masses 2/5 and 1/20: [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:50). |
| `FiniteSpinNetwork`, `.Valid`, `.weight` | Finite bonds and indexed unit pins; active statuses, strictly ordered endpoints, degree cap; product of masses, bonds and optional pins: [FiniteNetwork.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:10). |
| `dotPolynomial`, `freePolynomial`, `SeparateDegreeFour` | Formal dot products; bond factors times the entire observable list product; summed coordinate-exponent bound per site and support monomial: [NodesFinite.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesFinite.lean:36), [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:79). |
| `twoSiteFibre` | Equality with the fixed configuration outside the two named sites: [NodesFinite.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesFinite.lean:78). |
| Library polynomial and matrix operations | Natural Finsupp exponents, ordinary coefficient convolution, nonzero-coefficient support and support-sum evaluation; matrix-vector multiplication by row sums: [polynomial definitions](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Basic.lean:81), [evaluation](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Eval.lean:255), [mulVec](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean:698). |

**`OrthogonalTensorStatement` — TRUE, hard.** The functional is an actual weighted finite sum, so all required linearity follows from its definition. For square real 3 by 3 matrices, R.transpose * R = 1 also gives R * R.transpose = 1. Expanding the transformed moments and contracting rows preserves the constant, the zero odd tensors, and both scaled even tensors for arbitrary real c and signed weights.

Route 1: Derive row orthogonality from the given column identity and expand each transformed coordinate in the finite functional.  
Route 2: Commute the finite sums, substitute TensorLaw, and contract the two- and four-index Kronecker deltas.

Lean traps: The stated matrix identity contracts columns, while the moment calculation contracts rows. Justify the reverse identity for square real matrices. TensorLaw alone does not assert linearity for arbitrary functionals; the finiteFunctional definition supplies it here. The constant moment stays one, independently of c. An empty alphabet cannot meet that constant-moment premise, but the whole leaf is not vacuous: a weight-one zero-vector quadrature satisfies it with c = 0.

**`PolynomialExpansionStatement` — TRUE, medium.** MvPolynomial evaluation expands over the polynomial's actual finite support. The exponent function on Fin n times Fin 3 splits into the displayed product of site monomials, and finite distributivity gives the identity without degree, sign, normalization, or nonempty-alphabet hypotheses. Zero polynomials, zero sites, and empty site alphabets cause no exception.

Route 1: Expand eval p as the support sum of coeff m times the product of all coordinate powers, then regroup that product by site.  
Route 2: Unfold productSum, distribute its weights across the support sum, and commute the two finite sums.

Lean traps: The exponent m is a Finsupp on coordinate pairs, with zero outside its support. Passing to a product over all coordinates uses a ^ 0 = 1, including a = 0. The alphabet is dependent: the instance is (x : Fin n) → Fintype (α x). Zero sites give one empty configuration, while an empty alphabet at an existing site makes both sides zero.

**`BallDotBoundsStatement` — TRUE, easy.** dot is the Euclidean coordinate sum and normSq is the sum of three real squares. Cauchy-Schwarz and the two squared-norm bounds imply -1 <= dot a b <= 1, including zero vectors and equality at parallel or antiparallel unit vectors.

Route 1: Apply finite-sum Cauchy-Schwarz to obtain (dot a b)^2 <= normSq a * normSq b <= 1.  
Route 2: Use nonnegativity of the squared norms and real arithmetic to conclude 0 <= 1 + dot a b <= 2.

Lean traps: Vec3 is a function type; its default norm is the sup norm. Work directly with normSq or explicitly convert to EuclideanSpace before using Euclidean norm lemmas. The finite-sum squared Cauchy–Schwarz inequality avoids square roots and division.

**`LetterAvoidanceStatement` — TRUE, medium.** The explicit icoVector definition gives twelve distinct unit vectors: the radius is positive, the golden ratio is nonzero, and each group has a different zero coordinate. For a ball vector b, a unit atom a can have 1 + dot a b = 0 only when a = -b; hence each field forbids at most one label. At most four labels are forbidden, leaving at least eight. The k = 0 case simply chooses any label.

Route 1: Verify the explicit atoms are distinct and unit; use squared-distance nonnegativity to show a zero interaction forces icoVector j = -b i.  
Route 2: Bound the union of the k forbidden label sets by k <= 4 < 12, then use nonnegativity of interactions to turn avoidance of zero into strict positivity.

Lean traps: Count labels, or establish injectivity before passing to an image Finset. Unit length and injectivity follow from the explicit atoms and are not extra assumptions. Prove icoRadius > 0 before clearing its denominator. A field is allowed to lie strictly inside the ball; it then forbids no atom. Classical decidability can be used for forbidden-label Finsets.

**`GreedyAssignmentStatement` — TRUE, hard.** D.Valid bounds incident bonds plus pins by four and orders every retained bond's endpoints strictly, excluding loops and reversed duplicates. Assign sites in increasing Fin n order, using the local feasibility hypothesis on the pins and previously assigned neighbours. The generic vector premise bounds neighbour fields, UnitVector bounds pins, and dot symmetry handles their displayed order. Local feasibility at k = 0 already forces alpha to be nonempty; no Inhabited premise is missing.

Route 1: Maintain a partial assignment along the order on Fin n; enumerate the current site's pins and earlier-neighbour fields by Fin k with k <= 4.  
Route 2: Apply local feasibility to extend it, preserving earlier factors; every bond becomes positive when its later endpoint is assigned, and every pin is handled at its own site.

Lean traps: The k = 0 instance of local feasibility yields a letter, so no Nonempty or Inhabited premise is missing. The Fintype α binder is retained even though the argument needs no enumeration of α. Use the UnitVector subtype property for pins and dot symmetry to match argument order. Enumerate pins together with earlier neighbours, preserve multiplicity of pins, and handle n = 0 with the empty assignment.

**`FreeCoefficientsStatement` — TRUE, medium.** The polynomial uses only 1, coordinate variables, sums, and products. All generator coefficients are nonnegative and finite coefficient convolution preserves nonnegativity. This holds for every network, including invalid networks with bond loops, and for repeated or coincident-endpoint observable pairs; status and pins are absent from freePolynomial.

Route 1: Establish closure of nonnegative coefficients under addition and multiplication using the finite coefficient convolution formula.  
Route 2: Apply it to each coordinate variable, each dotPolynomial, the bond product, and the List product with all repeated factors retained.

Lean traps: Bonds are a Finset but observable pairs form a List; repeated observable factors remain repeated. Colliding terms add coefficients and preserve nonnegativity. This leaf needs neither active statuses nor valid bonds: status and pins do not occur in freePolynomial. The zero-site polynomial with an empty observable list is 1.

**`FreeDegreeStatement` — TRUE, hard.** For any support monomial, its total exponent at site x is bounded by the number of incident distinct-endpoint bonds plus the number of observable endpoint appearances at x. Valid supplies e.1 < e.2, so each incident bond contributes at most one. The two List filters count an observable loop twice and retain repeated pairs. The stated sum is therefore exactly a sufficient sitewise degree budget, bounded by four.

Route 1: Propagate sitewise exponent bounds through support of sums and products, using additivity of the sum of the three coordinate exponents.  
Route 2: Bound a bond factor by its incident indicator and a dot observable by both endpoint indicators; sum these bounds and apply the displayed budget.

Lean traps: SeparateDegreeFour sums the three coordinate exponents at each site; bounding each coordinate separately would be insufficient. Valid excludes bond loops via e.1 < e.2. Both List filters are necessary: a coincident-endpoint observable contributes twice, and repeated pairs retain their multiplicity. Pins are absent from the free polynomial and from this extra observable budget.

**`TwoSiteFactorizationStatement` — TRUE, medium.** With x distinct from y and both bond orientations excluded, every factor of D.weight depends on at most one of the two free letters. Allocate all off-site masses, pins, and bonds to C, and each on-site mass and incident pin or bond to u or v. The explicit spin vectors are in the unit ball, pins are unit, and active site weights are nonnegative, so every allocated factor is nonnegative. Zero masses and zero off-site factors are allowed: no normalization or division is needed.

Route 1: Partition the factors in weight into those involving x, those involving y, and those involving neither, substituting sigma at every off-site endpoint.  
Route 2: Define C, u, and v by these products; use ball interaction bounds for nonnegativity and the fibre equalities to reassemble weight.

Lean traps: The same C, u and v must work for every τ on the fibre. Define them as products without division or cancellation. C can vanish; at a U site the none label has zero mass, while its spin vector is still in the ball. Both missing-bond orientations are explicitly assumed. No positive event mass or conditional normalization is needed here. The explicit unit-atom geometry supplies the norm bound for every SpinLetter value.

All expected Fintype binders, including the dependent product instance, survived elaboration; there is no silently dropped instance. Classical choice or decidability may be used inside proofs for arbitrary alphabets, coefficient supports and finite witness selection. Coefficients, scales and displayed fractions are real, with no rational-cast mismatch or natural-number subtraction. The only potentially delicate geometric denominator is icoRadius, which is strictly positive.

None of the eight whole leaves is vacuous. Some parameter choices make antecedents impossible, such as an empty alphabet in the orthogonal-tensor or greedy leaf, but other choices satisfy them. A singleton alphabet with vector zero satisfies greedy feasibility; a two-site edgeless valid network gives a nontrivial instance of the factorization statement. The n = 0 and k = 0 cases elsewhere have the intended empty-product meanings.

Verification imported a single existing module with Lean `v4.35.0-rc2` and printed the exact leaves and their project definitions. [Inspect.lean](/home/ubuntu/aklt/reports/TS_MOM_02/checks/Inspect.lean) exited successfully; no leaf proofs or whole-repository builds were attempted. The verdicts follow from the definitions and the paper arguments.

[Selected sanity checks](/home/ubuntu/aklt/reports/TS_MOM_02/checks/sanity_checks.py) cover 1,815 tensor moments for signed laws under the identity, a rotation and a reflection; five exact rational polynomial expansions including empty-site and empty-alphabet cases; 625 ball-vector pairs; all 794 subsets of at most four antipodal fields; 1,100 simple graphs on at most five sites with pins filling their degree budgets; 106 exact integer polynomial expansions, including loops and repeated observables; and 1,690 two-site letter choices including zero-weight fibres. They passed. [sanity_results.json](/home/ubuntu/aklt/reports/TS_MOM_02/checks/sanity_results.json) records counts and numerical residuals. Polynomial checks use exact arithmetic; geometric checks use floating-point tolerances and are edge-case checks rather than proofs.
