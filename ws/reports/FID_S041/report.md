STATUS: PASS
BLOCKING: 0

DECL: icoSet PASS

Paper: `sec2-moments.tex:8–18` (Definition `d:moment`), with distinctness and normalization explained at `sec2-moments.tex:55–61`. Lean: `AKLT/Defs/Moment.lean:23–44`.

`IcoLetter = Fin 3 × (Fin 2 × Fin 2)` has exactly twelve elements. The first component selects, in the paper's order, `(0,a,b)`, `(a,b,0)`, or `(b,0,a)`. Each `Fin 2` component independently selects a sign: index zero gives +1 and index one gives −1. Thus `a = ±1` and `b = ±φ`, without identifying or correlating the signs. Mathlib's `![a,b,c]` is a function on `Fin 3` with those entries in that order (`Mathlib/Data/Fin/VecNotation.lean:52–77`); coordinates 0,1,2 correspond to the paper's coordinates 1,2,3.

`goldenRatio` and `icoRadius` are precisely `(1 + √5)/2` and `√(φ + 2)` in ℝ, and division is coordinatewise division by this latter scalar. Mathlib's `Real.sqrt` is the nonnegative square root, returning zero on negative inputs (`Mathlib/Analysis/Real/Sqrt.lean:109–113,144–150,286–287`). Here both radicands are strictly positive, so `φ > 0` and `r > 0`: totalized division cannot collapse the vectors to zero. The identities `φ² = φ + 1` and `r² = φ + 2 = 1 + φ²` give squared Euclidean norm one. Each group has a different unique zero coordinate; within a group the two nonzero coordinates determine both signs. Consequently the twelve labels have twelve distinct images.

Mathlib's `Finset.univ` contains every label exactly once (`Mathlib/Data/Fintype/Defs.lean:53–61,88–97`). `Finset.image` forms the image with duplicates removed, using actual equality of the target vectors (`Mathlib/Data/Finset/Image.lean:276–294`). Since the map is injective, no points are lost. This is exactly the paper's finite set D; it neither requires nor asserts finiteness of all of ℝ³. The product enumeration and cardinalities are the ordinary ones (`Mathlib/Data/Fintype/Prod.lean:42–58`; `Mathlib/Data/Fintype/Card.lean:497–498`).

DECL: moment PASS

Paper: `sec2-moments.tex:8–19`, especially the formula at line 14. Lean: `AKLT/Defs/Moment.lean:46–47`.

The argument is an arbitrary real-valued function on the three real coordinates, exactly as in the paper's finite functional. The expected type forces `1 / 12` to be real field division, not natural-number division; the denominator is the nonzero real number twelve. The whole finite sum is multiplied by this coefficient. Mathlib's typed sum `∑ j : IcoLetter, ...` means a `Finset.sum` over `Finset.univ`, not a conditional or infinite sum (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:59–69,125–130`).

Although Lean sums over labels and the paper sums over D, the injectivity established above makes the sums equal for every function f, not merely for polynomials. This is precisely the reindexing justified by Mathlib's `Finset.sum_image` (`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:90–97`, the additive version of `prod_image`). There is no multiplicity discrepancy or missing normalization: `moment (fun _ => 1) = 12/12 = 1`. Defining the functional on arbitrary functions adds no covariance assertion; the paper likewise restricts orthogonal covariance to degree-four polynomials (`sec2-moments.tex:46–52`). No hypotheses, quantifier restrictions, or analytic integrability assumptions have been inserted.

DECL: Status PASS

Paper: `sec6-walks.tex:8–17,25–36` (Definition `d:domain`). Lean: `AKLT/Defs/Moment.lean:49–54`.

This inductive type has exactly the three distinct, argument-free constructors U, D, and X. It matches the paper's three statuses, with no scalar trace mass or extra status parameter. `DecidableEq` decides equality and `Repr` supplies printing; neither changes the mathematical values. The explicit `Fintype` instance enumerates `{U,D,X}` and proves completeness by cases, which is exactly Mathlib's finite-type requirement (`Mathlib/Data/Fintype/Defs.lean:53–61`).

The intended meanings are realized by the consumers: U receives the uniform twelve-point law; D receives its 3/5 mixture with a zero atom (`Moment.lean:67–73`); X is excluded from `Network.active` and therefore from the product of spin variables (`AKLT/Defs/Domain.lean:14–16,58–70`). Kept bonds, protected-site requirements, and degree restrictions belong to network predicates rather than the status alphabet (`Domain.lean:33–55`), matching the paper's separation of these data. In particular X is a removed site, not the zero spin of a D site.

DECL: SpinLetter PASS

This is an auxiliary encoding of the supports specified at `sec2-moments.tex:16–19` and `sec6-walks.tex:25–26`. Lean: `AKLT/Defs/Moment.lean:56–58`, used at lines 61–73 and 83–86.

`Option IcoLetter` has one `none` and one distinct `some j` for each of the twelve labels: thirteen elements. Mathlib's option `Fintype` explicitly adjoins `none` to the images of all old elements, and its cardinality is the old cardinality plus one (`Mathlib/Data/Fintype/Option.lean:29–42`). It introduces no identification of labels or unspecified spin value.

The common alphabet is faithful even though the paper uses D alone at U sites. The extra `none` term has weight zero there; each `some j` has weight 1/12. At D sites `none` has weight 2/5 and each `some j` has weight 1/20 = (3/5)(1/12). Hence the weighted sums are exactly the two paper laws and both have mass one. Summing over `Option` separates the extra atom and the old atoms (`Mathlib/Algebra/BigOperators/Option.lean:26–28`, additive version). All observables here are real-valued, so the zero-weight terms vanish without any undefined product. Finite products enumerate genuine finite function spaces (`Mathlib/Data/Fintype/Pi.lean:133–142`); the additional zero-weight configurations do not change the paper's partition sums. X sites are omitted as described above.

DECL: spinVector PASS

This auxiliary evaluation map realizes the geometric atoms in `sec2-moments.tex:12–18` and the supports at `sec6-walks.tex:25–26`. Lean: `AKLT/Defs/Moment.lean:60–63`.

The two exhaustive branches send `none` to the origin and `some j` to exactly the normalized icosahedron vector indexed by j. For `Vec3 = Fin 3 → ℝ`, Mathlib's zero is pointwise zero (`Mathlib/Algebra/Notation/Pi/Defs.lean:40–46`, additive instance), so the first branch is `(0,0,0)`. The other branch introduces no rotation, sign change, or rescaling beyond the paper's normalization already checked for `icoSet`. Since those twelve vectors have norm one, none equals the origin; the map is a bijection between its thirteen labels and `D ∪ {0}`. Combined with `spinWeight`, it pushes the finite label sums forward to exactly λ_U and λ_D. Euclidean squared norms in this file are explicitly `dot a a`, not an implicit norm on the function type.

Non-blocking remarks:

- Read all of `Moment.lean` and its local import `Geometry.lean`, and checked the relevant Mathlib definitions and downstream uses. Verdicts concern only the five assigned declarations.
- An exact Python check in ℚ(√5), using the twelve displayed unnormalized vectors and `r² = φ + 2`, confirmed distinctness, unit normalization, antipodality, all 35 coordinate monomials of total degree at most four, thirteen distinct atoms after adding zero, and both probability normalizations. No floating-point approximation or Lean process was used.
- None of the five declarations uses ℕ subtraction, a variable denominator, an infinite sum, or a potentially empty alphabet. No blocking or non-blocking fidelity discrepancy was found. Inputs were not modified.
