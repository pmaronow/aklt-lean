STATUS: COMPLETE

| Leaf | Verdict | Difficulty | Finding |
|---|---|---|---|
| [AKLT.Blueprint.H1.PauliHermitianStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesStructure.lean:11) | TRUE | easy | Real scalar combinations of Hermitian tensor factors. |
| [AKLT.Blueprint.H1.ReflectionParityStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesStructure.lean:16) | TRUE | medium | The y reflection kills the selected odd-y coefficients. |
| [AKLT.Blueprint.H1.PauliRealityStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesStructure.lean:22) | TRUE | medium | Even-y tensor terms are real; the other terms vanish. |
| [AKLT.Blueprint.H1.InversionCovarianceStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesStructure.lean:29) | TRUE | easy | Each token sign commutes with every real linear rotation. |
| [AKLT.Blueprint.H1.AdjointPauliCoordinatesStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesStructure.lean:35) | TRUE | medium | Conjugated Pauli matrices have real traceless Hermitian coordinates. |
| [AKLT.Blueprint.H1.AdjointPauliOrthogonalStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesStructure.lean:43) | TRUE | medium | The half-trace pairing gives orthonormal columns of R. |
| [AKLT.Blueprint.H1.PauliRotationTransferStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesStructure.lean:52) | TRUE | hard | Tensor conjugation matches substitution by the transposed rotation. |
| [AKLT.Blueprint.H1.CayleyTensorCommutationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesStructure.lean:62) | TRUE | medium | Positive normalization yields an SU(2) matrix; tensor scaling clears it. |

All eight leaves are true as written and self-sufficient for the paper’s argument. No missing premise, counterexample, or unintended vacuity was found. No statement correction is required. The optional simplifications recorded below remove redundant hypotheses.

Audited repository: `/home/ubuntu/aklt/repo`, branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The repository was read only and its working tree is clean. The source of all eight leaves is [NodesStructure.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesStructure.lean:11). The paper comparison used [d:Pauli and its coefficient discussion](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:248) and [l:Ostruct and its proof](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:320). The label text was checked directly; some numeric line ranges in Lean docstrings refer to an earlier layout.

The project definitions were traced as follows. Here x(j,k) is a scalar coordinate variable, σ and τ are functions J → Fin 2, and a is a function J → Fin 4.

| Definition | Exact meaning relevant to the leaves | Source |
|---|---|---|
| `VectorPolynomial` | MvPolynomial (Fin 20 × Fin 3) ℚ: genuine formal polynomials in 60 variables, with rational coefficients. | [Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/Definitions.lean:14) |
| `Vec3` | Fin 3 → ℝ, with scalar coordinate indices 0, 1, 2. | [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9) |
| `VectorAffine` | For every m in p.support and token j, ∑ k : Fin 3, m(j,k) ≤ 1. This bounds the total degree in each whole vector. | [Operator.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:117) |
| `SupportedVectors` | For every supported exponent m, each j outside J has m(j,k) = 0 for all k. | [OperatorContracts.lean](/home/ubuntu/aklt/repo/AKLT/Defs/OperatorContracts.lean:36) |
| `OrthogonalInvariant` | For every real 3 by 3 R with R.transpose * R = 1 and every u : Fin 20 → Vec3, evaluateReduced p (j ↦ R.mulVec(u j)) = evaluateReduced p u. | [Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/Definitions.lean:46) |
| `evaluateReduced` | MvPolynomial.eval₂ (Rat.castHom ℝ) (v ↦ u v.1 v.2) p. | [FiniteNetwork.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:59) |
| `invertPolynomial` | eval₂Hom C substitutes (if j ∈ I then -1 else 1) * X(j,k) for each X(j,k). The same sign multiplies all three coordinates of one token. | [Operator.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:121) |
| `pauliExponent` | The exponent at (j,k) is 1 exactly when j ∈ J and (a j).val = k.val + 1; it is 0 otherwise. Finsupp.equivFunOnFinite.symm packages precisely this function. | [Operator.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:132) |
| `pauli` | Labels 0,1,2,3 are I, [[0,1],[1,0]], [[0,-i],[i,0]], [[1,0],[0,-1]], respectively. | [Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:53) |
| `pauliOperator` | Its (σ,τ) entry is ∑ a : J → Fin 4, (p.coeff(pauliExponent J a) : ℂ) * ∏ j : J, pauli(a j)(σ j)(τ j). | [Operator.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:137) |
| `pauliYCount` | The cardinality of Finset.univ.filter (j ↦ a j = 2), with univ ranging over the subtype J. | [Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/Definitions.lean:158) |
| `tensorPowerMatrix` | Its (σ,τ) entry is ∏ j : J, g(σ j)(τ j). There is no assumed representation theorem in this definition. | [OperatorContracts.lean](/home/ubuntu/aklt/repo/AKLT/Defs/OperatorContracts.lean:79) |

The auxiliary reflection [reflectY](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/Definitions.lean:161) is exactly diag(1,-1,1). For the real coefficient extension needed in rotation transfer, [realPauliOperator](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/Definitions.lean:135) is already defined by the same coefficient formula with real coefficients. The data substitution [invertVectors](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:68) is j ↦ if j ∈ I then -u j else u j.

Standard Lean definitions were also checked: a Matrix is an indexed function; multiplication is finite matrix multiplication; mulVec is multiplication by a column vector; transpose swaps row and column; conjTranspose adds entrywise complex conjugation; IsHermitian means conjTranspose M = M; Commute M T means M * T = T * M. A polynomial coefficient is indexed by a finitely supported natural exponent, its support consists of nonzero coefficients, and eval₂Hom is simultaneous ring-homomorphic substitution. Odd n has its ordinary natural-number meaning. No definition here represents an invariant function only on a sphere, a quotient polynomial ring, or a restricted rotation group.

Each leaf’s reason, two-line proof route, and implementation traps follow. These are routes for the future writer; no proofs were written.

**AKLT.Blueprint.H1.PauliHermitianStatement — TRUE; easy.**

pauliOperator is a finite sum of rational (hence real) multiples of entrywise tensor products of the four standard Hermitian Pauli matrices. Conjugating and exchanging the row and column functions fixes every summand. This holds for arbitrary p because the definition only selects the Pauli exponents. For empty J the operator is the 1 by 1 matrix with entry p.coeff 0.

Fix: None. VectorAffine and SupportedVectors are unnecessary for this particular conclusion.

Proof route:

1. Check conjugate symmetry of pauli a for each a : Fin 4.
2. Expand pauliOperator entrywise and distribute conjugation through its finite sum and product, using that rational casts are fixed by conjugation.

Lean traps: Use conjugate symmetry of the tensor entries. The factors are scalar entries in a finite product, so this does not require a false general rule that arbitrary products of Hermitian matrices are Hermitian. The rational coefficient cast to complex is fixed by conjugation.

**AKLT.Blueprint.H1.ReflectionParityStatement — TRUE; medium.**

OrthogonalInvariant quantifies over every real orthogonal matrix and every real vector assignment, not just unit vectors. Specializing to diag(1,-1,1) gives an equality of polynomial functions on all 60 real coordinates, hence equality of their coefficients after the injective rational-to-real cast. At pauliExponent J a the sign is (-1)^(pauliYCount J a), because label 2 corresponds exactly to coordinate 1. Odd count forces c = -c and therefore c = 0. The affineness and support hypotheses suffice and are in fact stronger than needed for this selected-coefficient conclusion.

Fix: None. Optional simplification: VectorAffine and SupportedVectors can be omitted from this leaf.

Proof route:

1. Use reflectY in OrthogonalInvariant and polynomial-function extensionality over the infinite field of reals to compare coefficients.
2. Compute the reflected monomial sign at pauliExponent J a as (-1)^(pauliYCount J a); oddness and characteristic zero force the rational coefficient to vanish.

Lean traps: The Pauli label 2 selects coordinate 1 of Fin 3, and pauliYCount counts exactly those subtype tokens. Uncurry u : Fin 20 → Vec3 to an arbitrary assignment of all 60 scalar variables before applying polynomial extensionality. Compare real coefficients after mapping the rational polynomial, then use injectivity of the rational cast. Full orthogonal invariance includes reflectY, whose determinant is -1.

**AKLT.Blueprint.H1.PauliRealityStatement — TRUE; medium.**

Entrywise complex conjugation fixes Pauli factors 0, 1 and 3, and negates precisely factor 2. A tensor summand is thus multiplied by (-1)^(pauliYCount J a). Odd-count summands vanish by the explicit premise; even-count summands and their rational coefficient are fixed by conjugation, so every entry has zero imaginary part. Empty J gives a real scalar.

Fix: None.

Proof route:

1. For each a, compute the conjugate of its tensor entry as (-1)^(pauliYCount J a) times that entry.
2. Split on parity, use the zero-coefficient premise in the odd case, and sum the conjugation-fixed terms.

Lean traps: Complex conjugation of a product is the product of its conjugates; the imaginary part of a product is not the product of the imaginary parts. Two sigma_2 factors can give a nonzero real tensor entry. Count the factors with pauliYCount rather than counting nonzero matrix entries.

**AKLT.Blueprint.H1.InversionCovarianceStatement — TRUE; easy.**

invertPolynomial substitutes the scalar sign -1 or 1 in front of every coordinate belonging to a given token. evaluateReduced therefore evaluates p at the tokenwise signed vectors. A real linear matrix action commutes with each of these scalar signs, so OrthogonalInvariant p applies to the signed assignment. No support, degree, or containment assumption on I is needed.

Fix: None. In particular I need not be contained in a support set.

Proof route:

1. Establish evaluation/substitution compatibility for invertPolynomial directly from eval₂Hom.
2. Commute each token sign through R.mulVec and apply the supplied invariance of p.

Lean traps: The signs in invertPolynomial live in the rational polynomial ring before evaluation. Establish the eval₂Hom composition identity with Rat.castHom ℝ explicitly. The predicate quantifies over all 20 vectors; no restriction to J or unit vectors is implicit.

**AKLT.Blueprint.H1.AdjointPauliCoordinatesStatement — TRUE; medium.**

For every j the conjugate A_j = g * pauli (j+1) * g.conjTranspose is Hermitian, and cyclicity of trace plus g.conjTranspose * g = 1 makes it traceless. Every traceless Hermitian 2 by 2 matrix has real Pauli coordinates (Re A_01, -Im A_01, Re A_00). Taking those coordinates as column j defines the single real matrix R required by the existential before all j. The determinant-one hypothesis is redundant.

Fix: None. Optional strengthening: omit g.det = 1.

Proof route:

1. For each j establish that its conjugated Pauli matrix is Hermitian and traceless.
2. Set column j of R to (Re A_j[0,1], -Im A_j[0,1], Re A_j[0,0]) and use the four entries to obtain the required expansion.

Lean traps: For a traceless Hermitian A, the sigma_2 coefficient is -Im(A 0 1), not +Im(A 0 1). Construct the whole matrix R with these vectors as columns, respecting ∃ R, ∀ j. If a right-unitary identity is used, derive it from the given left-unitary identity for this finite square matrix; it is not an additional assumption.

**AKLT.Blueprint.H1.AdjointPauliOrthogonalStatement — TRUE; medium.**

The given conjugation expansion and g.conjTranspose * g = 1 preserve the bilinear half-trace pairing of the three Pauli matrices. Its value is delta_ij, so sum_l R[l,i]*R[l,j] = delta_ij, exactly the entries of R.transpose * R = 1. Real coefficients are supplied by the type of R, and no determinant-one or orientation hypothesis is needed.

Fix: None. g.det = 1 is not a missing premise.

Proof route:

1. Calculate Tr((g sigma_i g*) (g sigma_j g*)) = Tr(sigma_i sigma_j) = 2 delta_ij using the supplied left-unitary identity and cyclic trace.
2. Insert the supplied real Pauli expansions, use the Pauli trace table, and cancel 2 to identify each entry of R.transpose * R.

Lean traps: The supplied expansion has coefficients R l j, so the pairing gives column dot products, exactly R.transpose * R. Cast the real entries into complex, cancel the nonzero complex scalar 2, and descend back through the injective real-to-complex cast. A determinant-one assumption is unnecessary.

**AKLT.Blueprint.H1.PauliRotationTransferStatement — TRUE; hard.**

VectorAffine and SupportedVectors identify the complete polynomial expansion with precisely the pauliExponent J a monomials used by pauliOperator. If T = tensorPowerMatrix J g, expanding the supplied adjoint coordinates gives T O(p) T* = O(p composed with tokenwise R.transpose), with the latter expansion interpreted over real coefficients. Since the real square matrix R satisfies R.transpose * R = 1, its transpose is also orthogonal, so the stated evaluation invariance makes the transformed polynomial equal to p. Finite-square unitarity supplies g * g.conjTranspose = 1 and T* T = 1, yielding the requested commutator. No determinant or spin-representation premise is missing.

Fix: None.

Proof route:

1. Derive the supported vector-affine coefficient expansion and the tensor conjugation/substitution identity directly from the supplied Pauli coordinates, extending coefficients from rationals to reals.
2. Apply OrthogonalInvariant at R.transpose, use polynomial-function extensionality, and multiply the conjugation identity by T to obtain O(p) T = T O(p).

Lean traps: An arbitrary real rotation can produce irrational coefficients, so polynomial substitution cannot be kept inside VectorPolynomial over ℚ. Map coefficients to ℝ and use the existing realPauliOperator or the identical finite coefficient formula. With the stated R l j convention, the polynomial substitution is R.transpose.mulVec. Derive R * R.transpose = 1 to apply invariance at R.transpose, and derive g * g.conjTranspose = 1 for the identity Pauli factor. The finite tensor multiplication identity uses sums over the whole function type J → Fin 2.

**AKLT.Blueprint.H1.CayleyTensorCommutationStatement — TRUE; medium.**

For A = I - i t sigma_j, the explicit Pauli matrices give A* A = (1+t^2) I and det A = 1+t^2. The real scalar s = sqrt(1+t^2) is strictly positive for every real t, so g = s^(-1) A is unitary with determinant one and is covered by the hypothesis. The definition gives tensorPowerMatrix J A = (s:complex)^(J.card) times tensorPowerMatrix J g, and scalar multiplication preserves commutation with arbitrary M. This also works for t = 0 and empty J, where the tensor power is the 1 by 1 identity.

Fix: None. No extra premise about M, t, or nonemptiness of J is needed.

Proof route:

1. Check the numerator identities for each of the three explicit Pauli matrices, then normalize by s = sqrt(1+t^2) > 0 to apply the SU(2) commutation premise.
2. Pull s out of each tensor entry, obtaining the scalar power s^(J.card), and scale the resulting commutation equality.

Lean traps: Take the square root in ℝ, prove it positive, then cast to ℂ; complex division does not itself record a nonzero denominator. Scaling the 2 by 2 determinant uses s², while scaling the tensor entries uses s^(J.card). Do not encode the paper’s half exponent as J.card / 2 in ℕ: use (sqrt(1+t²))^(J.card). The stated expression contains no natural-number division.

**Shared instance, coercion, and edge-case checks.**

The compiled declarations are closed propositions with exactly the stated quantifiers. There are no extra section variables or silently dropped instance hypotheses. The coercion of a Finset J to a type is its membership subtype, and its Fintype instance is available; the function types J → Fin 2 and J → Fin 4 therefore have their own finite instances. The finite sums and products range over those complete types. Classical reasoning may be used for function equality, supports, and finite-sum manipulation without adding a mathematical premise.

All rational-to-real and rational/real-to-complex casts are the usual injective characteristic-zero casts. In particular, real equality of polynomial evaluations supports coefficient comparison after scalar extension. The index j.val + 1 in the adjoint and Cayley leaves is always 1, 2, or 3, with the explicit bound proved by omega. The definition of pauliExponent uses no natural subtraction. The unrelated helper pauliCoordinate only subtracts 1 after excluding label 0.

For J = ∅, the type J → Fin 2 has one element; it is not empty. Likewise there is one a : J → Fin 4. Its exponent is 0, its y count is 0, and each empty product equals 1. Hence pauliOperator is the 1 by 1 real scalar p.coeff 0 and tensorPowerMatrix is the 1 by 1 identity. The odd-count premise is locally empty only in this intended boundary case. The leaves as universal assertions are not vacuous: constant polynomials and nonzero dot-product polynomials supply compatible data, and g = I is a valid unitary.

In the rotation leaf both VectorAffine and SupportedVectors ensure the selected coefficients reconstruct the entire polynomial; neither is silently inferred from the operator definition. In the Hermitian and reality leaves, the definition is allowed to select those coefficients from any polynomial, which is why those leaves need no support or degree premise. In the reflection leaf the two supplied structural hypotheses are redundant. Inversion needs no containment condition on I. The adjoint coordinate leaf does not need det g = 1; the orthogonality leaf correctly omits it.

**Verification performed.**

The single-module scratch [Inspect.lean](/home/ubuntu/aklt/reports/TS_H1M_06/scratch/Inspect.lean) was run with Lean 4.35.0-rc2 and the repository’s existing compiled imports and linked package tree. It exits successfully and contains only #print, #print axioms, and #check commands. The [inspection log](/home/ubuntu/aklt/reports/TS_H1M_06/scratch/lean-inspection.log) confirms the elaborated binders and the availability of polynomial extensionality and the finite-square inverse identity. The declaration dependencies contain only propext, Classical.choice, and Quot.sound; this inspection concerns the statement definitions, not proofs of the propositions.

The supplemental [exact arithmetic script](/home/ubuntu/aklt/reports/TS_H1M_06/scratch/exact_checks.py) uses fractions.Fraction for Gaussian rational entries, without floating point. Its [results](/home/ubuntu/aklt/reports/TS_H1M_06/scratch/exact-checks.json) record: all 85 Pauli words on zero through three slots satisfy the expected Hermitian and conjugation-sign identities; 64 exponents on noncontiguous tokens {2,7,19} are distinct and have the correct y count; five unitary matrices, including one of determinant -1, give the stated coordinates and orthogonality; 20 invariant tensor commutators and 60 Cayley tensor scaling/commutator cases pass. An arbitrary noninvariant polynomial distinguishes R.transpose substitution from the incorrect R substitution. Reflection and tokenwise inversion checks include zero through three slots.

These finite checks corroborate indexing, signs, normalization, and boundary cases. The truth verdicts rest on the definition analysis and the proof routes above. No repository files were changed, no proofs were created, and no sub-agents were launched.
