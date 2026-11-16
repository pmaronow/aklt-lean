STATUS: PASS
BLOCKING: 0

Reviewed `AKLT/Defs/Operator.lean` in full, its local import closure (`Pattern`, `Trails`, `Domain`, `PinModel`, `Moment`, `Geometry`, and `Frame`), and the relevant consumers in `OperatorContracts.lean` and `Blueprint/Top/Operator.lean`. Lean paths below are relative to the supplied `lean/` directory; paper paths are relative to the supplied `paper/` directory. Mathlib paths are relative to the permitted `Mathlib/` directory. Judgments concern the five assigned declarations.

DECL: contractSpins PASS

This auxiliary definition implements the coefficientwise finite product moment contraction used in `app-local-operator.tex:634–687`, especially the local moment table at lines 634–650 and factorization at lines 683–687. The underlying laws and their degree-four moments are specified in `sec2-moments.tex:8–19,35–52`.

For an exponent function `m`, the output exponent at vector coordinate `(j,k)` is exactly `m (.inr (j,k))`. Mathlib's `Finsupp.comapDomain` composes the exponent function with its argument map (`Data/Finsupp/Basic.lean:503–519`); the supplied proof uses the injectivity of `Sum.inr`. Thus it restricts to vector exponents without identifying different vector coordinates. The scalar coefficient is the original coefficient multiplied by one status moment for each spin in `V`. Terms giving the same remaining monomial add in the polynomial ring, as required by linearity of finite integration. `MvPolynomial.monomial` constructs the specified coefficient and exponent (`Algebra/MvPolynomial/Basic.lean:92–101`), and `p.support` contains precisely the exponents with nonzero coefficients (lines 461–463,513–514).

The helpers at `Operator.lean:69–78` give constant moment 1, degree-two diagonal moment 1/3, degree-four pure moment 1/5, degree-four mixed-even moment 1/15, and zero for the remaining monomials through degree four. For D, each positive-degree value is multiplied by 3/5, giving respectively 1/5, 3/25, and 1/25; the constant remains 1. These are exactly the paper's moments, including the zero atom's effect on the constant.

The actual callers use only U/D sites in `V`, contain no internal variable outside `V`, and have spin degree at most four. For `originalPatternPolynomial` this follows from the covered template's factor counts (`sec6-walks.tex:521–528`); for `reducedPolynomial` it follows from the replacement analysis below. Consequently the finite moment table suffices for every contracted monomial. All sums and products are finite despite `Plane = ℤ × ℤ`; polynomial support and `V` supply the finite index sets. Empty products give 1 and the zero polynomial has empty support, with the intended results.

DECL: reducedIntegrand PASS

This is the polynomial integrand implementing Definition `d:reduction`, `app-local-operator.tex:146–168`, before the passage spin is summed. The template and original current/next conventions are `sec6-walks.tex:488–516`; the replacement radii are justified in `app-local-operator.tex:87–96`.

The retained set `V` deletes all tips, zero-bond corners, and precisely the one-bond corners selected for replacement in the reduced representation. A removed X site cannot enter `V`. The groups consist of bonded tips and bonded corners; a bonded site is active because `PatternData.bonds` excludes X endpoints. Tips have at most one internal bond. Each single replacement therefore has one unique internal neighbour, which is a retained passage-neighbour site. No two tips or corners are adjacent. The list order and default in `leafNeighbour` cannot affect these uses.

The first product retains each bond between retained spins once. `internalBonds` uses only east/north orientations (`Geometry.lean:46–51`), so reversing an unoriented bond does not duplicate it. The unordered endpoint-set test deletes exactly the passage out-bond when `next = true`. Replaced leaf bonds disappear from this product and are restored as single replacement factors in the second product. Retained corners receive both slot factors and keep their bond factors. Isolated periphery sites contribute no group or factor, matching deletion of their common positive normalizers.

Each single factor is `1 + radius * dot(neighbour, vector)`, with exact rational radius 3/5 for tips, 1/2 for U corners, and 1/3 for D corners. Each retained pair has its two original slot indices. Leaders are 0,2,4,6 for corners and 8,11,14,17 for tips; second indices are used only for corner pairs, where they are 1,3,5,7. Thus the `min 19` totalization never clamps a used pair index, and groups have disjoint tokens. The unused original slot coordinates simply do not occur. This embeds the paper's list of k remaining vectors in the fixed twenty-token polynomial ring without changing its meaning.

`formalDot` is the sum of the three coordinate products, using `MvPolynomial.X` as formal variables. Commutativity makes its argument order agree with the paper's scalar products. All interaction signs are positive. The polynomial is defined for arbitrary vector coordinates, with no norm or realizability condition, exactly as required at `app-local-operator.tex:166–168`. Rational division has its field meaning, so none of the radii is rounded or zero.

DECL: reducedPolynomial PASS

This reconstructs the two reduced partition polynomials of `app-local-operator.tex:154–168`. It also agrees with their explicit descriptions as T[WI] and T[WJ] at lines 610–632.

The contraction uses exactly the retained spins, their original status laws, and the integrand just checked. The passage remains in `V`, has current law U, and has next law D. All other retained laws are unchanged. Summing the passage's at most three current bond factors gives `I = 1 + (P_fg + P_fo + P_go)/3`. For next, the deleted out-bond leaves at most two factors, and the D second moment gives `J = 1 + P_fg/5`. Missing neighbours omit the corresponding terms. These are precisely `app-local-operator.tex:22–58`. No replacement factor involves the passage, so summing the passage after the leaf replacements gives the same polynomial as the paper's order of finite summation.

Every retained corner has at most two bonds plus two slots. A replacement contributes one factor at its retained neighbour in place of its former bond. Passage-neighbour sites consequently have at most four factors, and the passage has at most three, or two for next. Thus all inputs to the moment table have degree at most four. Retained isolated non-periphery spins contribute moment 1, expressly permitted at `app-local-operator.tex:630–632`.

The coefficients are exact rationals. `evaluateReduced` evaluates through `Rat.castHom ℝ` (`FiniteNetwork.lean:58–60`); Mathlib's cast is injective and preserves ring operations and division (`Data/Rat/Cast/CharZero.lean:37–64`). Hence this representation gives the same real polynomial, with no coefficient loss, normalization division, or hidden positivity hypothesis. The relevant interface statements explicitly assume `π.Covered` (`Blueprint/Top/Operator.lean:48–59`), supplying the paper's covered-pattern domain.

DECL: reducedDifference PASS

Definition `d:reduction` sets `F̂_c = Ẑ_cur - c Ẑ_next` (`app-local-operator.tex:154–156`), with the original difference fixed at lines 7–10. `false` selects current and `true` selects next throughout the checked definitions. Mathlib's `MvPolynomial.C c` is the constant polynomial (`Algebra/MvPolynomial/Basic.lean:104–106`); multiplying by it multiplies each coefficient by c (line 646). The subtraction therefore has exactly the stated order, sign, and threshold scale.

The parameter `c : ℚ` implements the exact rational thresholds used in the certificate construction (`app-local-operator.tex:580–590`); casting its result to real coordinates gives the paper's difference at that threshold. The definition extends algebraically to all rational c, while the paper's applicable range `0 < c < 1` is explicit in its consumers (`Blueprint/Top/Operator.lean:49,77,119–120`). No order assertion is made outside that range. Subtraction is polynomial-ring subtraction over ℚ, with no truncated natural subtraction or division.

DECL: VectorAffine PASS

This is precisely separate affineness in entire vectors, as used in `app-local-operator.tex:171–193` and Definition `d:Pauli`, lines 246–264. Mathlib represents each monomial by a finitely supported natural exponent function (`Algebra/MvPolynomial/Basic.lean:57–61,80–83`). For each nonzero monomial and each vector token j, summing its three coordinate exponents and requiring the sum to be at most 1 permits either no coordinate or exactly one coordinate to the first power. It excludes both coordinate squares and products of two different coordinates from the same vector, while allowing products involving different vectors. This is exactly the paper's unique expansion with one choice from {constant,x,y,z} per vector.

The test concerns actual nonzero coefficients, so cancelled monomials impose no spurious condition. Constants and the zero polynomial satisfy it as affine polynomials should; the paper explicitly includes the case of no vector variables (`app-local-operator.tex:16–18,225–227`). Quantification over all twenty tokens is equivalent to the paper's k-token condition for polynomials supported on the remaining vectors. The predicate imposes no unintended bound on total degree across different vectors and uses formal polynomial affineness on all of ℝ³, rather than identities restricted to unit spheres.

Non-blocking remarks:

- `contractSpins` is an auxiliary contraction on supported, degree-four U/D inputs. Its totalized values for higher degrees, X laws, or internal variables outside `V` are outside the paper's use; all present callers satisfy the required conditions. Likewise, raw `PatternData` admits extra data, while the comparison and certificate statements supply `Covered` explicitly.
- The use of rational coefficients and a rational threshold is exact for the certificate objects. The paper's general real-polynomial discussion specializes to these objects; no approximation or floating-point evaluation enters the definitions.
- Independent Python checks verified all 35 three-coordinate monomials of total degree at most four against the explicit icosahedron law using exact arithmetic in ℚ(φ), and both U/D moment scalings. A geometric check covered all 32,768 subsets of the fifteen template bonds remaining after exclusion of the passage-arrival bond, in both representations: 65,536 cases. It verified token distinctness, retained replacement neighbours, and spin degrees at most four. These source-level checks supplement the semantic reasoning; no Lean build was run.
- No blocking discrepancy was found. Inputs were left unchanged.
