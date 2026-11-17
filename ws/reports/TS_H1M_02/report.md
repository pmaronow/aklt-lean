STATUS: COMPLETE

| Leaf (namespace AKLT.Blueprint.H1) | Verdict | Difficulty | Reason |
| --- | --- | --- | --- |
| [OriginalDegreeStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPassage.lean:61) | TRUE | medium | All internal variables are active; the full template has at most four incident factors per site. |
| [OriginalFactorStructureStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPassage.lean:67) | TRUE | medium | A vector token occurs only in its own linear slot factor, and simultaneous orthogonal maps preserve every dot product. |
| [OriginalRawEvaluationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPassage.lean:73) | TRUE | easy | Evaluation reproduces the same assignment sum, weights, bond factors, and slot factors. |
| [MomentContractionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPassage.lean:81) | TRUE | medium | Support, separate degree, and U/D hypotheses exactly justify the monomial moment factors. |
| [MomentCovarianceTransferStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPassage.lean:90) | TRUE | hard | Specialization and finite reindexing put the integrand within the supplied polynomial covariance hypothesis. |
| [ContractionAffineStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPassage.lean:97) | TRUE | easy | The exponent projection preserves every external vector's total degree. |
| [ContractionSupportStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPassage.lean:103) | TRUE | easy | The exponent projection preserves absence of each external token. |
| [BlochAlgebraStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPauli.lean:11) | TRUE | easy | The concrete Pauli matrices give a Hermitian, traceless Bloch matrix whose square is the squared Euclidean norm times identity. |

All eight leaves are true and self-sufficient as written. No correction is required. The `Covered` premise in `OriginalDegreeStatement` can optionally be removed: the stated degree-four bound and active-support property already hold for arbitrary `PatternData`.

Audited repository: `/home/ubuntu/aklt/repo`, branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The repository remained clean. The source statements, their transitive mathematical definitions, and the cited manuscript arguments were inspected. No proofs were written and no sub-agents were used.

The definition audit covered the following dependencies, including the concrete finite data rather than only their comments:

| Source | Definitions checked |
| --- | --- |
| [H1/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/Definitions.lean:14) | `LocalPolynomial`, `VectorPolynomial`, `localEvaluation`, `rawFunctional`, `InternalAdmissible`, `LocalVectorAffine`, `LocalSupportedVectors`, `IntegrandInvariant`, `OrthogonalInvariant`, `MonomialMoments`, `ProductMomentCovariance`, `originalIntegrand`, `nextStatus`, `blochMatrix`. |
| [Defs/Operator.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:63) | `LocalVariable`, `formalDot`, `rationalMoment`, `rationalStatusMoment`, `contractSpins`, `VectorAffine`. |
| [Defs/Pattern.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Pattern.lean:8) | All thirteen template sites, tips, corners, all twenty `externalSlot` entries, `PatternData`, `Covered`, `statusAt`, `keptAt`, `bonds`, `active`, `spins`, `patternFunctional`, `patternCurrent`, `patternNext`. |
| [Defs/Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8) | `Plane`, `latticeDist`, `Compass`, `Compass.step`, `Adjacent`, `neighbours`, `positiveNeighbours`, `internalBonds`, `square`. |
| [Defs/Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9) | `Vec3`, `dot`, `normSq`, `UnitVector`, `Status`, `IcoLetter`, `SpinLetter`, `signValue`, `goldenRatio`, `icoRadius`, `icoVector`, `spinVector`, `spinWeight`, `siteFunctional`, `SeparateDegreeFour`, `productFunctional`. |
| [Defs/OperatorContracts.lean](/home/ubuntu/aklt/repo/AKLT/Defs/OperatorContracts.lean:9) | `supportSpins`, `SupportedVectors`. |
| [Defs/FiniteNetwork.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:59) and [Defs/Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:53) | `evaluateReduced` and every branch of `pauli`. |
| Mathlib | `Finsupp.comapDomain` and its application rule, `MvPolynomial.eval₂` and support-of-sum semantics, and `Matrix.IsHermitian` as equality with conjugate transpose. |

The paper arguments are [l:Iw and c:reduce](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:25), [d:Pauli and l:inversion](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:247), [l:moments](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:40), and [d:pattern](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:488). These supply the incidence argument, finite moment factorization, covariance of polynomials, and explicit Pauli algebra used by these leaves.

The degree count uses the complete template before any filtering:

| Site class | Number of sites | Internal bond factors per site | Slot factors per site | Total |
| --- | --- | --- | --- | --- |
| Passage and its four neighbours | 5 | 4 | 0 | 4 |
| Corners | 4 | 2 | 2 | 4 |
| Tips | 4 | 1 | 3 | 4 |

`internalBonds` uses positive coordinate orientations, so there are sixteen bonds, no self-bonds, and no duplicate reverse orientations. Each bond contributes degree one at each endpoint. The status and kept-set filters only delete bonds; the next-step conditional deletes another factor. A nontrivial slot factor is present only at a nonremoved template site. These facts establish both conjuncts of `InternalAdmissible`, including absence of variables at omitted sites. The stronger paper count of three passage bonds before the step is compatible with this upper bound.

Two existing moment premises deserve particular care:

- The support conjunct is essential. If it were omitted, `V = ∅` and `p = X (.inl (x,0))` would give contracted value `1` and raw value `0`. The current statement excludes this example.
- The U/D restriction on `V` is essential. For `V = {x}`, `s x = X`, and `p = 1`, the contraction uses constant moment `1`, but every actual spin weight is zero and the raw sum is `0`. The current statement excludes this example too. Statuses outside `V` are irrelevant.

The constant D moment is `1`; only its positive-degree moments receive the factor `3/5`. In particular, the U/D second moments are `1/3` and `1/5`, the fourth powers are `1/5` and `3/25`, and the mixed even fourth moments are `1/15` and `1/25`. All are consistent with the definitions. The twelve unit labels and the zero label give a common thirteen-letter assignment space; the zero label has weight zero at U sites. Powers use Lean's `0^0 = 1`, so constants and zero atoms behave correctly.

For the covariance leaf, fixing external vectors to `R*u` produces a polynomial with **real** coefficients in the finite internal coordinates. Its separate degree remains at most four. Reindex the subtype `V` by `Fin (Fintype.card V)`, use the same orthogonal matrix at every site, and apply the supplied product covariance. It changes the raw value of `p(n,R*u)` to the raw value of `p(R*n,R*u)`. Integrand invariance identifies the latter with the raw value of `p(n,u)`. The zero extension of spins commutes with rotation because `R.mulVec 0 = 0`. The contraction/evaluation identity needed in this route follows directly from the leaf's own `MonomialMoments` premise; no other blueprint leaf is an additional assumption.

For Bloch algebra, the definitions give the entries

```text
B(u) = [[ z,       x - i*y ],
        [ x + i*y, -z      ]],  with x = u 0, y = u 1, z = u 2 cast to complex.
```

Conjugation fixes the three real coordinates. The off-diagonal entries of the square cancel, and both diagonal entries are `x^2 + y^2 + z^2`, exactly the complex cast of `normSq u`. The zero vector is included; no division or normalization occurs in this leaf.

The Lean-specific checks and traps are:

- The scratch Lean inspection printed all eight declarations as closed `Prop`s. No section instance, type parameter, or implicit mathematical hypothesis was silently omitted. `Bool` conditions elaborate as `next = true`.
- Products over `π.bonds` are `Finset` products; the twenty slot factors use the `Fintype` `Fin 20`. The assignment space is a function on the finite subtype `V`, which has a `Fintype` instance even though `Plane` is infinite. Finite reindexing is required to use covariance stated on `Fin n`.
- `LocalVectorAffine` and `VectorAffine` bound the **sum** of the three coordinate exponents at one vector by one. The statements use the intended whole-vector affineness.
- `Finsupp.comapDomain Sum.inr` has value `m (.inr (j,k))` at `(j,k)`. Summing projected monomials can merge terms or cancel coefficients. Use support containment, not equality with the collection of input projections, for both contraction structure leaves.
- Rational polynomial coefficients and moment factors are cast by ring homomorphisms to real evaluations. The covariance hypothesis is on real polynomials after specialization. Bloch entries and scalar multiplication are complex. `normSq` is the explicit Euclidean dot product; it should not be replaced by the default norm on the function type `Fin 3 → ℝ`.
- Classical decidability may be introduced locally for finite polynomial-support and subtype manipulations. No additional decidability premise is mathematically needed. Polynomial moment covariance suffices throughout; invariance of the finite atom law on arbitrary functions is not a premise or conclusion.

All edge cases agree: `p = 0`, `V = ∅`, `J = ∅`, constant monomials, omitted spins, and `u = 0` in Bloch algebra. An empty assignment domain has one assignment, giving the empty product value one. These universal claims are not vacuous. For example, choose outgoing east, status U at every template site except removed south neighbour `(0,-1)`, all four kept directions away from the passage, and the three non-south directions at the passage; this satisfies `Covered`. Unit-vector assignments exist by choosing `(1,0,0)` at every slot. The explicit moments are consistent with the finite laws. A nonconstant covariance example is `p = (n_x · u_0)(n_x · u_1)` at one U site: its contraction is `(u_0 · u_1)/3` (and `/5` at a D site).

Two-line proof routes, with difficulty understood as estimated Lean implementation effort:

**OriginalDegreeStatement — medium**  
1. Use the bond and slot membership filters to show that every internal variable in any nonconstant factor lies in `π.active`.  
2. Bound monomial exponents by factor incidences and enumerate the complete template counts; filtering and next-step deletion only decrease them.

**OriginalFactorStructureStatement — medium**  
1. Track support through the finite products; only the `j`-indexed slot factor can contain token `j`, and it is linear in that entire vector.  
2. Evaluate `formalDot` as `dot` and use preservation of dot products by `R.transpose * R = 1` in every factor.

**OriginalRawEvaluationStatement — easy**  
1. Unfold the two functionals and the integrand, and push polynomial evaluation through sums and products.  
2. Identify `supportSpins` with `π.spins`, commute the slot dot products, and split `next` to obtain the current or next partition sum.

**MomentContractionStatement — medium**  
1. Expand supported monomials, using internal support to split evaluation into an external monomial and internal coordinate monomials over `V`.  
2. Factor the finite assignment sum into site sums, apply `MonomialMoments` with the separate degree bounds, and commute rational casts with products.

**MomentCovarianceTransferStatement — hard**  
1. Derive contraction/raw evaluation from the monomial moment premise; specialize external vectors to `R*u` in a real polynomial on the finite internal support.  
2. Reindex by `Fin (card V)`, apply product covariance, then use simultaneous integrand invariance and preservation of zero to obtain the contracted equality.

**ContractionAffineStatement — easy**  
1. Bound the support of `contractSpins` by the union of the singleton supports of its summands.  
2. Choose a contributing input exponent and use `comapDomain_apply` to transfer its whole-vector degree bound.

**ContractionSupportStatement — easy**  
1. Select a contributing input support monomial for any exponent surviving the sum defining `contractSpins`.  
2. Apply `comapDomain_apply` and `LocalSupportedVectors` at every coordinate outside `J`.

**BlochAlgebraStatement — easy**  
1. Expand the `Fin 3` sum and concrete Pauli matrices into the four entries of the Bloch matrix.  
2. Check conjugate transpose and trace entrywise, multiply the two-by-two matrix, and simplify the real-to-complex norm cast.

Verification artifacts are confined to this directory:

- [Inspect.lean](/home/ubuntu/aklt/reports/TS_H1M_02/scratch/Inspect.lean) imports the existing compiled statement modules, prints the exact declarations and relevant predicates, checks finite instances, and evaluates representative rational moments. It contains no proof declarations. The single-module Lean run exited successfully; see [lean-inspection.log](/home/ubuntu/aklt/reports/TS_H1M_02/scratch/lean-inspection.log). Only one Lean process was used.
- [checks.py](/home/ubuntu/aklt/reports/TS_H1M_02/scratch/checks.py) checked all thirteen incidence rows and the concrete covered witness, all seventy U/D monomial moments through degree four, 140 transformed-moment checks for a rational rotation and a rational reflection, 157 direct product-assignment sums on zero/one/two sites, and symbolic Bloch Hermiticity, square, and trace. Arithmetic used exact fractions, `Q(sqrt(5))`, and Gaussian integer polynomials, with no numerical tolerance. All checks passed; see [checks.json](/home/ubuntu/aklt/reports/TS_H1M_02/scratch/checks.json). The finite checks supplement the definition-and-paper audit; they are not claimed as Lean proofs of the leaves.
- [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_H1M_02/verdicts.jsonl) contains exactly one object per assigned leaf, in the brief's order, with the requested fields, per-leaf Lean traps, two-line routes, and difficulty.
