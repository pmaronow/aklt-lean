STATUS: COMPLETE

All eight leaves are **TRUE** and self-sufficient as written. No fixes or additional hypotheses are needed. No vacuous cases were found.

Every leaf below is in namespace `AKLT.Blueprint.Mom` and corresponds to paper label `l:moments`.

| Leaf | Verdict | Difficulty | Reason |
| --- | --- | --- | --- |
| [IcoInjectivityStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesMoments.lean:11) | TRUE | easy | The unique zero coordinate recovers the group; two independent signs recover the label. The common radius is positive. |
| [IcoUnitStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesMoments.lean:15) | TRUE | easy | Every numerator has squared norm 1+phi²=phi+2=icoRadius². |
| [OddMonomialStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesMoments.lean:29) | TRUE | medium | Individual coordinate reflections preserve the labelled sum and negate the selected odd-coordinate monomial, in every degree. |
| [SecondScalarMomentStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesMoments.lean:34) | TRUE | easy | (1+phi²)/(3 icoRadius²)=1/3 for each coordinate. |
| [FourthScalarMomentStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesMoments.lean:38) | TRUE | easy | (1+phi⁴)/(3 icoRadius⁴)=1/5 for each coordinate. |
| [MixedScalarMomentStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesMoments.lean:43) | TRUE | easy | For distinct coordinates, one four-label group contributes, giving phi²/(3 icoRadius⁴)=1/15. |
| [ScalarTensorReconstructionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesCore.lean:44) | TRUE | medium | Pointwise monomial identities and the supplied scalar values give every tensor entry; the fourth-order pairing counts are 3, 1, or 0. |
| [TensorMonomialStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesCore.lean:55) | TRUE | medium | All 35 exponent triples of total degree at most four match rationalMoment; degree zero is correctly independent of c. |

The audit used repository branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`, and the paper’s [definition and moment lemma](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:8). The relevant paper argument is at lines 55–76; the statement is at lines 35–52. The repository was clean before and after the audit and was not modified.

**Definition closure checked.** The six explicit-icosahedron leaves unfold through `Vec3`, `IcoLetter`, `signValue`, `goldenRatio`, `icoRadius`, `icoVector`, `moment`, `normSq`, and `dot` in [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9), together with `mono` in [NodesCore.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesCore.lean:14). The two abstract leaves additionally use `TensorLaw` and `scaledMoment` in [NodesCore.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesCore.lean:29), and `rationalMoment` in [Operator.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:70). The foundational definitions of `Function.Injective`, natural parity, and `Real.sqrt` were also inspected. Imported unrelated blueprint propositions are not premises of these leaves.

Concretely, the alphabet is `Fin 3 × (Fin 2 × Fin 2)`, `Vec3` is `Fin 3 → ℝ`, `normSq v = ∑ i, v i * v i`, and `moment f = (1/12 : ℝ) * ∑ j : IcoLetter, f (icoVector j)`. The vectors are exactly the paper’s three cyclic groups with two independent signs. Writing phi for `goldenRatio` and r for `icoRadius`, their definitions give phi>0, r>0, phi²=phi+1, r²=phi+2=1+phi², r⁴=5 phi², and 1+phi⁴=3 phi².

`TensorLaw L c` supplies mass one, zero first and third tensors, second tensor `(if i=j then c/3 else 0)`, and fourth tensor `c/15` times the sum of the three pairing indicators. `rationalMoment` returns one at total degree zero, 1/3 at degree two with an exponent two, 1/5 at degree four with an exponent four, 1/15 in the remaining all-even degree-four cases, and zero otherwise. `scaledMoment` returns one at degree zero and `c * (rationalMoment m : ℝ)` at positive degree. These branches agree exactly with the supplied tensor data through degree four.

**Lean traps and self-sufficiency.**

- The elaborated declarations are closed `Prop` constants with no implicit instance parameters. Inferred coordinate indices are `Fin 3`; the powers in the statements are natural powers of real coordinates. The label product is right-associated, so the sign projections are `j.2.1` and `j.2.2`.
- The coordinate moments use real division. `rationalMoment` uses rational division, followed by a rational-to-real cast in `scaledMoment`. No displayed fraction becomes natural-number division. Cast normalization is needed in the abstract monomial leaf.
- `Real.sqrt` is totalized, and real division at zero is also totalized. Here phi+2 is strictly positive, so r is nonzero. Derive this from the definitions before cancelling denominators; it is not a missing premise.
- `moment` sums all twelve labels using `Fintype`, not the image `icoSet`. Its scalar and parity identities do not require injectivity. The explicit `Fin` alphabets and their product have their standard finite instances. Classical decidability used during a proof supplies no additional mathematical hypothesis; the printed finite equality/parity tests already have decidability instances.
- `mono` includes zero exponents, with `0^0=1`. A selected odd exponent is positive, so the corresponding zero-coordinate group contributes zero. Antipodality alone does not settle an exponent pattern such as `(1,1,0)`; use preservation under an individual coordinate reflection. This settles the arbitrary-degree quantifier in `OddMonomialStatement`.
- Both abstract leaves quantify over arbitrary `L`. They require only equality of input functions, which can be shown pointwise and rewritten under `L`. They do not require distributing `L` over sums or constants, so no linearity premise is missing. The reconstruction parity premise covers all degrees, although its conclusion uses only degrees one through four.
- `TensorMonomialStatement` permits every real c. Positivity is unnecessary for its algebraic conclusion. In particular c=0 still has constant moment one. Degree zero forces all three exponents to be zero; positive degree uses the scaled branch. No natural-number subtraction occurs in the audited definitions.
- The domains and premises are nonvacuous: there are twelve labels, the explicit moment functional meets the scalar assumptions, and evaluation at zero realizes `TensorLaw` with c=0. Signed mixtures `c * moment f + (1-c) * f 0` also realize the tensor values for arbitrary real c.

**Two-line proof routes (no proofs written).**

1. `IcoInjectivityStatement` (easy): Derive goldenRatio > 0 and icoRadius > 0 from their explicit square-root definitions.  
   Cancel the common radius, identify the unique zero coordinate, and recover the two Fin 2 signs within the resulting group.

2. `IcoUnitStatement` (easy): Establish phi^2=phi+1, icoRadius>0, and icoRadius^2=phi+2 from Real.sqrt.  
   Expand normSq and the three vector groups, reduce both sign squares to one, and simplify (1+phi^2)/icoRadius^2=1.

3. `OddMonomialStatement` (medium): For the selected odd coordinate, define the label involution that fixes its zero-coordinate group and flips the relevant sign in the other two groups.  
   Use odd-power negation, including the zero-coordinate case, and reindex the finite sum to obtain moment(mono m)=-moment(mono m), hence zero.

4. `SecondScalarMomentStatement` (easy): Expand the twelve-label sum for each of the three coordinates and reduce the two sign squares to one.  
   Use phi^2=phi+1 and the positive-radius identity icoRadius^2=phi+2 to simplify (1+phi^2)/(3*icoRadius^2)=1/3.

5. `FourthScalarMomentStatement` (easy): Expand the three coordinate cases in the twelve-label sum to obtain (1+phi^4)/(3*icoRadius^4).  
   Derive 1+phi^4=3*phi^2 and icoRadius^4=5*phi^2 from the radical definitions, then cancel the nonzero factors to get 1/5.

6. `MixedScalarMomentStatement` (easy): Split the six distinct Fin 3 coordinate pairs and expand the label sum; only their common nonzero group survives.  
   Use icoRadius^4=5*phi^2 and phi != 0 to simplify phi^2/(3*icoRadius^4)=1/15.

7. `ScalarTensorReconstructionStatement` (medium): Rewrite each indexed coordinate product as mono of its multiplicity function, using pointwise commutative-ring identities, and apply the given constant/parity/second-moment hypotheses.  
   For the fourth tensor, classify all-equal, two-distinct-pairs, and remaining odd-exponent patterns; the three Kronecker pairing indicators give 3, 1, and 0 respectively.

8. `TensorMonomialStatement` (medium): Expand the Fin 3 sum to bound all three natural exponents by four, and classify their 35 possible triples; rewrite mono pointwise as a product of zero through four indexed coordinates.  
   Apply the corresponding TensorLaw component and simplify rationalMoment and scaledMoment, separating degree zero before normalizing rational casts and the three fourth-order pairings.

**Verification.** [check_finite_cases.py](/home/ubuntu/aklt/reports/TS_MOM_01/check_finite_cases.py) uses exact `Fraction` coefficients in the quadratic field with phi²=phi+1, without floating-point tolerances. It checked twelve distinct numerators, twelve numerator norm identities, all three coordinate-reflection permutations, all 35 exponent triples through total degree four, and all 120 indexed tensor products of orders one through four. The fourth-order pairing counts are three entries with three pairings, eighteen with one pairing, and sixty with none. The degree-four monomial comparison also treats c symbolically, covering zero and negative c. As an additional check of the parity calculation, all 371 exponent triples with an odd coordinate and total degree at most twelve had zero numerator average. The general odd-degree verdict rests on the reflection argument, rather than a finite cutoff. Results are saved in [finite_checks.json](/home/ubuntu/aklt/reports/TS_MOM_01/finite_checks.json).

One Lean 4.35.0-rc2 process successfully inspected [inspect_statements.lean](/home/ubuntu/aklt/reports/TS_MOM_01/inspect_statements.lean), using the repository’s existing compiled modules and a local symlink to its Mathlib package directory. The file contains only imports, printing options, `#print`, and `#check`. The [elaboration log](/home/ubuntu/aklt/reports/TS_MOM_01/lean_inspection.log) records all eight exact statements, relevant tensor definitions, instance elaboration, and coercions. This was declaration inspection, not a Lean proof of the leaves. No repository build or whole-project build was run, and no sub-agents were launched.

The machine-readable deliverable is [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_MOM_01/verdicts.jsonl), with one object per requested leaf and exactly the requested fields.
