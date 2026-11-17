VERDICT: SOUND

Fatal findings: None.

Major findings: None.

Minor correctness/completeness findings: None.

The section proves the actual local partition-function comparison required by Sections 6–7, with the stated constants. Its finite certificates and coverage check pass. This verdict uses the replacement explicitly specified in Remark 1.1 and Proposition 1.18: H1-tree replaces the original, stronger covered-slot assertion (H1). It does not identify the two assertions. The necessary substitutions in the manuscript are listed below; they require no additional inequality. H2 and H3 are outside this review.

Numbering below is that of the supplied `wrapper.pdf`; locations are source-line numbers in `h1tree.tex`. I read the complete section, all three replay programs, `sec2-moments.tex`, `sec6-walks.tex`, and `sec7-recursion.tex`, and checked the invoked operator lemmas in `app-local-operator.tex`.

**Per-statement verdicts**

| Statement | Source lines | Verdict | Reason |
|---|---:|---|---|
| Remark 1.1, scope | 31–41 | correct | An actual D corner has two kept bonds and no original pin. Filling two independent external slots at such a corner can enlarge the model. The section correctly distinguishes the actual local conclusion from the original covered-pattern hypothesis. The replacement suffices at the uses audited below. |
| Definition 1.2, laws and factors | 43–61 | correct | The U and D laws, bond and field factors, and all moments agree with P.Definition 2.1 and P.Lemma 2.2. Covariance is asserted only for the relevant polynomials through separate degree four. |
| Lemma 1.3, elementary facts | 63–110 | correct | At most four factors exclude at most four of twelve positive-mass letters, giving positive normalizers even with fixed unit-ball neighbours. Leaf summation is exact. The two-field U computation assumes unit fields and is then extended correctly to balls. The one-field D means and the cited three-field bound have the stated laws and radii. Normalized-mean extension uses normalizer-weighted convex coefficients. |
| Definition 1.4, models and passage polynomials | 112–158 | correct | All 38 listed models have the required degree bounds. Deterministic mean vertices have no integration weight. The next polynomial retains the pair of non-outgoing marks when the outgoing mark disappears. The positivity estimates follow pointwise before integration. The printed models agree with the machine data. |
| Definition 1.5, H1-tree | 160–170 | correct | This is a precise list of 38 universally quantified inequalities. Separate affinity permits testing mean vectors on their boundary spheres. Missing outgoing marks and straight/turning constants are specified. |
| Lemma 1.6, unequal-radius means | 219–297 | correct | For either law the displayed mean formula follows from the second and fourth moments, with denominator parameter 3 or 5 as appropriate. The polynomial is exactly the difference of the squared bound and squared numerator. All 567 reconstructed Bernstein coefficients are nonnegative. The full cube contains every admissible Gram triple, and the normalizer is positive on actual fields. |
| Lemma 1.7, two unit fields and a small field | 299–339 | correct | The coordinate decomposition and the comparison of the two transverse coefficients are correct, including endpoint limits. Both required sets of 25 Bernstein coefficients are nonnegative. Expansion handles shorter first and second fields; the third field is already allowed throughout its ball. |
| Lemma 1.8, scalar inequalities | 341–377 | correct | Minimizing over the outgoing vector gives the stated square-root expression. Nonnegativity of L and Q implies the desired inequality. Endpoint tests and the conditional interior-vertex test exhaust a quadratic's minimum on the interval. All 89 exact comparisons pass; the sole interior test is model 32. |
| Definition 1.9, reconstruction | 379–438 | correct | The mean encoding has normalizer one and prescribed first moment; it is used algebraically, so 3R exceeding one is harmless. The bond-index contractions, insertion indices, denominator clearing, Pauli map, pair bases, and positive scaling in (14) are consistent. The central weight is 0 or 1/2; the program represents these as doubled weights 0 or 1. |
| Lemma 1.10, matrix certificates | 440–540 | correct | Degree-four covariance gives simultaneous spin commutation. Each retained U field pair is supported on its symmetric square; there are no retained D field pairs. P.Lemma D.9 therefore applies. All reconstructed central forms equal gN exactly, and all 384 residual row margins are strictly positive. Positivity of these forms implies full operator positivity and then polynomial nonnegativity by the Pauli trace identity. Unnormalized pair bases cause no problem for positivity of a Hermitian form. |
| Proposition 1.11, discharge | 542–554 | correct | The 22 scalar models and 16 matrix models partition the complete printed input. Their certificates are universal in the directions. The two mean lemmas remain separately established inputs to the local reduction. |
| Definition 1.12, actual data | 556–582 | correct | These are exactly the non-tip kept-set rules supplied by the trace closure statements. Actual tips, original pins, missing tip bonds, and the pre/post-step networks are distinguished from covered slots. |
| Lemma 1.13, pins and counts | 584–611 | correct | Distance at least three from the original complement puts the entire template in G and excludes original legs at the passage and its nearest neighbours. Corners have at most two external directions and tips at most three. A D corner has no pins and at most 2−k external factors. Removal creates no new pins. |
| Lemma 1.14, reduction cases | 613–881 | correct | Passage summation gives the common base functional. Tip integration, D-law expansion, upper-corner handling, the lower cases (a)–(d), and isolated-mark integration are valid with the stated laws and field counts. All removed normalizers and mixture coefficients are common to the current/next pair. The lower path is retained precisely in the case requiring its correlation. Detailed checks appear below. |
| Lemma 1.15, coverage | 883–1026 | correct | The raw masks and consistency filter exhaust the allowed non-tip configurations. The effective-record quotient preserves the maximal field allowances. The program enumerates every reduction branch, checks domination of every generated model, and checks equality of both maximal antichains. All printed counts, 20 geometries, 38 maximal models, and 21 mean calls reproduce. |
| Lemma 1.16, extension | 1028–1051 | correct | Relabeling preserves the finite sums. F is separately affine in each field and each isolated marked mean. Componentwise enlargement therefore transfers the inequality by common convex coefficients; no ratio monotonicity is assumed. |
| Theorem 1.17, actual local conclusion | 1053–1101 | correct | C and N are unnormalized template sums with identical outside factors. Each reduction branch satisfies the desired difference inequality, including empty marked sets. Summing against the common nonnegative outside weight proves the full-network comparison and its ratio consequence. The finite checks discharge the premises. |
| Proposition 1.18, use in the paper | 1103–1136 | correct | P.Lemma 7.2 supplies the first-trace hypotheses. Outside distance two from the fixed terminal defect, P.Lemma 7.3 supplies the second-trace hypotheses. At most twelve U departures can be exceptional, and the existing 12/5 bound applies there. The typed-response use also needs only the actual ratio inequality, as checked below. |
| Remark 1.19, computational scope | 1138–1182 | correct | The distinctions about D slots, upper D leaves, lost outgoing marks, fixed D tip-neighbours, and retained lower paths agree with the proof and implementation. All supplied numerical diagnostic counts and values reproduce. These diagnostics are properly excluded from the proof inputs. |

**Checks of the reduction and its conditioning**

At lines 622–630 the passage is integrated under its pre-step U law or post-step D law. There are at most three pre-step bonds, no passage pin, and no incoming bond. The remaining spin laws and factors are identical in the two expressions. Thus the only distinction is the inserted polynomial I or J. In particular, none of the later normalizers is taken under a measure already tilted by I or J.

At lines 632–650 each actual tip is integrated against its own external weight, excluding its template bond. There are at most three such fields, including any original leg factors, and either U or D is allowed. P.Lemma 2.5 consequently bounds the resulting mean by 3/5. A missing actual tip bond is represented by zero in the prospective covering direction. Its scalar normalizer is still retained in both sums. This does not add a factor to a D kept set.

At lines 652–691 a D marked neighbour keeping its tip is left under the D law. After passage deletion it has precisely one possible effective field, of norm at most 3/5, so its mean is b/5 and its normalizer is one. Its bound is 3/25, not a three-field U bound. Every other D marked neighbour has at most one non-passage bond and no tip field. Expanding its law is exact in both polynomials. The zero branch kills its incident bonds and every insertion containing that mark. It does not change the identities of the other two non-outgoing sites.

An upper D corner with two original internal bonds has zero external fields. Its law expansion yields an active U bridge or the constant kernel one. After loss of one endpoint the active U term also integrates to one: it has just one bond and no fields. The proof and code do not assign an arbitrary two-field U-leaf mean in that situation. A D upper corner with one original internal bond has at most one external field, so the 1/5 bound at lines 839–841 has its hypotheses satisfied.

The lower-case analysis at lines 693–827 is exhaustive because the arrival is X or D with two kept directions among its two lower directions and its tip direction. After removal of endpoints, its present lower degree is two, one, or zero:

| Lower case | Integration and bound | Verdict |
|---|---|---|
| Two lower bonds, both side marks survive, outside case (d) | Integrate the field-free D arrival and use the auxiliary twelve-letter identity (18). On each fixed auxiliary-spin fibre, an attached U corner has at most two external unit-ball fields plus one field of radius sqrt(3/5), so the three-field 3/5 bound applies. An attached D corner had two internal bonds and no external fields; its only new field gives mean sqrt(3/5)ξ/5, bounded by 1/5. | correct |
| Two lower bonds, one side survives | Integrate the opposite corner first, excluding its bond to the arrival. Its mean is bounded by 1/2 for U or by 1/5 for D. Integrating the D arrival divides this field by five. The attached U corner therefore has radii at most (1,1,1/10), giving 18/35. The attached D corner has no external fields and gives at most 1/50. | correct |
| One lower bond and tip direction | Tip integration gives a field of norm at most 3/5 at the D arrival, whose integration divides it by five. The attached U corner has radii at most (1,1,3/25), giving 137/265. The attached D corner has no external fields and gives at most 3/125. | correct |
| One lower bond without an effective tip field, or no lower connection | The D arrival integrates to one when it has only the lower bond. Remaining U leaves have at most two external fields, giving 1/2; attached D leaves have at most one, giving 1/5. Disconnected components contribute common positive scalars. Zero prospective tip fields are included in these bounds. | correct |
| Retained case (d) | E,W survive, N does not, both lower bonds are present, and both lower corners were U. Consistency forces both side bonds, so retaining the five-vertex U–U–D–U–U path is exact. No independent-field relaxation of that path is made. | correct |

For the auxiliary split, the coefficient after corner integration is A_L(ξ)A_R(ξ)/12. Each A is the normalizer excluding the bond to a surviving marked site and excluding passage insertions. Therefore the coefficient is the same for C and N even though it depends on ξ and the fixed outside fields. It need not sum to one. Together with the fixed D-law weights and all leaf normalizers, this establishes the common-coefficient assertion, rather than merely separate convex decompositions of the two partition functions.

The retained case is also necessary for this particular enlargement strategy. I independently checked the displayed exact arithmetic: with q=226/495, 1−q²/3=683999/735075<187/200. The proof correctly treats this as a counterexample to an intermediate independent-mean enlargement and preserves the missing correlation.

After the upper reductions, every remaining component is a path. If N survives, cutting the arrival connection leaves subpaths of E–A–N–B–W. If the lower path is retained, N is absent and no upper bridge can remain. A marked U vertex of path degree d has at most 3−d fields; adding one insertion gives separate degree at most four. Unmarked U corners have degree four, and the retained D arrival has degree two. Isolated marks are integrated against their external fields alone, giving a common positive normalizer and their actual normalized means. Every requested radius triple is one of the 21 certified triples.

Original pins present no exception to these arguments. They can occur at corners or tips, use their actual external directions, and have unit norm. D sites have no original leg. Correlated outside spins or coincident pin directions give particular assignments inside the independently bounded field balls; no independence of those fields is needed.

At lines 1076–1098 the outside configuration is fixed before taking any template sums. H(ω) consists of outside laws and outside-only factors and is identical before and after the step. C(ω),N(ω) are unnormalized sums; the argument does not compare differently normalized conditional probabilities. The proof remains valid on zero-weight outside assignments. Multiplication by H and finite summation is legitimate, and strict positivity justifies the final partition-function ratio.

**Exhaustiveness and finite certificates**

The coverage enumeration follows the stated definitions, rather than reading an old catalogue. There are 4 arrival options, 5 options at each other neighbour, and 8 at each corner. The filter tests exactly the corner/neighbour bonds with two nonremoved ends. Bonds to the passage have already prescribed flags. A removed endpoint imposes no consistency test, as required by P.Definition 6.1. Tip status is not enumerated because the preceding exact tip integration covers every actual tip with a vector in the 3/5 ball, including zero.

Collapsing effective records is safe. A U corner has at most two external fields; a D corner with k present internal bonds has at most 2−k. Different original masks can reduce the number of actual external factors, but they cannot exceed these allowances. Missing factors are represented by zeros. Isolated unmarked sites have common positive normalizers and can be removed. Reflection preserves the type and all these allowances.

The replay obtains 106,101 consistent raw choices, 184,914 choices with a marked outgoing site, 123,339 with outgoing N or E, 7,962 effective reflection classes, and 24,741 binary branches. Of these, 981 have no surviving mark and are trivial. Every other generated forest is checked against a dominating listed model. The maximal antichains are compared for equality, giving exactly 20 decorated geometries and 38 models. The mean-call set equals the printed set of 21 rows. I separately parsed the printed tables and compared all 38 model descriptions, all 21 mean rows, and all 16 matrix-certificate parameter rows with their data files; all agree.

The Bernstein implication is valid: each Bernstein basis function is nonnegative on [0,1], and the tensor-product basis is nonnegative on the full cube. For Lemma 1.6 the separate degrees are at most (2,2,2); for Lemma 1.7 the chosen degree (4,4) is sufficient. Every actual scalar-product triple lies in the respective full box. The box can contain unrealizable Gram triples without weakening the implication. Positive actual normalizers permit taking square roots and dividing. The mean bounds are asserted only for the certified radii.

For scalar models, the minimizing outgoing vector can be opposite the sum of the other means. L≥0 and Q=L²−(nonnegative square-root term)²≥0 consequently suffice. The code recomputes both endpoint tests for L, both for Q, and the interior minimum when present, comparing the rational values to the witness file. This proves all 22 scalar inequalities, including cases with absent outgoing marks. The older 19-box file is not used as their certificate.

For matrix models, the reconstruction uses only the displayed site moments and the printed radii. All inserted degrees are counted. Pair support follows from the unit spin at an unmarked U corner, not from a claim that the finite law is invariant on arbitrary functions. Simultaneous polynomial covariance gives commutation with the total spin generators. P.Lemma D.9's ladder argument reaches weight 0 or 1/2 in each invariant eigenspace, so a positive central form suffices on the whole supported space. In the unnormalized basis, positive definiteness is a property of the form and does not require treating its entries as an orthonormal-basis operator matrix.

The replay checks M=gN entry by entry, reality, symmetry, separation of different weights, integer triangular L, and every strict diagonal-dominance margin of E=ds²N−LLᵀ. These exact checks give E>0, hence N>0 and M>0. Positive scaling, the central-weight argument, zero action on discarded antisymmetric spaces, and the product-density Pauli trace identity then imply F_c≥0. No floating point factorization or sampled-direction assertion enters that proof.

The replay statistics agree with the section: 567 cube coefficients, 25 coefficients for each required special mean bound, 22 scalar models with 89 comparisons, 16 central forms, 14,502 matrix entries, 7,443 triangular Gram entries, 129,491 triangular Gram products, 384 residual rows, 1,465,600 dense coefficient cells and 122,884 nonzero cells. The reported bit bounds also reproduce: 53 for the cube coefficients, at most 27 for the required special coefficients, 37 for normalized matrix entries, and 19 for Gram entries.

**Every use of (H1) in Sections 6–7**

The following includes explicit mentions of (H1) and downstream invocations of the local/one-point lemmas. Locations refer to the manuscript source files.

| Location | What is needed | Sufficiency of the replacement |
|---|---|---|
| `sec6-walks.tex:531–544`, Definition 6.9 and scope sentence | The original covered-slot hypothesis is defined here. | The new section does not prove this definition's full assertion. Use H1-tree and Theorem 1.17 as the replacement, as Remark 1.1 explicitly directs. The sentence about using the full covered class must be read with that replacement. |
| `sec6-walks.tex:546–653`, Lemma 6.10, especially the application at 636 | C(ω)≥cN(ω) and therefore ρ^τ≤1/c for actual departures with the specified non-tip data. | Theorem 1.17 proves these conclusions directly, with the same uniformity in pins, outside fields, missing factors, and actual tips. Its proof replaces the old filled-slot proof. |
| `sec6-walks.tex:695–775`, Lemma 6.13, especially 696 and 728–744 | Ordinary U departures have ρ^τ≤1/c; exceptional ones have ρ^τ≤12/5. Free ratios are at most one; D ratios are one. | Theorem 1.17 supplies the first bound. The remaining bounds come from P.Lemma 6.6 and P.Definition 6.5 independently of (H1). The same pointwise trail majorant and summed bound follow. |
| `sec7-recursion.tex:10–34` | Quantitative-input declaration and references to local and one-point bounds. | Substitute the certified actual local theorem for (H1). The cited consequences remain available. |
| `sec7-recursion.tex:142–159`, proof of Lemma 7.2 | Every first-trace U departure has the requisite local data; original corner/tip legs are retained. | The kept-set induction supplies Definition 1.12. Lemma 1.13 supplies the actual field counts. The original corner-slot filling reference is replaced by the new direct reduction. |
| `sec7-recursion.tex:172–246`, Lemma 7.3, especially 223–246 | In the second trace the fixed protected defect e is outside the template when d(y′,e)>2; at most twelve U departures need the exceptional bound. | The new theorem applies away from e. The actual tips are then distinct from e. The defect can only cause missing external factors outside the template, which are allowed. At distance one or two use 12/5. There is no departure at e, and a site can have U status at departure at most once. |
| `sec7-recursion.tex:398–428`, typed-response lemma | I^τ/J^τ≥c_type. | This is exactly the full-network ratio consequence of Theorem 1.17: divide Z_cur≥cZ_next by the common positive passage-deleted normalizer. The proof never needs an artificially filled D corner. |
| `sec7-recursion.tex:494–510`, same lemma | I^τ≥cJ^τ with three neighbours, and I^τ≥c when J=1 with two. | Both follow from that same actual comparison. The estimates of J^τ, I^0 and J^0 are separately proved from conditional means and free positivity. Thus all typed response constants are preserved. |
| `sec7-recursion.tex:705–709,770–802`, recursion lemma and its T1 estimate | At every actual U departure, both the ratio majorant and typed response bounds. | Lemma 7.2 supplies the geometry; the theorem and preceding typed-response reasoning supply exactly these bounds, including the designated initial incoming direction. D departures need no local input. |
| `sec7-recursion.tex:872–897`, second expansion in T2, including explicit (H1) mention at 888 | The one-point bound in the terminal auxiliary network. | Lemma 7.3 and Proposition 1.18 provide the non-exceptional theorem applications and at most twelve generic 12/5 applications. The proof does not require the terminal network to be an ordinary consistent domain everywhere. |
| `sec7-recursion.tex:904–921`, enlarged first-trail sum | The one-point majorant after dropping avoidance of v. | Lemma 7.2 explicitly does not require avoidance of v. Its local hypotheses therefore still hold throughout the enlarged class. |
| `sec7-recursion.tex:1012–1037`, final recursion theorem | The preceding recursion, under the local input, H2, and H3. | This is an inherited use only. Replace the (H1) hypothesis by the certified local theorem. The kernel thresholds, response constants, exception factor, and ensuing recursion are unchanged. |

Thus the section supplies the required local input at all uses, including the typed-response argument and both exceptional-trace estimates. Adding the section while continuing to claim that it certifies the old covered-slot Definition 6.9 would misstate its result; that is expressly excluded by the submitted section itself.

**Numbered displays and tables**

| Display/table | Verdict | Check |
|---|---|---|
| (1) | correct | Constants equal those used in the manuscript. |
| (2) | correct | U moments and D scaling agree with P.Lemma 2.2. |
| (3) | correct | Exact leaf summation with its external normalizer. |
| (4) | correct | Nonnegative coefficients sum to one, including a zero field. |
| (5) | correct | Exact passage-integrated current and next polynomials, including lost outgoing marks. |
| (6) | correct | Precise H1-tree assertion. |
| (7) | correct | Mean formula and listed proposed radii, with d=3 or 5. |
| (8) | correct | 25R²(d+x+y+z)²−|V|². |
| (9) | correct | Monomial-to-Bernstein conversion on the tensor-product cube. |
| (10) | correct | Both small radii and resulting bounds agree with the special-mean formula. |
| (11) | correct | Orthogonal-coordinate bound and positive three-field normalizer. |
| (12) | correct | Complete interval tests for L and Q. |
| (13) | correct | Tensor contraction for the normalizer and pair insertions. |
| (14) | correct | 5qA−3pB=15qD₀ O(F_c^I) on the central form. |
| (15) | correct | Exact integer Gram/residual positivity certificate. |
| (16) | correct | The specified D probability law. |
| (17) | correct | Field-free two-bond D corner kernel and its U/zero mixture. |
| (18) | correct | Auxiliary-spin split follows from zero first moment and second moment δ/3. |
| (19) | correct | Product of the two external corner normalizers divided by twelve; common to current and next. |
| (20) | correct | D arrival transmits the opposite mean divided by five. |
| (21) | correct | D arrival transmits the tip mean divided by five. |
| (22) | correct | Retained lower-path case; complements are exhausted by (a)–(c). |
| (23) | correct | Every listed lower radius has the required law and field-count justification. |
| (24) | correct | Every enumeration count reproduces. |
| (25) | correct | Conditional unnormalized template-sum inequality. |
| (26) | correct | Full-network comparison and reciprocal ratio bound. |
| Table 1, all indices 0–37 | correct | All printed paths, laws, marks, outgoing marks, and radii match the replay data. The 22 scalar and 16 matrix certificates pass. |
| Table 2, all 21 rows | correct | Every printed law, radius triple, and mean bound matches the reconstructed exact Bernstein check. |
| Table 3, all 16 rows | correct | Every inversion, dimension, scale, Gram parameter, and minimum residual margin matches the data and exact reconstruction. |
| Geometry table at lines 997–1019 | correct | Its 20 entries partition the 38 maximal rows; all are generated by the exhaustive coverage replay. |

**Replay and independent tests**

I copied `checks/` and `data/` to `REF_H1T/replay/` before running them, because the programs regenerate receipts in their own data directory. The source directory and manuscript were not edited. Python was 3.12.3; NumPy 2.5.5 was installed locally in `REF_H1T/deps/`. At most one CPU-heavy replay process was running at a time.

From `/home/ubuntu/aklt/reports/REF_H1T`, the successful replay commands were:

```sh
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH="$PWD/deps" OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 replay/checks/audit.py all
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH="$PWD/deps" OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 replay/checks/numerical.py
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH="$PWD/deps" OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 independent.py
```

The exact audit finished successfully in approximately 6.9 seconds. Its coverage, mean and finite receipts are identical as parsed JSON to the supplied receipts. The numerical replay also regenerated an identical receipt: 1,764 assignments, 6,336 branches, 522 auxiliary splits, and 24 retained-path branches; maximum normalized identity error 8.881643014828648×10⁻¹⁶; minimum sampled ratio slack 0.019535315917221123.

The independent checker parses the three printed tables, tests normalized means directly on the thirteen-letter U/D support, and compares the supplied coefficient reconstruction against a separate finite-spin path-message integration, without using the supplied bond-contraction algorithm. It checked 25,000 mean assignments, 1,824 forest assignments across all 38 models, and 300 auxiliary-arrival identities. The largest forest discrepancy was 9.992007221626409×10⁻¹⁶; the minimum sampled forest ratio slack was 0.0028740824241481056. Mean-bound discrepancies were within floating point roundoff. The independent checker also verifies the discarded-correlation counterexample exactly with rational arithmetic. These are falsification diagnostics, not replacements for the exact proof.

Evidence files: [exact replay log](/home/ubuntu/aklt/reports/REF_H1T/replay/audit.log), [numerical replay log](/home/ubuntu/aklt/reports/REF_H1T/replay/numerical.log), [independent checker](/home/ubuntu/aklt/reports/REF_H1T/independent.py), and [independent results](/home/ubuntu/aklt/reports/REF_H1T/independent-results.json).
