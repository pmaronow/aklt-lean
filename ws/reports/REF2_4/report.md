VERDICT: SOUND

This verdict concerns Sections 2 and 6, including their conditional conclusions, rather than an independent certification of the whole paper. I read all supplied LaTeX files for context and checked `sec2-moments.tex:1–353` and `sec6-walks.tex:1–776` line by line. I found no false statement, missing hypothesis needed by the proofs, or substantive proof gap in these sections. The local inequality (H1) and trail bound (H2) are explicitly external inputs to the conditional estimates; their numerical certificate files were not among the permitted paper inputs and were not inspected. No input file was modified, and no sub-agents were used.

## Numbered findings

None. The finding list is empty: no Critical, Major, or Minor defect was identified in the assigned sections, and no LaTeX repair is required.

## Proof audit

1. **Moment functional and covariance — `sec2-moments.tex:8–95`, `d:moment`, `l:moments`.** The three coordinate families have distinct zero-coordinate locations, and each has four distinct sign choices. The identity \(r^2=1+\phi^2\) gives unit norm. Independent coordinate sign changes kill every monomial with an odd coordinate exponent. The three remaining nonconstant cases through degree four give exactly \(1/3,1/5,1/15\). In particular, cyclic coordinate symmetry is sufficient; the proof does not require the vertex set to be invariant under every coordinate permutation. The delta-tensor expressions prove covariance under arbitrary orthogonal matrices for the stated polynomial degrees. This is polynomial covariance, not invariance of the discrete measure on arbitrary functions. The mixture law has mass \(1/20\) at each vertex and \(2/5\) at zero; its second and fourth tensors have coefficients \(1/5\) and \(1/25\), respectively. Sitewise covariance follows by factoring monomials of separate degree at most four.

2. **Pins, positivity, and conditioning — `sec2-moments.tex:97–195`, `d:pinmodel`, `l:finitefacts`.** Original legs are indexed by directed incidences, so unrelated pins at a shared outside endpoint are permitted. Removing a site adds no interaction or pin. Each surviving spin has at most four incident factors. A unit pin or a previously selected unit neighbouring spin excludes at most one of the twelve available letters. Thus the greedy construction leaves at least eight choices at every stage and produces a strictly positive summand, for either site law. This establishes the denominators used in the definitions, including empty networks. Conditional independence is used only after fixing every other spin on a positive fibre; the factorized conditional normalizer is then positive. Free positivity applies only to the pin-free, positive-interaction model and to observables satisfying the separate-degree restriction. Its coordinate expansion has nonnegative coefficients and nonnegative delta-tensor contractions. Coincident endpoints consume two degrees, as stated.

3. **The sharp mean bound and its range — `sec2-moments.tex:197–295`, `l:35`.** The three-unit-field normalizer is at least \(1/2\), and the displayed polynomial identity has the correct coefficients and sign. Consequently \(|V|\le 3(3+p)\), with a positive denominator. Resolving shorter products and fields in the closed unit ball into three-unit-field products gives a convex combination only after reweighting by the positive normalizers; the proof performs this reweighting correctly. The diluted-law mean is the asserted positive scalar, less than one, times the undiluted mean. For the range assertion, the endpoint at \(t=2\pi/3\) has all three pair products equal to \(-1/2\) and zero numerator. Continuity and the intermediate value theorem give every norm between zero and \(3/5\); polynomial covariance gives every direction without rotating the finite support as a probability law. This exact range, rather than just the norm bound, is what the covering argument needs.

4. **Quadrature and response property — `sec2-moments.tex:297–351`, `l:exact`, `h:P`.** Equality of moments through degree four gives equality of the finite product functionals by monomial factorization, also for an arbitrary specified subset of diluted sites. Both signs in the bond/pin factors are covered. The degree restriction includes observables and multiplicities; it does not imply equality of arbitrary marginals or conditional laws. Property \(\mathsf P\) is well posed for all its quantified data. If a pair exists, \(G\) is nonempty and finite, hence \(S(G)\ne\varnothing\); the exponent is a finite nonnegative integer. Empty pair classes impose no condition. The common removed neighbour lies outside the protected layer by the hypothesis on \(Y\).

5. **Networks and trace invariants — `sec6-walks.tex:8–98`, `d:domain`, `d:trace`.** Kept flags and present bonds are distinct data. Ordinary domains impose the stronger flag consistency conditions; auxiliary networks permit the protected endpoint's lost arrival flag. All original pin factors remain at protected U sites. A later U arrival leaves at most three present bonds, and a D arrival leaves at most one. A U departure therefore leaves at most two present bonds at the new D site. A D departure removes a site with no other present bond after deleting its out-bond. Thus removal cannot destroy a future unused bond. This proves both that every initially permitted stopped trail can be traced and that the expansion's branch choices recover precisely those trails. A site has at most two departures, and the factor \((3/5)^{N_{\mathrm D}}\) belongs in \(a_D(w)\), independently of partition ratios.

6. **Step identities and pair expansion — `sec6-walks.tex:100–238`, `l:stepid`, `p:pairwalk`.** The U identity uses moments of degrees at most four and yields coefficients \(1/3\) and \(1/15\). The residual D second moment is \(1/5\), giving the same \(1/15\) coefficient. At an admissible D departure the coefficient is \(1/5\), and the removed site contributes no additional scalar. Summation over coordinates and finite iteration yield the unnormalized identity before any division. Every nonterminal iteration consumes an unused bond, so branches ending in an empty sum contribute zero and the process terminates. For a hit of the target, its status is unchanged. A U target has squared norm one. A D target had at most one present bond before tracing; after its first arrival it is isolated, has no original legs, and has expected squared norm \(3/5\) under either pin choice. The target assumptions, including the restriction when the target is protected, are necessary and are present in the statement.

7. **Ratios and response coefficients — `sec6-walks.tex:240–435`, `d:ratios`, `l:response`.** Summing the departure spin gives \(\rho=J^\bullet/I^\bullet\), with the stated formulas for one, two, and three neighbours. At a D departure the one-bond integral is one, so both ratios are exactly one. For a U departure outside \(S\), every neighbour is at original depth at least two and therefore has no original leg. After deletion of the departure site each neighbour has at most three factors. The neighbours are pairwise nonadjacent, so conditional independence and `l:35` give conditional means of norm at most \(3/5\). These facts justify all intervals for \(I^\bullet,J^\bullet\), and free pair positivity is used within degree four. The logarithmic-mean formula has the correct response sign, including coincident arguments. The positive lower bound for \(\alpha_j\), both logarithm bounds, and every rational margin check exactly. The estimates \(\rho^0\le1\) and \(\rho^\tau\le12/5\) follow without any local certificate. The lemma concerns actual departures, so the zero-neighbour case needs no step ratio.

8. **Exposure — `sec6-walks.tex:437–486`, `l:exposure`.** Step ratios remain attached to their original trace prefixes; reordering merely reorders their scalar product. The telescoping identity is exact for every ordering. The factors after the exposed difference can be discarded because every free step ratio is at most one. The inequality \(|b-c|\le\max(b,c)|\log b-\log c|\), together with \(x_j\ge1\), supplies the remaining exposed factor. With no U departures both products equal one and the right-hand side is empty.

9. **Covered patterns and the local comparison — `sec6-walks.tex:488–653`, `d:pattern`, `h:H1`, `l:local`.** The radius-two diamond has four corners with two external slots each and four tips with three each, giving twenty slots. Every covered template has at most four factors per site, even when a D corner receives both artificial external slots. Thus both local partition sums are positive, and each slot enters affinely. The proof of `l:local` is genuinely conditional on the stipulated covered non-tip data; it does not assert that every domain departure is covered. Original depth at least three puts the entire diamond in \(G\) and excludes original legs at the passage and its neighbours.

   For each fixed outside configuration, integrating an actual tip gives a positive constant times an affine factor with mean in the closed \(3/5\)-ball. This also holds for D tips, absent internal bonds, and removed tips. When the covering pattern requires a bond missing in the actual network, the required effective mean is zero. The full range assertion of `l:35` realizes each required mean with three unit fields at a covering U tip. The replacement multiplies current and next sums by exactly the same positive scalar. The at most eight corner slots are then filled or resolved using the affine convex decomposition, with identical nonnegative coefficients for both sums. Every term now satisfies (H1); undoing the scalar and summing against the common nonnegative outside weight preserves the inequality. No independence of the outside spins or realizability constraint on the twenty covering fields is assumed. Division is only by positive global partition functions.

10. **Trail weights and the one-point estimate — `sec6-walks.tex:655–775`, `d:weights`, `h:H2`, `l:onepoint`.** A first lattice departure from an initially D site is bounded by \(x_{\mathrm{type}}/3\), and a later departure has coefficient exactly \(1/5\) and ratio one. A true U departure is a first lattice departure. A covered U step is bounded by its lattice weight for both pin choices; an uncovered U step costs at most one extra factor \(12/5\), since its lattice weight is at least \(1/3\). Therefore the same product bound holds for both ratios before taking their maximum. Twelve exceptions can occur anywhere along the trail. The absent initial bond supplies precisely the extra first-step restriction in (H2); later reversals would reuse a bond. Each trail has length at least the ambient distance to the original \(S\). Enlarging the finite network sum to all plane trails and summing \(C_Vq^n\) gives the stated constant \((12/5)^{12}C_V/(1-q)\). If there is no stopped trail, the sum is zero. If a start exists, finite nonempty \(G\) guarantees nonempty \(S\), so no infinite exponent is used in this argument.

## Statement table

“Well posed” below marks a definition or input contract, rather than a newly proved estimate. All source locations are relative to the supplied paper directory.

| Label; source location | Content | Verdict | Dependencies |
|---|---|---|---|
| `d:moment`; `sec2-moments.tex:8` | Twelve-point functional, U/D laws, distances, empty products, TV/variance/Hamming conventions | Well posed | Explicit coordinates; finite sums |
| `l:moments`; `sec2-moments.tex:35` | Unit antipodal support, moments through degree four, orthogonal polynomial covariance, product version | Sound | `d:moment`; \(\phi^2=\phi+1\); tensor contractions |
| `d:pinmodel`; `sec2-moments.tex:97` | Original legs, protected layer, deletion without new pins, pinned/free partition sums and ratios | Well posed | `d:moment`; positivity supplied by `l:finitefacts` |
| `l:finitefacts`; `sec2-moments.tex:126` | Positive normalizers, conditional independence, free product-correlation positivity, norm bounds | Sound | `l:moments`; nonnegative factors; at most four incident factors; degree restriction for inserted observables |
| `l:35`; `sec2-moments.tex:197` | Mean norm at most \(3/5\) for up to three ball fields; exact full-ball range for three unit fields | Sound | `l:moments`; positive normalizers; convex decomposition; continuity/IVT; polynomial covariance |
| `l:exact`; `sec2-moments.tex:297` | Degree-four product quadrature, including diluted sites and signed factors | Sound | Equality of local moments; finite monomial expansion |
| `h:P`; `sec2-moments.tex:338` | Pair-response property for holes outside the original protected layer | Well posed | `d:pinmodel`; original ambient distances; positive normalizers |
| `d:domain`; `sec6-walks.tex:8` | U/D/X networks, consistent domains, auxiliary networks, unchanged original legs | Well posed | `d:moment`; `d:pinmodel`; `l:finitefacts` |
| `d:trace`; `sec6-walks.tex:50` | Stopped bond trails, status changes, admissible starts, coefficients and telescoping ratios | Well posed; invariants sound | `d:domain`; degree bounds at departures; positivity |
| `l:stepid`; `sec6-walks.tex:100` | U propagation with coefficient \(1/3\), D removal with coefficient \(1/5\) | Sound | `l:moments`; U degree at most four; D at most one factor |
| `p:pairwalk`; `sec6-walks.tex:148` | Finite pair expansion; target constants \(1,3/5\); degree ledger | Sound | `d:trace`; `l:stepid`; `l:finitefacts`; explicit start/target hypotheses |
| `d:ratios`; `sec6-walks.tex:240` | Step ratio formulas using \(I,J\); D ratio one | Well posed; asserted identities sound | `d:trace`; `l:moments`; `l:finitefacts` |
| `l:response`; `sec6-walks.tex:286` | Positive response coefficients with rational upper bounds; free ratio at most one; pinned ratio at most \(12/5\) | Sound | `d:ratios`; `l:35`; `l:finitefacts`; positive logarithmic mean; exact rational inequalities |
| `l:exposure`; `sec6-walks.tex:437` | Ordered difference-of-products bound for any ordering of U departures | Sound under stated ratio bounds | `d:trace`; `l:response`; positive ratios; \(x_j\ge1\) |
| `d:pattern`; `sec6-walks.tex:488` | Radius-two covered pattern class with twenty unit slots | Well posed; local positivity sound | U/D laws; finite kept-set rules; `l:finitefacts` |
| `h:H1`; `sec6-walks.tex:531` | Uniform pointwise local partition inequality at type-dependent thresholds | Well posed input contract | `d:pattern`; \(0<c_{\mathrm s},c_{\mathrm t}\le1\); established outside this part by `t:H1` |
| `l:local`; `sec6-walks.tex:546` | Covered departure ratio at most \(1/c_{\mathrm{type}}\), uniformly in actual external data | Sound conditional on (H1) and covered-data premise | `d:pattern`; `h:H1`; full range and ball-field bound in `l:35`; convex slot filling; `l:finitefacts` |
| `d:weights`; `sec6-walks.tex:655` | Open lattice trail weights using first departures and revisits | Well posed; comparison with initially D sites sound | Positive H1 thresholds; `d:trace`; initial-reversal convention |
| `h:H2`; `sec6-walks.tex:684` | All-length open-trail sum bounded by \(C_Vq^n\) with fixed initial data | Well posed input contract | `d:weights`; \(C_V\ge1\), \(0<q<1\); established outside this part by `t:inputs` |
| `l:onepoint`; `sec6-walks.tex:695` | Common pointwise and summed bounds for pinned/free trail ratios with at most twelve exceptions | Sound under all stated hypotheses | `d:trace`; `l:response`; `l:local`; `d:weights`; `h:H2`; absent incoming bond; exception-count premise |

## Cross-section hypotheses and notation

- The fixed thresholds in `sec6-walks.tex:538–539` agree with `t:H1` and `t:inputs`: \(961/1000\) and \(187/200\), both in \((0,1]\). The reciprocal weights are consequently \(1000/961\) and \(200/187\). Appendix C uses exactly these weights, a revisit defined by an earlier **departure**, revisit coefficient \(1/5\), and the forbidden initial reversal. Its stated (H2) constants have \(C_V=10\ge1\) and \(0<q<1\). These match the hypotheses of `l:onepoint` without a parity or boundary change.
- The closure result `l:closure` in Section 7 supplies the non-tip pattern premise for the first expansion after explicitly dropping the irrelevant kept flag into the removed centre. This flag normalization changes no present factor. The second expansion is handled by `l:terminalcover` with the extra assumption that its start is outside \(S\). A defect can affect only departure templates within distances one or two of the first terminal site: four plus eight sites. Each has at most one U departure, giving the twelve-exception premise. These are hypotheses/results outside the assigned proof audit, and their stated conclusions match the Section 6 lemmas they invoke.
- Section 7's two applications of `p:pairwalk` respect its target restrictions. The original distance-two target has lost its bond to the removed centre, so a U target has at most three factors; a D target has at most one present bond by `d:pairenv`. In the second expansion the protected target has already lost the first trail's arrival bond and therefore has at most three factors. The recursion is restricted to distance \(d\ge1\), so neither expansion starts in \(S\).
- No finite-energy or full-support assertion for arbitrary unit pins is imported from the frame specifications. Section 6 needs positive partition sums and positive conditioning fibres, which Section 2 proves. Free positivity is never applied to antiferromagnetic bond factors. Quadrature is used on summed polynomial expressions, with its local degree restrictions intact.
- The notation \(D\) is overloaded for the twelve-point alphabet and a network. This is understandable in the text but should become separate types/names in Lean. Superscript \(0\) means that all original pin factors are omitted, not that zero is used as a unit pin. Every distance to \(S\) refers to the original \(S(G)\), and no trace or deletion changes that set.

## Exact computations

The accompanying `exact_checks.py` uses standard-library rational arithmetic and sparse polynomial arithmetic, with one process and no data-file reads. Running

```text
python3 /home/ubuntu/aklt/reports/REF2_4/exact_checks.py
```

passes all checks:

- The identities \(1+\phi^2=\phi+2\), \((\phi+2)^2=5\phi^2\), and \(1+\phi^4=3\phi^2\) hold in exact \(\mathbb Q(\phi)\) arithmetic.
- The norm identity in `l:35` has zero polynomial residual in the three pair products, after imposing unit lengths.
- All 255 multilinear coefficients of the U step identity, for \(k=0,1,2,3\), and all 15 coefficients of the D identity, for \(k=0,1\), agree exactly with the stated moment tensors.
- Both displayed values of \(B(s)/3\) and their cross-product margins \(224059660\), \(50021800\) agree. The lower bound for \(\alpha_j\) is \(175/5916>0\), its upper bound is \(6061317/33500000\), and the latter's margin below \(\bar\alpha\) is exactly \(173/33500000>0\).

These computations check algebraic identities and constants, not just sampled numerical instances. They supplement the proof audit and do not verify the external H1/H2 certificate archives.

## Formalization notes

1. **Use a separate-degree ledger.** The needed maximum degrees are: unmarked partition sites, four; moving U mark, \(3+1=4\); moving D mark, \(1+1=2\); fixed U target before arrival, \(3+1=4\); terminal protected site distinct from the target, \(4-1+1=4\); terminal U target, \(3-1+2=4\); isolated terminal D target, two. A covered tip has \(3+1=4\) factors and a covered corner at most \(2+2=4\). This avoids any appeal to moments beyond degree four or to pointwise rotational invariance of a discrete law.

2. **Represent flags and present bonds separately.** A kept flag into an X site need not correspond to a factor. Tracing changes flags at both endpoints of the selected bond, then changes the departure status. Prove that a D removal has no other present bond before using any identity of partition sums. Keep the original volume, protected layer, and original-leg index set fixed across all these updates. The terminal protected-site defect belongs to the auxiliary-network type.

3. **Establish positivity before division and logarithms.** Global partition positivity follows from the finite twelve-letter avoidance argument, without full support of the interacting law. Define conditional distributions only on positive fibres. For tip replacements use the separate three-field normalizer bound; arbitrary outside spins may have norm less than one. Logarithmic means must include their equal-argument value, rather than a totalized quotient with denominator zero.

4. **Make the finite expansion genuinely finite.** Induct on the number of remaining present bonds, or on a decreasing finite fuel equal to the initial bond count. Record an explicit bijection between surviving expansion branches and stopped trails. Dead ends give zero by the empty-sum identity. The zero-length trail has its specified start and empty edge product; it should not be confused with a sequence lacking a starting vertex.

5. **Preserve the D target invariant.** The value \(3/5\) at a D target is an isolated-site calculation after arrival. It is not a universal identity for the squared norm in an interacting D law. Likewise, coefficient \(1/5\), diluted positive-degree moment factor \(3/5\), and partition ratio one at a D departure are three distinct facts.

6. **The full-ball range can avoid trigonometry.** An equivalent implementation of the proof in `l:35` takes orthonormal \(e,f\), a parameter \(t\in[-1/2,1]\), and fields
   \[
   a=e,\qquad b=t e+\sqrt{1-t^2}\,f,\qquad
   c=t e-\sqrt{1-t^2}\,f.
   \]
   The mean is
   \[
   \frac{2t^2+5t+2}{5(t^2+t+1)}e.
   \]
   Its coefficient is continuous, equals zero at \(-1/2\), and equals \(3/5\) at one. The intermediate value theorem supplies every required norm; choosing \(e\) in the desired direction supplies the vector. This is an optional proof representation, not a correction to the source.

7. **Treat covering as an existential replacement for each outside configuration.** The four covering tips need not preserve their actual statuses, kept sets, or original slot fields. What must be preserved is the integrated affine factor, up to the same positive scalar in current and next sums. Resolve the corner fields using a common finite product distribution of sign choices. Apply (H1) pointwise and then average. No compatibility of slot values sharing an outside endpoint is required by (H1).

8. **Keep exposure order separate from trace order.** The \(\rho_j\) are computed along the actual trace. A permutation is used only in the product-difference identity. Include the empty U-departure case explicitly. The estimates rely on positive free ratios at most one and on majorants at least one.

9. **Take the pointwise maximum before summation.** Prove the same per-trail majorant for both pin choices, then bound \(a_D(w)\max\{R_D^\tau(w),R_D^0(w)\}\). Separate bounds for the two summed ratios would not by themselves prove the stated bound on their summed maxima. The source follows the required order. Only after the trail-to-plane injection is established should the finite length sum be enlarged to the geometric series.

10. **Preserve computational inputs as separate obligations.** The local and open-trail contracts are mathematical assertions with precise quantifiers. Theorem `t:inputs` supplies matching parameters, but native archive checks are not Lean proofs. Formalizing these assigned sections can proceed parametrically in (H1)/(H2); discharging those inputs belongs to the separate certificate formalization.

## ORCH-SUMMARY

- VERDICT: SOUND for Sections 2 and 6; no Critical, Major, or Minor findings.
- Full supplied LaTeX read for context; assigned sections checked line by line.
- Moment identities, degree-four covariance, normalizer positivity, and quadrature are valid.
- The mean bound is sharp, and its full closed-ball range supports the tip covering step.
- Trace invariants justify every step and the finite branch/trail bijection.
- Pair-expansion target constants and all observable degree restrictions are correct.
- Response signs, logarithmic means, rational constants, and D ratio one check out.
- Exposure handles arbitrary orders and empty products correctly.
- Local covering handles missing slots, D/removed tips, and arbitrary bounded outside spins.
- The one-point estimate bounds the pointwise maximum before summing and permits twelve exceptions anywhere.
- H1/H2 parameters and later start/target hypotheses match the stated contracts.
- External certificate data were not inspected; their independent verification is outside this part.
- Exact rational/polynomial checks pass in `exact_checks.py`; no floating-point evidence is used.
- No input modifications or sub-agents; no repair required.
