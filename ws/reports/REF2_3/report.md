VERDICT: SOUND

The verdict covers Section 5 and Appendix B. I read the complete LaTeX paper for context and checked `sec5-window.tex:1–781` and `app-topology.tex:1–183` line by line. Results from other sections were checked for applicability under their stated hypotheses; the numerical certificates underlying the response theorem were outside this audit.

## Numbered findings

None. Critical: 0; Major: 0; Minor: 0. I found no false statement, missing hypothesis, invalid proof step, or necessary LaTeX repair in the assigned part. The details below record the substantive checks, including the qualifications that must survive formalization.

## Statement table

All file paths in this report are relative to `/home/ubuntu/aklt/review/REF2/paper/`.

| Label and location | Content | Verdict | Dependencies and applicable hypotheses |
| --- | --- | --- | --- |
| `l:shellgeom`, `sec5-window.tex:27` | At most one exceptional shell; shell inclusion; bound `8 l_0` on the end strips; nonexceptional side clearance; the preceding-shell separator. | SOUND | `d:shells`, `sec4-periodic-gap.tex:10`; integer `l_0 >= 1`, integer `u >= M_g(l_0)`, exterior site at ambient infinity-distance one. Clearance and the end-strip bound both exclude `I_0`. |
| `l:cut`, `sec5-window.tex:128` | A uniform absolute bound `E` on the change of `log Psi` gives a positive reference window law, the factors `exp(±2E)`, and TV at most `1-exp(-2E)`. | SOUND | `d:framemodel`; `d:pinmodel`; `l:threeframes`; `l:exact`; `l:finitefacts`; precisely the stated separation and no-adjacency assumptions. Only original legs are retained. |
| `l:removal`, `sec5-window.tex:233` | Removing an ordered connected set costs at most one seed constant, `4 F` at its first site, and `2 F` at every subsequent site. | SOUND | `h:P`; `l:moments`; `l:35`; `l:finitefacts`; original depth at least three at every removed site; distinct sites, with a predecessor adjacent to each site after the first. |
| `d:thickcut`, `sec5-window.tex:361` | The taper `U`, its exterior star-boundary `X_0`, its nearest-neighbour thickening `X`, and the two retained pieces. | WELL-POSED | `d:shells`; `l_0=64`; a nonexceptional integer `2 <= i <= s`. Real scale parameters and integer site functions are distinguished correctly. The subsequent assertions use `s >= 390`. |
| `l:cutgeom`, `sec5-window.tex:382` | Connectivity of the taper and its complement; containment and clearance; raw depths at least 14; at most 48 near sites per level; weighted sum; thickened depths at least 13; cut separation. | SOUND | `d:thickcut`; nonexceptional clearance in `l:shellgeom`; elementary metric and integer inequalities. The proof establishes the explicit threshold `s_0=390`. |
| `l:Xconn`, `sec5-window.tex:670` | The cut is finite, nonempty, nearest-neighbour connected, and admits the removal ordering. | SOUND | `l:cutgeom`; Appendix B's `l:boundaryconn` and `l:thicken`; ordering by distance from a root in the induced nearest-neighbour graph. |
| `t:cutMOS`, `sec5-window.tex:696` | `P(A,theta)` implies `W(64,p_0,M_star)` with the displayed `E`, `p_0=exp(-2E)`, and a common integer threshold. | SOUND | `h:P`, `d:W`, `l:cutgeom`, `l:Xconn`, `l:removal`, `l:cut`, and the explicit exponential tail bound. All constants are independent of colouring, translation, exterior letters, and permitted shell index. |
| `l:boundaryconn`, `app-topology.tex:10` | A finite nonempty star-connected set with star-connected complement has nonempty star-connected exterior star-boundary. | SOUND | Both connectivity assumptions are used. The finite even-edge decomposition into star-triangle boundaries is proved within the lemma. |
| `l:thicken`, `app-topology.tex:138` | Unions of nearest-neighbour crosses around a star-connected set are nearest-neighbour connected; their weighted depth sum increases by at most `5/vartheta`. | SOUND | Finite nonempty `X_0`; ambient lattice distances; for the weighted estimate, finite `G` containing all of `X` and `0 < vartheta < 1`. |

## Proof audit

### Shell geometry

At `sec5-window.tex:40`, the signed coordinate permutations and translation are applied only to geometry. They do not require a symmetry of a chosen plane colouring or of its site alphabets. Every exterior site can be put in the stated form `y=(beta,-u-1)` with `-u-1 <= beta <= u+1`.

The inequalities at lines 50–58 hold at the inclusive threshold. In particular, the proof allows nonintegral `s=u^(1/4)`. For all indices through `i_1=floor(s)+1`, one has `k_i <= s^2+s`, while distinct radii differ by at least `floor(s)>2s/3`.

The corner argument at lines 60–76 is valid: only one corner can have infinity-distance strictly less than `u` from `y`; any corner causing an exception is within that range. Two exceptional radii associated to that corner would violate the reverse triangle inequality and the strict `2s/3` bound. Empty shells cause no exception.

The side-clearance argument at lines 78–100 handles both parallel exterior half-planes and the extreme values `beta=±(u+1)`. A vertical side meeting the physical square contains its lowest clipped point on the bottom edge, which belongs to `D_i`. Nonexceptionality therefore supplies the needed clearance. Consequently, at lines 102–108, a point of `A_i` cannot be on a side parallel to its nearby exterior half-plane; each perpendicular side contributes at most `l_0` lattice sites. The count `8 l_0` is valid with possible double counting.

At lines 110–123, `k_i >= i s-1 > (i-1)s` proves shell inclusion. For the final separator statement, integer radii force both bounding values to equal `floor((i-1)s)`. This remains true when `(i-1)s` is an integer. The final assertion is valid for every integer `i>=2`, including indices for which `F_i` is empty.

### Cut factorization

At `sec5-window.tex:155–177`, the window product is a nonempty finite configuration space, even for an empty window. Its actual weight `W_B` is strictly positive because internal bonds join distinct frames. All factors into the exterior are assigned to `G`: the assumption on `B` excludes a missing direct window-to-exterior factor.

The quadrature step in `e:windowfactor` is legitimate. The window letters are fixed while summing over `G`, and every summed variable has at most four incident bond or original-leg factors. No equality of marginal laws on different alphabets is asserted.

At lines 179–199, the factorization uses only the original legs with tails in each retained piece. The hypotheses exclude exterior pins from `G_1` and window pins from `G_2`; there are no cross-bonds between the pieces. Empty pieces contribute one. The sign and free normalizers are correct:

\[
 Z_G^{\eta s}
 =e^{-e(\eta,s)}
   \frac{Z_G^0Z_{G_2}^{\eta}}{Z_{G_1}^0Z_{G_2}^0}
   Z_{G_1}^{s}.
\]

At lines 200–228, the positive normalizer `Q` exists, the reference law is independent of the exterior letters, and its normalization accounts for the second factor `exp(±E)`. The assumption implies `E>=0` because admissible assignments exist. Both window laws dominate `exp(-2E) nu`, so the stated TV estimate follows from their overlap. The empty-window case is covered explicitly.

### Removal estimate

At `sec5-window.tex:247–285`, every prefix of removals is contained in `G \ S(G)`, as required by `P`. There are four surviving neighbours at the first removal and at most three thereafter. The removed spin has no original pin. The second- and fourth-moment contractions in `e:removalpolynomial` are correct, and `e:removaltelescope` has the correct sign.

At lines 287–319, the surviving neighbours are pairwise nonadjacent. Each has original depth at least two, hence no original leg, and at most three remaining factors. Conditional independence and `l:35` apply separately on every positive conditioning fibre for both the pinned and free laws. Their conditional means have norms at most `3/5`. This proves the lower bounds

\[
 \mathbb E I_j\ge1-\frac{3k}{50}\ge\frac{41}{50}
 \quad(k\le3),\qquad
 \mathbb E I_1\ge1-\frac6{25}-\frac3{15}
 =\frac{14}{25}>\frac12.
\]

At lines 321–337, every response pair survives, has ambient distance two, and has the removed `x_j` as a common neighbour in the current removal set. The original protected set is used throughout. The one-Lipschitz estimate gives distance at least `b_G(x_j)-3` to that set. Since `0<theta<1`, replacing the actual response exponent by this lower bound has the correct inequality direction.

At lines 339–356, the logarithm is 2-Lipschitz on the relevant interval. At most three pair terms occur after the seed, giving `2 F`; the seed has six, giving `4 F`. Its quartic difference is at most six, producing the additional `4/5`, safely enlarged to one. Each observable insertion adds one degree at an endpoint that has lost its bond to `x_j`, so the separate degree remains at most four. The cases `k=0,1`, a singleton removal set, and later removals with several predecessors are harmless.

### Tapered set and thickened cut

At `sec5-window.tex:418–439`, all displayed scale inequalities follow from `s>=390`, `u=s^4`, and integer `2<=i<=s`. In particular, `k-T-1>(i-1)s` provides clearance from the inner boundary of `F`, with `T=s/12` real.

At lines 441–486, the radial moves reduce integer `t` by exactly one and decrease `h` by at most one. They preserve both taper inequalities. The core `K` is nonempty: each clipped coordinate interval is nonempty and contains an endpoint of the radius-`k` interval because `32<=k<=u-31`. Choosing the resulting contained corner joins every clipped side segment by nearest-neighbour paths. Thus the radial star-paths prove the required connectivity of `U`.

At lines 488–512, all three complement-path constructions terminate outside `C` while avoiding `U`. In the inner case the sum of coordinate displacements from `y` strictly decreases, even when the maximum displacement stays constant. In the taper-failure case the outward coordinate move decreases `h` by one and changes `t` by at most one, so the strict inequality `h-t<32` persists. This proves nearest-neighbour, hence star-, connectivity of `U^c`.

At lines 514–529, integer depth outside `A_i` is at least 65, so every point of `B` and all its nearest neighbours belong to `U`. The two separate clearances `h>=32` and `rho>=k-T` put `U` and all its neighbours inside `F`. Every raw boundary point has `h>=31` and sufficient radial clearance, hence belongs to `G`; finiteness and nonemptiness follow as stated.

At lines 531–572, the complement decomposition

\[
 G^c=B\cup C^c\cup(C\setminus F)
\]

is exact. The lower bounds on distances to its three pieces imply `e:sitecutdepth` in the ambient one-norm. For near sites, the integer level satisfies `30+t<=h<32+t`; the three entries of the minimum each dominate `max(t,16)-2`. For far sites, `T<t<=T+1` and `h>=30+t`, giving depth at least `T-1`. Both cases imply depth at least 14. Empty distance targets are compatible with the paper's infinity convention.

At lines 574–624, near sites lie at the intersection of one of at most two radius levels about `y` and one of at most three depth levels about the square's centre. The proof excludes coincident supporting lines before counting intersections. The inside, beyond-the-specified-edge, and beyond-the-opposite-edge cases exhaust all integer line coordinates. Nonexceptional clearance and `s/3-2j>=s/6>32` exclude coincidence in the inside case. There are then at most eight intersections for each pair of square boundaries, so 48 is a valid upper bound. The depth interval actually permits at most two integer levels; using three is safe.

At lines 626–639, the near sum is computed correctly:

\[
 \sum_{j\ge0}\vartheta^{\max(j,16)-2}
 =\vartheta^{14}\left(17+\frac{\vartheta}{1-\vartheta}\right).
\]

Replacing the numerator `vartheta` by one only enlarges the bound. The far cardinality is at most `(2u+1)^2`, because `X_0` was already proved to lie in `C`; the displayed factor four is an additional safe enlargement.

At lines 641–668, nearest-neighbour thickening decreases original depth by at most one, giving depth at least 13 and excluding `B` and `S(G)`. A cross has five sites, which gives the stated factor `5 vartheta^(-1)` even with overlaps. The definitions partition `G \ X` into the two retained pieces. A bond crossing from `U` to `U^c` would meet `X_0`, and the previously established containments give every remaining no-adjacency hypothesis of `l:cut`.

At lines 670–692, Appendix B applies with `A=U` using both connectivity conclusions, and then to `X_0` using its finiteness and nonemptiness. Ordering by induced nearest-neighbour graph distance gives exactly the predecessor condition needed by `l:removal`; ambient distance is not substituted for that graph distance.

### Window theorem and constants

At `sec5-window.tex:712–733`, setting `c=-log(theta)>0` gives

\[
 4(2u+1)^2\theta^{s/12-1}
 \le36\theta^{-1}s^8e^{-cs/12}
 \le K_\theta s^{-2},\qquad
 K_\theta=36\theta^{-1}10!\left(\frac{12}{c}\right)^{10}.
\]

The exponential-series inequality used here has a positive argument. The choice `M_star=ceil(max(390^4,K_theta^2,1))` implies `s^2=sqrt(u)>=K_theta`, so the far term is at most one. It also meets the explicit geometric threshold. No limiting or uniformity assertion in `theta` is needed.

At lines 735–759, the cut is nonempty, all its depths exceed three, and its ordering satisfies the removal hypotheses. Exterior and window letters give an allowed original unit-pin assignment; repeated outside endpoints pose no restriction because `P` permits unrelated original pins. The seed exponent is nonnegative and can be bounded by one. Combining the removal coefficient `2A theta^(-3)` with the thickening factor `5 theta^(-1)` gives exactly `10A theta^(-4)`. The displayed `E` therefore bounds the absolute cut cost for all exterior and window assignments.

At lines 761–781, the factorization lemma gives a common minorization for each fixed window and hence exactly the quantifiers in `d:W`, including arbitrary pairs of admissible boundaries. The reference law may depend on the colouring and placement, whereas `p_0` and `M_star` do not. The finite moment identity is used only for summed partition polynomials. Empty windows and either lattice parity are consistent with the conclusion; no global sign change or extra colouring symmetry enters this section.

### Appendix B

At `app-topology.tex:19–34`, eliminating each diagonal by its triangle boundary preserves evenness and creates no other diagonal. At lines 36–86, the half-plane parity identity makes the plaquette coefficients `n(i,j)` finitely supported. The stated coefficients recover every horizontal edge. Summing the even-degree equations recovers every vertical edge, including rows below the chosen support box; the endpoint bounds justify the zero terms there. Each plaquette boundary splits into two star-triangle boundaries. Thus the claimed decomposition of every finite even edge set is established without a planar embedding assumption for crossing diagonals.

At lines 88–124, a disconnected linked-edge graph would define a parity functional vanishing on every triangle, hence every finite even edge set. Paths inside `A` and inside `A^c` produce a closed walk whose odd-traversal edge set crosses the cut in exactly the two chosen distinct edges, contradicting that functional. Both connectivity hypotheses are used here. Repeated vertices or edges in the paths cause no problem because traversal counts are taken modulo two. One-point paths are allowed.

At lines 126–135, the outer-endpoint map covers the entire exterior star-boundary. Linked edges have equal or star-adjacent outer endpoints, giving the claimed paths after repetitions are removed. The rightmost-site argument proves nonemptiness.

At lines 150–182, crosses at axis-adjacent centres overlap in both centres; crosses at diagonal-adjacent centres overlap in the two displayed intermediate sites. A star-path therefore joins their unions by nearest-neighbour paths. For the weighted inequality, finite `G` has nonempty complement, its distance function is one-Lipschitz in the one-norm, and decreasing base `0<vartheta<1` gives the stated direction of comparison. Counting overlaps more than once is valid because all summands are nonnegative.

## Exact computational checks

The computations used a single Python 3 process at a time and integer or rational arithmetic. They read no certificate archives and made no changes to the paper. These finite checks support the proof audit; their scope is the configurations described here.

1. **Shells:** 20,352 shell/placement cases, of which 20,302 were nonexceptional, with `l_0` in `{1,2,64}` and radii `u=t^4`, `t^4+1`, and `(t+1)^4-1`, where `t=max(16,6(l_0+1))`. Selected exterior placements included corner-adjacent sites, equality and neighbouring positions at the exception threshold, and the last permitted shell. Every tested exceptional-index count, shell inclusion, side clearance, and `8 l_0` bound passed.
2. **Tapered cuts:** 26 permitted configurations with `u` in `{390^4,390^4+1,391^4-1}`, indices two and three, and selected central, corner-adjacent, and exception-threshold exterior placements. Interval representations generated `U`, `X_0`, and `X` exactly. Checks covered connectivity of `U`, its complement, `X_0`, and `X`; window-neighbour containment; clearance from `F^c`; exact one-norm depths to `G^c`; and the near-level count. The largest observed near-level count was eight; minimum observed raw and thickened depths were 31 and 30, respectively, above the claimed 14 and 13.
3. **Topology:** all 65,535 nonempty subsets of a `4 x 4` lattice box were enumerated. Of these, 36,603 satisfied both star-connectivity hypotheses. Every such exterior star-boundary was nonempty and star-connected, and every corresponding thickening was nearest-neighbour connected. A surrounding `8 x 8` box with its exterior ring represented complement connectivity. Another 593 star-connected sets failed the complement hypothesis and were excluded.
4. **Arithmetic:** exact fractions verified the removal lower bounds, the seed cost `4/5<=1`, the coefficient `10A theta^(-4)`, and the near-series identity at several rational bases. Floor and exception comparisons in the geometry checks used integer fourth powers, so nonintegral fourth roots were not rounded numerically.

## Formalization notes

1. **Carry the original volume explicitly.** Represent a partition sum by its original volume, surviving set, retained bonds, and retained original legs. Factoring into `G_1,G_2` must restrict this leg data. Reinitializing `d:pinmodel` on a smaller surviving set would add unwanted pins and invalidate the identities.
2. **Keep the two metrics separate.** Shells, corners, the taper, and `X_0` use the infinity norm. Protected depths `b_G`, response exponents, and the thickening `X` use the one-norm. Root ordering in `l:Xconn` uses distance in the graph induced by `X`.
3. **Make the index and scalar types explicit.** Sites and radii `u,k_i,rho,t,h` are integral; `s=u^(1/4)` and `T=s/12` are real. Prove the floor identities and the inclusive/strict inequalities before using arithmetic automation. The final assertion of `l:shellgeom` is over all integer `i>=2`, not just indices below `i_1`.
4. **Preserve the nonexceptional qualifier.** It is essential for the parallel-side assertion as well as for the end-strip estimate. The near-site count depends on that assertion to rule out coincident supporting lines.
5. **Distinguish nonnegative weights from positive normalizers.** The uniform unrotated pin model can have zero individual configuration weights. Conditional independence and the mean bound are used only on positive fibres. Strict positivity of every normalizer comes from `l:finitefacts`; strict positivity of actual frame window weights comes from the separated frames.
6. **Record degree budgets with insertions.** For quadrature, window letters are fixed. For removal, each inserted endpoint has lost its bond to the removed site. Quartic seed terms use four distinct endpoints. No degree-five moment or invariance of the finite alphabet on arbitrary functions is needed.
7. **Establish nonemptiness before choosing witnesses.** Use the clipped core for `U`, a maximal coordinate for `X_0`, and then the thickening for `X`. A nonempty finite original `G` also has nonempty `S(G)`, so response exponents are finite integers in nonvacuous removal uses. Empty pieces and windows have partition/product value one.
8. **Use finite supports for the topology algebra.** Model unoriented edges by unordered pairs with distinct endpoints; finite edge sets form an `F_2` space under symmetric difference. Restrict half-plane degree sums to the finite vertex support. The plaquette-coefficient construction supplies a direct proof of cycle generation, and avoids needing a Jordan-curve theorem for the graph with both diagonals.
9. **Keep path multiplicities until reduction modulo two.** A closed walk may repeat edges; its odd-traversal edge set is even. The two cut edges in the contradiction remain distinct because they were chosen in different linked-edge components. The outer-endpoint map need not be injective.
10. **Extract the explicit scale from the proof.** Formalize `l:cutgeom` with threshold 390, or expose that witness as a corollary. This supplies the exact threshold used by `t:cutMOS`. Positive bases and denominators justify all negative powers, logarithms, and reciprocals; `u>=K_theta^2` is converted to `sqrt(u)>=K_theta` using `K_theta>0`.

## ORCH-SUMMARY

VERDICT: SOUND for Section 5 and Appendix B.
No Critical, Major, or Minor defect found; no repair required.
Read the whole LaTeX paper; audited both assigned files line by line.
The cut factorization retains the correct original legs and free normalizers.
Removal uses P only for admissible surviving distance-two pairs and protected prefixes.
The single quartic seed cost and all logarithmic constants are valid.
The taper works at s=390, including nonintegral-scale rounding cases.
Nonexceptionality correctly excludes coincident sides in the 48-site count.
Raw/thick depths 14/13 and the factor 5/theta suffice for the displayed E.
The explicit M_star makes the far contribution at most one.
Appendix B's finite F_2 cycle argument and connected thickening are valid.
Exact checks passed: 20,352 shells, 26 tapers, and all 4 x 4 subsets for topology.
Formalization must preserve the original volume, metric distinctions, and positive-fibre conditions.
Other sections' results were checked for applicability; external certificate data were not audited.
