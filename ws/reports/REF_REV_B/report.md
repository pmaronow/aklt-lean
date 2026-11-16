VERDICT: SOUND WITH FIXES

The new text proves `t:cutMOS`, including the displayed values of \(E\) and \(p_0=e^{-2E}\), assuming the supplied interface results. I found no internal mathematical error or missing substantive proof step. The shared shell-geometry statement needs an explicit hypothesis to match the version proved here. This correction does not change the window theorem or its constants.

The review covers `part/sec5-window.tex`, `part/app-topology.tex`, and `part/compile-wrapper.tex`, using `interfaces.tex` as the contract for imported results. No original-manuscript assertion is used to fill a gap. Locations below are relative to `/home/ubuntu/aklt/review/REF_REV_B/`.

**Numbered findings**

1. **Major — synchronize the shell-geometry export with its necessary nonexceptional-index hypothesis.**

   **Location:** `interfaces.tex:321`, label `l:shellgeom`, compared with `part/sec5-window.tex:28` and the explanation at `part/sec5-window.tex:16`.

   **Exact claim:** The interface says that every indicated parallel side meeting \(C_u(a)\) has distance at least \(s/3\) from the corresponding exterior half-plane, without explicitly restricting that sentence to \(i\notin I_0\). The new lemma explicitly imposes that restriction and proves only that restricted assertion. An unrestricted export is false.

   **Counterexample:** Take
   \[
   l_0=64,\quad s=390,\quad u=s^4=23134410000,\quad a=0,
   \quad y=(2s-u,-u-1),\quad i=2.
   \]
   These satisfy the scale threshold and \(\operatorname{dist}_\infty(y,C_u(0))=1\). Here \(k_2=780\), and the left side of \(y+[-k_2,k_2]^2\) lies on \(x_1=-u\). It meets \(C_u(0)\), contains the lower-left corner, and has distance exactly \(1<130=s/3\) from \(\{x_1\le-u-1\}\). The index is exceptional, since the corner itself belongs to \(D_2\).

   **Repair:** Make the scope explicit in the shared interface, matching the new part:

   ```latex
   For the same indices \(2\le i\le i_1\) outside \(I_0\), every side of
   \(y+[-k_i,k_i]^2\) parallel to an edge of \(C_u(a)\)
   and meeting \(C_u(a)\) is at distance at least \(s/3\) from the
   exterior half-plane beyond that edge.
   ```

   The new proof already uses this assertion only for nonexceptional indices, notably at `part/sec5-window.tex:580`. If the interface sentence was intended to inherit the preceding sentence's index restriction, the repair merely makes that intended quantifier scope unambiguous. There is no missing argument for the corrected statement.

**Statement table**

“Sound” below means sound under the stated interface assumptions. Section labels are organizational; the wrapper contains no additional mathematical claim.

| Label and location | Content | Verdict | Dependencies |
|---|---|---|---|
| `l:shellgeom`, `sec5-window.tex:24` | At the stated scale: at most one exceptional index; shell inclusion; \(8l_0\) strip bound; parallel-side clearance for nonexceptional indices; location of the inner conditioning boundary. | Sound as stated in the part; interface qualification requires Finding 1. | `d:shells`; integer radii and elementary square geometry. |
| `l:cut`, `sec5-window.tex:125` | A bounded change in log boundary response across a separating cut gives a positive reference window law and comparisons \(e^{-2E}\nu\le\mu_B\le e^{2E}\nu\), hence TV at most \(1-e^{-2E}\). | Sound. | `d:pinmodel`, `d:framemodel`, `l:threeframes`, `l:exact`, `l:finitefacts`; stated separation assumptions. |
| `e:windowfactor`, `sec5-window.tex:163` | Actual window mass is proportional to \(W_B(s)Z_G^{\eta s}\). | Sound. | No boundary bond out of \(B\); quadrature at the summed sites only. |
| `e:cutfactorization`, `sec5-window.tex:183` | Pinned and free partition sums factor over \(G_1,G_2\) after deletion. | Sound, including empty pieces. | Product site laws; no bond between pieces; only original legs retained. |
| `l:removal`, `sec5-window.tex:230` | Connected-order deletion costs at most \(1+4\mathsf F(b_G(x_1)-3)+2\sum_{j\ge2}\mathsf F(b_G(x_j)-3)\). | Sound, including a singleton deletion. | `h:P`, `l:moments`, `l:finitefacts`, `l:35`; depths at least three and the stated predecessor condition. |
| `e:removalpolynomial`, `sec5-window.tex:256` | Integrating a site with \(k\le4\) surviving neighbours produces the displayed quadratic terms and, only for \(k=4\), the three quartic pairings. | Sound, interpreted by cases as the text specifies. | `l:moments`; distinct neighbours. |
| `e:removaltelescope`, `sec5-window.tex:270` | Log boundary-response difference telescopes into log expectations of the removal polynomials. | Sound. | Exact finite summation and positive normalizers. |
| `d:thickcut`, `sec5-window.tex:345` | Defines the tapered set, its outer star-boundary, its nearest-neighbour thickening, and the two remaining pieces. | Well posed. | `d:shells`; the explicitly distinguished ambient metrics and empty-set distance convention. |
| `l:cutgeom`, `sec5-window.tex:366` | With \(s_0=390\): connectivity and clearance of \(U\); raw-cut depths and multiplicity at most 48; weighted sums; thickened-cut depths and separation. | Sound. | `d:thickcut`, the qualified `l:shellgeom`, elementary lattice geometry; `l:thicken` or the direct cross-sum argument. |
| `e:sitecutscales`, `sec5-window.tex:409` | The six scale inequalities used in constructing the cut. | Sound. | \(u=s^4\), \(s\ge390\), integer \(2\le i\le s\), \(k=\lfloor is\rfloor\). |
| `e:taperconditions`, `sec5-window.tex:425` | Equivalent global description \(U=\{t\le T,\ h-t\ge32\}\). | Sound. | \(t\ge0\), \(h=0\) outside \(C\). |
| `e:sitecutdepth`, `sec5-window.tex:527` | \(b_G(x)\ge\min\{\max(t,65-h),h,s-1-t\}\) on the raw cut. | Sound. | \(G^c=B\cup C^c\cup(C\setminus F)\); Lipschitz bounds; \(d_1\ge d_\infty\). |
| `e:rawdepthrange`, `sec5-window.tex:538` | For a near raw-boundary site, \(30+t\le h<32+t\). | Sound. | One star-step to \(U\); both \(h\) and \(t\) are 1-Lipschitz for the star metric. |
| `l:Xconn`, `sec5-window.tex:650` | The nonempty thickened cut is nearest-neighbour connected and admits the required deletion order. | Sound. | `l:cutgeom`, `l:boundaryconn`, `l:thicken`; finite graph distances. |
| `t:cutMOS`, `sec5-window.tex:676` | \(\mathsf P(A,\theta)\Rightarrow\mathsf W(64,e^{-2E},M_\star)\), uniformly over proper colourings and translates, with exactly the displayed \(E\). | Sound; matches `interfaces.tex:329`. | `h:P`, `d:W`, `l:removal`, `l:cutgeom`, `l:Xconn`, `l:cut`, and the tail estimate. |
| `e:windowtail`, `sec5-window.tex:711` | \(4(2u+1)^2\theta^{s/12-1}\le1\) above the displayed common threshold. | Sound. | \(0<\theta<1\); exponential-series bound; \(u\ge K_\theta^2\). |
| `e:windowcutcost`, `sec5-window.tex:726` | The log-response cost of the constructed cut is at most the stated \(E\). | Sound. | Removal bound, raw-cut sum, thickening factor \(5\theta^{-1}\), and `e:windowtail`. |
| `l:boundaryconn`, `app-topology.tex:10` | A finite nonempty star-connected set with star-connected complement has a nonempty star-connected outer star-boundary. | Sound. | The complete finite even-edge/triangle decomposition proved in the appendix; the two stated connectivity hypotheses. |
| `l:thicken`, `app-topology.tex:130` | Thickening a finite nonempty star-connected set by one nearest-neighbour step makes it nearest-neighbour connected; the weighted cost is at most \(5\vartheta^{-1}\) times the original sum. | Sound. | Intersections of five-site crosses; Lipschitz distance to \(G^c\); \(0<\vartheta<1\). |

**Proof and hypothesis audit**

- **Shell geometry:** The coordinate reductions preserve the geometric objects and make no claim about rotating frame laws. The bounds on \(k_i\) cover \(i_1=\lfloor s\rfloor+1\), whereas the final window theorem needs only integer \(i\le s\). The corner argument establishes at most one exceptional index even when \(s\) is nonintegral. The final boundary assertion also handles an empty \(F_i\).
- **Factorization and positivity:** Each integrated site has at most four bond or original-leg factors, so `l:exact` is applied within its separate-degree bound. `l:threeframes` gives positive actual window weights on every proper-colouring bond. The deleted model introduces no pins into \(X\). Thus \(Z_{G_1}^s\) is independent of the exterior boundary, and the resulting reference law has positive finite normalizer. Empty pieces and the empty window are explicitly covered. The TV overlap calculation and both exponential comparisons have the correct signs and factors of two.
- **Removal and property P:** Every deleted site lies outside the original \(S(G)\). Every surviving neighbour has original depth at least two, hence has no original leg, and has at most three factors after removal. The neighbours are mutually nonadjacent, so their joint conditional law factors on each positive conditioning fibre. The conditional means satisfy \(|m_r|\le3/5\). This gives \(1-3k/50\ge41/50\) for \(k\le3\), and \(1-6/25-3/15=14/25\) for \(k=4\). Consequently the log Lipschitz constant 2 is valid. Each response pair survives, is at ambient distance two, and has the just-deleted common neighbour in \(Y_j\); all hypotheses of `h:P` hold. Distances are to the original protected layer throughout. Later steps have at most three pairs and cost \(2\mathsf F\). The seed has six pairs and an uncontrolled quartic contribution costing at most \(4/5\), which is correctly absorbed by 1. No quartic response hypothesis is needed.
- **Tapered geometry:** Radial paths decrease \(t\) while decreasing \(h\) by at most the same amount. The central shell intersection is nonempty and connected because each clipped coordinate interval contains a shell endpoint; the resulting side segments join at a square corner. Each complementary site has the described path to \(C^c\), proving the required complement connectivity. The depth estimate separately accounts for the window, the exterior square, and the inner removed square. In counting near sites, the nonexceptional clearance excludes coincident supporting lines; without that step an intersection could be a long segment. The bound of three depth levels is conservative: \([30+j,32+j)\) actually has only two integer levels. The constants 48, 14, and 13 are therefore valid.
- **Planar topology:** Diagonal elimination preserves parity and leaves only horizontal and vertical edges. The horizontal cut-parity identity gives finite support to the plaquette coefficients, and the even-degree identity proves the vertical coefficients by telescoping. Thus the triangle decomposition needs no unproved topological assertion. The linked-cut-edge argument uses both connectivity hypotheses and produces a finite even edge set whose cut intersection is exactly the two selected edges. Passing to outer endpoints and then to intersecting crosses proves the two connectivity claims.
- **Constants and uniformity:** The near-site series equals \(48\theta^{14}(17+\theta/(1-\theta))\), which is bounded by the stated expression. Multiplication of the removal coefficient \(2A\theta^{-3}\) by the thickening cost \(5\theta^{-1}\) gives exactly \(10A\theta^{-4}\). With \(c=-\log\theta>0\), the bound \(e^r\ge r^{10}/10!\) yields the stated \(K_\theta s^{-2}\); \(u\ge K_\theta^2\) makes this at most one. All denominators are positive, all logarithm arguments are positive, and \(M_\star\) is an integer at least \(390^4\). The constants are independent of colouring, translate, boundary, and shell. Only partition sums outside the fixed window are transferred by quadrature, so no equality of different frame-valued window laws is assumed.

**Formalization notes**

1. Preserve the original volume \(G\) as a parameter of every deleted-volume partition sum. Defining \(Z_{G\setminus Y}\) by recomputing its boundary legs would change the model and invalidate both telescoping and factorization. Its protected layer is always \(S(G)\).
2. Keep ambient \(\ell^1\) distance and ambient \(\ell^\infty\) distance separate. Corner distances, \(h\), \(t\)'s Lipschitz property, and star-boundaries use \(\ell^\infty\); response distances, removal depths, and the final thickening use \(\ell^1\). Encode the nonexceptional quantifier explicitly as in Finding 1.
3. Define the removal polynomial by cases on the surviving-neighbour count. For \(k<4\), do not form nonexistent entries \(u_4\) and then multiply their expression by a zero indicator. This implements the text's express convention that \(Q_j\) is needed only for \(k=4\). For \(k=0,1\), the polynomial is identically one.
4. Conditional laws need only be formed on positive-probability fibres. Prove their product structure directly for the entire independent neighbour set, rather than relying only on a pairwise-independence formulation. The mean bound applies because these sites have no pin factors and at most three remaining bonds.
5. Track separate polynomial degrees per site. Every endpoint of an inserted pair or quartic pairing has lost its bond to the deleted site, leaving room for its one inserted occurrence. No degree-five quadrature or moment identity is used.
6. Use finite edge sets over \(\mathbb F_2\) in the appendix. Implement sums such as \(\sum_{r>j}H(i,r)\) using finite support, and establish the vanishing total horizontal crossing parity before asserting finite support of the plaquette coefficients. No convergence theorem is required.
7. Prove the cut nonempty before choosing a root. A finite connected induced graph then supplies finite shortest-path distances; sort by distance with an arbitrary finite tie order to obtain the deletion enumeration. Empty-set distances and empty products should retain their interface conventions.
8. Treat \(s=u^{1/4}\), \(T=s/12\), and tail exponents as real quantities; \(k_i\), \(t\), \(h\), and lattice depths are integers on the relevant sites. The ceiling defining \(M_\star\) and the positive real powers require the usual coercions and monotonicity lemmas. None requires an effective numerical value for \(\theta\).

**Exact checks performed**

The removal lower bounds, the seed contribution \(4/5\), and the geometric-series algebra were checked with rational arithmetic. The counterexample in Finding 1 was also checked exactly.

A single-process C enumeration checked the cut at 12 nonexceptional configurations: \(u=390^4\), \(u=390^4+1\), and \(u=396^4\), with indices 2 and 3, exterior corner sites, central side sites, a shell side just outside the square, and positions at the nonexceptional cutoff. Fourth-power integer comparisons resolved the nonintegral-root case exactly. The checks covered connectivity of \(U\), its complement, \(X_0\), and \(X\); window-neighbour inclusion; clearance from \(F^c\); exact \(\ell^1\) depths; and near-site multiplicities. All passed. Three additional configurations were correctly classified as exceptional, including the equality-cutoff case that becomes exceptional when \(u\) increases from \(390^4\) to \(390^4+1\). These finite checks support, but do not replace, the general proofs audited above.
