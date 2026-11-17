VERDICT: SOUND WITH FIXES

Section 7's quantitative argument is sound after the two minor statement/definition fixes below. I found no Critical or Major defect in the assigned section. In particular, the terminal auxiliary network, the logarithmic-mean coefficients, the comparison with the type-dependent kernel, the transport of the positive-vector witness, and the renewal estimate support the stated conditional response theorem.

I read `main.tex` and all twelve included section/appendix files for context, and checked Section 7 against the supplied PDF (Definitions/Lemmas/Theorem 7.1–7.13). Locations below refer to the supplied LaTeX source. Results from other sections are treated as established results with their stated hypotheses; the external certificate archives mentioned in Sections 8 and Appendices C–D were neither available within the permitted inputs nor read. Consequently, this report verifies Section 7's implication from (H1), (H2), and (H3_h), rather than independently certifying those archived data.

## Numbered findings

1. **Minor — the closure lemma's statement includes neighbour pairs that its proof correctly excludes.**

   **Location/label:** `sec7-recursion.tex:79–81`, `l:closure` (Lemma 7.2); compare its proof at lines 158–164 and its use at lines 788–812.

   **Exact claim:** “Every \(\mathrm U\) departure before stopping has a covered pattern, and its nonremoved neighbour pairs belong to \(P_B\) or \(P_C\) of that ordinary domain.”

   **Why the unrestricted claim fails:** A nonremoved arrival neighbour can be a \(\mathrm D\) site with **two present bonds** after the live departure site is removed. Such an endpoint is excluded by Definition `d:pairenv`, which permits a \(\mathrm D\) endpoint only with at most one present bond.

   Here is an explicit example satisfying the other hypotheses. Let
   \[
   G=\{-4,\ldots,4\}^2,\qquad
   S=\{x\in G:\|x\|_\infty\ge3\},
   \]
   remove only \(c=(1,0)\), give all other sites status \(\mathrm U\) with full kept sets, and take the original pair \(u=(0,0)\), \(v=(2,0)\). This pair belongs to \(P_B\), with centre \(c\). The trail
   \[
   ((0,0),(0,1),(0,2),(0,3))
   \]
   avoids \(v\) and first hits \(S\) at its last site. Normalize the kept flag from \(u\) to \(c\) as prescribed. After the first step, at the \(\mathrm U\) departure \(y=(0,1)\), the arrival site \(u\) is \(\mathrm D\) and keeps its west and south bonds. Removing \(y\) leaves both bonds present. Thus \((u,(1,1))\) is an ordered pair of nonremoved neighbours of the removed \(y\), at distance two, but belongs to neither \(P_B\) nor \(P_C\), because \(u\) has two present bonds.

   **Exact repair:** Replace the quoted sentence by

   ```latex
   Every \(\mathrm U\) departure at \(y\) before stopping has a
   covered pattern. In the ordinary domain obtained by removing
   the live site \(y\) from the pre-step network, every ordered
   pair of distinct nonremoved non-arrival neighbours of \(y\)
   belongs to \(P_B\) or \(P_C\), with designated centre \(y\).
   ```

   The existing proof already proves this corrected statement. The response set \(\mathcal Q_i\) in the recursion is explicitly restricted to non-arrival neighbours, so no coefficient, estimate, or theorem conclusion changes.

2. **Minor — explicitly specify the domain of the prescribed short-trail orderings.**

   **Location/label:** `sec7-recursion.tex:579–585`, `d:kernel-order` (Definition 7.8); relevant preceding definition at lines 518–521.

   **Exact claim:** “For a closed trail of length \(n\le L\), let \(\sigma_w\) order its first visits …”.

   **Why this needs correction:** The kernel is indexed by \(w\in\mathcal T_n^X\), whose endpoints are the distinct sites \(u\) and \(v\). Such a trail is not closed in the usual graph-theoretic sense. No alternative meaning of “closed trail” has been defined. For example,
   \[
   ((-1,0),(-1,1),(0,1))\in\mathcal T_2^C
   \]
   needs a short-trail ordering but has unequal endpoints. The intended domain is clear from the kernel formula and Appendix C's enumeration; the literal wording leaves that domain underspecified for formalization.

   **Exact repair:** Replace the ordering instructions at lines 579–584 by

   ```latex
   For each \(X\in\{B,C\}\) and \(w\in\mathcal T_n^X\),
   define \(\sigma_w\) as follows. If \(n\le L\), order its
   lattice first-departure indices by increasing
   \((x_i-1)/(x_i\kappa_h(i))\), assigning value \(+\infty\)
   when \(\kappa_h(i)=0\), and break ties by increasing path index.
   If \(n>L\), list straight first departures in path order
   and then turning first departures in path order.
   ```

   Interpret the corresponding “closed trail” terminology in Appendix C as referring to these same \(u\)-to-\(v\) kernel trails. This is a terminology/domain repair; the prescribed numerical ordering is unchanged.

## Statement table

“Sound” below concerns the stated mathematical assertion or definition within Section 7's assumed input contracts. References to the two fixes are explicit where relevant.

| Label / PDF number | Content | Verdict | Dependencies |
|---|---|---|---|
| `d:pairenv` / 7.1 | Ordered distance-two response pairs with a removed centre; envelopes \(F_B,F_C\), bounds \([0,2]\), monotonicity, negative-integer extension | Sound | `d:domain`, `d:moment`, `l:finitefacts`; ambient distances and original \(S(G)\) |
| `l:closure` / 7.2 | Kept-set/status invariant under tracing; removal of the live interior endpoint gives an ordinary consistent domain; covered departures; terminal boundary defect | Minor fix: restrict pair clause as in Finding 1 | `d:domain`, `d:trace`, `d:pattern`, `l:local`, `d:pairenv` |
| `l:terminalcover` / 7.3 | Admissible second start/target; coverage away from the first terminal site; at most twelve exceptional \(\mathrm U\) departures | Sound; the one-point estimates are conditional on (H1), (H2), as the proof specifies | `l:closure`, `p:pairwalk`, `l:local`, `l:onepoint`; \(u,v\notin S\) for the two starts |
| Unlabelled Remark / 7.4, lines 246–258 | Example showing why the second start must satisfy \(v\notin S\) | Sound | `d:pinmodel`, `d:pairenv`, `d:trace` |
| `l:log-mean-bounds` / 7.5 | Monotonicity of \(G_c\), logarithm enclosures, exact rational coefficient table | Sound; all displayed rational checks independently verified | Positive logarithmic means; \(3/5\le c\le1\); finite geometric expansion and positive remainder |
| `l:response-typed` / 7.6 | Canonical positive response coefficients and their straight/turn bounds | Sound | (H1), `l:local`, `d:ratios`, `l:response`, `l:finitefacts`, `l:35`, `l:log-mean-bounds` |
| `d:kernel` / 7.7 | Nonnegative type/shift kernel; geometric liveness and trace coefficients | Sound with the orderings specified by repaired 7.8 | `d:weights`, `l:log-mean-bounds`; distinct unoriented bonds and first-hit target stopping |
| `d:kernel-order` / 7.8 | Fixed rational vector, \(\rho_0\), short and long orderings | Minor domain clarification: Finding 2 | `d:kernel`; exact \(x_{\rm s},x_{\rm t}>1\), \(h_C>1\); explicit zero-key branch |
| `h:H3` / 7.9 | Finite-cutoff positive-vector assertion, equivalent to \(M_1h\le\rho_0h\) | Sound definition/equivalence after Finding 2 | Nonnegative sums, finitely many trails at each length, fixed orderings; asserted realization in `l:stationary-assembly` |
| `l:Mtheta` / 7.10 | Shift bound \(s\le n/2+1\), summability for \(\theta>q^2\), explicit transport of the same witness | Sound | (H2), (H3_h), `d:kernel`, coefficient table bounded by \(\bar\alpha,\bar\beta\), `d:weights` |
| `l:recineq` / 7.11 | \(F_X(d)\le\sum_{Y,s}M_{XY,s}F_Y(d-s)+C_Tq^{2d}\) for every integer \(d\ge1\) | Sound using the corrected closure clause | (H1), (H2), `p:pairwalk`, `l:closure`, `l:terminalcover`, `l:exposure`, `l:response-typed`, `l:onepoint`; only the (H2)-part of `l:Mtheta` |
| `l:renewal` / 7.12 | Bounded nonnegative solutions of the shift inequality satisfy \(F_X(d)\le A\theta^d\) | Sound, including zero shifts and \(C_T=0\) | Positive \(h\), weighted row bound, \(0<\rho<1\), \(0<q^2<\theta<1\); bounded \(F\) on all integers |
| `t:rec` / 7.13 | (H1)+(H2)+(H3_h) imply \(\mathsf P(A,\theta)\), with the displayed finite \(A\ge2\) | Sound after the two minor fixes | `l:Mtheta`, `l:recineq`, `l:renewal`, `d:pairenv`, `h:P`; realization of deletion-only volumes as ordinary consistent domains |

## Proof and dependency checks

- **Closure and boundary.** For \(y\notin S(G)\), \(d(y,G^c)\ge3\); the entire radius-two template lies in \(G\), and the immediate neighbours carry no original legs. Dropping the initial flag toward the removed centre changes no present factor. A \(\mathrm U\) departure leaves exactly two kept flags; a later live \(\mathrm D\) site has one kept flag and its departure removes no other present bond. These facts prove the induction and ordinary-domain membership after removing an interior live endpoint. The removed centre automatically lies outside \(S\), since protected sites cannot have status \(\mathrm X\).

- **Terminal cover and expansion hypotheses.** In the first expansion, the start and target meet `p:pairwalk`: an interior \(\mathrm U\) endpoint has no leg and at most three present bonds; a \(\mathrm D\) endpoint has at most one. On an \(S\)-ending branch the unvisited second start retains its status/kept set and cannot gain present bonds. The first terminal site \(e\) remains \(\mathrm U\), with at most three factors counting its unchanged original legs; it is therefore a valid target for the second expansion. Its only fixed defect is within distance two of at most twelve possible departure sites. Each can have at most one \(\mathrm U\) departure during the second trace. No estimate requires removing \(e\) or treating the terminal auxiliary network as ordinary.

- **Logarithmic means and response coefficients.** The reciprocal-mean integral, including equal arguments, is correct. The two displayed derivative signs follow from \(c\le1\) and \(5c\ge3\). In the removed-site network, the three response neighbours are pairwise nonadjacent, unpinned, and have at most three factors each. Thus `l:finitefacts` and `l:35` apply on positive conditioning fibres. They give precisely \(I^\bullet\in[41/50,34/25]\), \(J^\bullet\in[116/125,134/125]\), and \(J^\tau\ge a\). Each free pair insertion has separate degree at most four, so \(I^0\ge J^0\ge1\). The canonical coefficient has lower bound \(25/102-25/116=175/5916>0\). Using the monotonicity of \(G_c\) to bound the difference defining \(\alpha_j\) is valid.

- **Kernel comparison.** The fixed lattice symmetry exists for both ordered pair types and preserves distances and local passage types. A true \(\mathrm U\) departure is a first lattice departure; every lattice revisit is a \(\mathrm D\) departure. Therefore \(a_D(w)\le3^{-n}(3/5)^{\operatorname{rev}(w)}\). A kernel-dead site is actually removed, so actual response pairs are a subset of kernel-live pairs. If the kernel has forgotten an actual removal, the surviving outgoing-pair coefficient changes from \(b'_\tau\) to the larger \(b_\tau\), and added terms are nonnegative. Restricting the fixed full ordering to actual \(\mathrm U\) departures makes inserted prefix factors harmless because every \(x_i\ge1\).

- **Shifts and summability.** The distance inequality at lines 803–812 has the correct direction and uses \(s(p)=\max_{z\in p}\min\{d(z,u),d(z,v)\}\). Negative arguments use the prescribed constant extension. For a length-\(n\) trail, a response neighbour is at distance at most \(n/2+1\) from the nearer endpoint. Summing all response coefficients at one first departure gives at most \(C=\bar\alpha+2\bar\beta\); the bound is on their total across both pair types, so the witness-transport estimate does not lose an extra factor of two. The geometric series converges for every \(q^2<\theta\le1\). The explicit \(\varepsilon\) is strictly positive, \(q^2<\theta<1\), and \(\sum_{n\ge1}n(n+1)r^n=2r/(1-r)^3\) gives exactly the stated \(B_*\).

- **Two-boundary contribution.** The second expansion uses stopping set \(S=S\cup\{e\}\), exactly as `p:pairwalk` requires. `l:onepoint` applies with the absent initial bond and the twelve-exception allowance. For the first expansion's boundary branches, enlarging to all first-hit trails to \(S\) is legitimate because closure did not assume avoidance of \(v\). The maximum over pin choices is taken before summation, as required by the pointwise majorant. Consequently
  \[
  |T_2|\le2K_*^2q^{d(u,S)+d(v,S)}\le C_Tq^{2d},\qquad
  C_T=2(12/5)^{24}\bigl(C_V/(1-q)\bigr)^2.
  \]
  The separate-degree bound is also valid in the second expansion, including the inserted coordinate at the already defective target \(e\).

- **Renewal and final response property.** The all-integer source \(g\) is bounded and gives \(F\le KF+g\), including at \(d\le0\). The unshifted row inequality sends the bounded remainder to zero as \(\rho^k\); the shifted row inequality controls the source by \(h_X\theta^d\). This handles \(s=0\), arbitrarily large shifts, and arbitrarily negative intermediate arguments without an induction-on-distance assumption. The stated \(A=H\max\{2,C_T\}/(1-\rho)\) is correct. The final deletion-only domain belongs to \(\mathcal D_{\rm cons}(G)\), has exactly the original partition sums, and supplies the required removed centre. Cases with distance zero use \(F_X(0)\le2\le A\). With no eligible pair the assertion is vacuous; otherwise finiteness and nonemptiness of \(G\) ensure \(S(G)\ne\varnothing\), so the final distance is a finite nonnegative integer.

## Exact computations performed

All computations used one Python process at a time, with `fractions.Fraction` for rational quantities. No input was modified.

1. Reconstructed all five logarithm-enclosure rows from the eight-term sums and the displayed integer formulas for \(P,Q\). Verified both integer inequalities in each row, all six coefficient bounds, \(0<b'_\tau\le b_\tau\), the coarse coefficient bounds, and every residual numerator in the table: straight \((13215,1425,1692)\), turning \((259510,2684,2235)\). All passed.
2. Implemented the trace flags in the counterexample in Finding 1. Checked ordinary-domain consistency after removing \(y\), and the two remaining present bonds at the \(\mathrm D\) arrival site.
3. Independently enumerated the canonical kernel trails through length twelve, computed their exact short-ordering contributions, and checked the outgoing-neighbour liveness condition during enumeration. The five node/prefix/short-hit triples agree exactly with Appendix C:

   | Case | Nodes | Surviving length-12 prefixes | Short first hits |
   |---|---:|---:|---:|
   | B/N | 139985 | 89150 | 937 |
   | B/W | 161929 | 103257 | 922 |
   | C/N | 105025 | 66947 | 715 |
   | C/W | 155673 | 99168 | 1036 |
   | C/S | 145485 | 92748 | 861 |

   The B/S short sum, prefix count, and hit count also equal B/N. This check does not evaluate the archived stationary potentials or their long-trail bounds.
4. Checked the Section 8/Appendix C endpoint arithmetic against the exact Section 7 vector and coefficients:
   \[
   \frac{2\cdot351207554+290599163}{10^9}<\rho_0h_B,
   \qquad
   \frac{527872005+380754375+273048088}{10^9}<\rho_0h_C.
   \]
   In particular the stated certificate contracts use \(a_{\rm t}=150000/10^6\), the same dyadic \(h_C\), \(L=12\), and the same prescribed orderings.
5. Evaluated the explicit shifted-witness construction over the rationals with the stated \(q,C_V=10\). All positivity, strictness, and residual inequalities passed. For scale only, \(1-\theta\approx1.65494\times10^{-15}\), \(\rho=0.9965075\), and the displayed bound gives \(A\approx4.80531\times10^{20}\). These decimal illustrations were not used in any check.

## Formalization notes

1. Represent kept flags separately from present bonds. In particular, normalization at the removed centre preserves the partition polynomial but temporarily takes the start outside the ordinary consistent subclass. Do not coerce that live network to \(\mathcal D_{\rm cons}(G)\). Prove membership only after removing the live interior endpoint.
2. Encode response pairs with their designated removed centre and distinct endpoints. Kernel pairs are unordered whereas \(P_B,P_C\) are ordered; choosing either endpoint order preserves the observable, type, and shift. Restrict their construction to non-arrival neighbours as in Finding 1.
3. Keep the original finite \(G\), original legs, and original \(S(G)\) as fixed parameters through both traces. A terminal protected site with a lost arrival bond belongs to the auxiliary-network type. The second trace has one fixed defect there; it is not an ordinary-domain trace globally.
4. State the exact admissible start, target, and stopping-set conditions in both calls to `p:pairwalk`. In particular, quantify \(u,v\notin S\) in the two-start application, and retain the bound of three total factors, including original legs, at target \(e\). All fibres used for conditional independence must have positive probability.
5. Define the logarithmic mean with its equality branch before using a divided difference. Prove positivity of its arguments and of its value before division. Use the canonical coefficient formulas even if a response vanishes; existence of some coefficients in a linear identity does not itself identify their numerical bounds.
6. Use nonnegative extended sums initially, or delay the real-valued kernel until summability has been proved. The summability portion of `l:Mtheta` uses only (H2), and must be available independently of its witness-transport portion; `l:recineq` assumes no (H3_h). Preserve the fixed ordering when proving the comparison with the trace.
7. At a noninitial twice-departed site, two arrival/departure pairs have already used all four incident bonds. At the start, two departures have used all three bonds available after excluding \(c\). These direct counts are a convenient formal proof of the outgoing-neighbour assertion at lines 560–568.
8. Distances and shifts are integers when an eligible site/pair exists. Establish nonemptiness of \(S(G)\) from finite nonempty \(G\) before converting a distance to an integer. For the bound involving \(n/2\), use either real coercions explicitly or the stronger integral form \(s\le\lfloor n/2\rfloor+1\).
9. Use integer powers for \(\theta^d\) on \(\mathbb Z\). Keep the unweighted bounded remainder and the weighted source estimate distinct in the renewal proof: \(h_X\theta^d\) is unbounded as \(d\to-\infty\), but its shifted sums at each fixed \(d\) are finite by hypothesis. A zero-shift term prevents a naive strict induction on distance; the stated operator iteration handles it.
10. The theorem is conditional on the precise mathematical inputs. Any separate Lean proof of (H1), (H2), or (H3_h) must establish those definitions with the same constants and orderings. Finite short-trail checks alone do not replace (H3_h)'s uniform bound over all cutoffs.

## ORCH-SUMMARY

- Assigned scope: Section 7; whole LaTeX paper read for context.
- Verdict: SOUND WITH FIXES; no Critical or Major finding in this section.
- Minor 1: `sec7-recursion.tex:79–81`, `l:closure`, overclaims closure for all nonremoved neighbour pairs.
- Explicit counterexample: the arrival neighbour remains D with two present bonds.
- Repair: restrict to distinct nonremoved non-arrival neighbours, exactly as the proof and recursion already do.
- Minor 2: `sec7-recursion.tex:579`, `d:kernel-order`, should quantify over kernel trails, whose endpoints are distinct.
- Repair: explicitly define the orderings for every `w in T_n^X`; numerical rules unchanged.
- Terminal coverage, target degrees, twelve exceptions, and original-boundary distances checked.
- Logarithm enclosures, coefficient constants, and all displayed residual numerators passed exact arithmetic.
- Independent length-12 kernel enumeration matches all five Appendix C count triples; B reflection also checked.
- Shifted witness and renewal constants checked, including zero shifts and negative arguments.
- Conditional conclusion `(H1)+(H2)+(H3_h) => P(A,theta)` is sound after these minor fixes.
- External certificate archives were not read or independently certified; their mathematical contracts match Section 7.
