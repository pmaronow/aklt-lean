STATUS: COMPLETE

This is a ranked opportunity assessment, with mathematical proofs or proof sketches, not a Lean implementation. I used the frozen manuscript, all seven referee reports, the ADJ-R4/R5/R6 and ADJ-MINOR adjudications, MOSPROOF and its referee report, and PROBE1. The proposed changes below presuppose the adjudicated repairs, especially the protected boundary/terminal-network distinction and the corrected definition of the 7,962 patterns. I have not modified the manuscript. I have not worked on the separately assigned extension to all tori or finite-volume ground-state uniqueness.

The most useful package is **1–10**: a direct periodic block proof, finite moment algebra, a thickened cut, simpler tracing and spin-sector arguments, and explicit formulas for the existence constants. The main numerical obstacle remains (H3′). The orchestrator transferred its certificate search, and that for (H2), to another agent during this task. The short final entry records only runs started before that instruction; no subsequent certificate or parameter scans were launched, and the last existing run had already exited when the stop check was made.

**1. Apply the stopped coupling directly to periodic block updates; remove Section 3 and most of the box-gap apparatus from the main dependency chain.**

**Statement: true.** In the existing even-torus setting, one fixed cell partition and one square scale suffice. This is a further simplification of [MOSPROOF](../MOSPROOF/proof.tex), not an application of the old unstopped surgery bound alone. It removes both imported mixing theorems, compatible sets and common multiples, the second cell offset, the Knabe criterion, and the clamped variable-size squares. The rectangular-box theorem in MOSPROOF can remain an optional stronger classical result.

Here is the complete finite-dimensional reduction. Let the cell specification have finite-energy constant `alpha`, and suppose, at a square radius `M`, every pair of square laws differing at one exterior cell has a coupling with expected Hamming distance at most `K=M/1000`. MOSPROOF Lemma 7.2 supplies precisely this estimate, with `M=n^8`, from the existing window estimate and its explicit conditions on `n`.

On a cell torus with both periods at least `2M+3`, update all translates of the square of side `2M+1`, each at rate one. For configurations differing at one cell `x`, exactly

`T=(2M+1)^2`

blocks contain `x`; couple their resampling identically, removing the disagreement. At most

`S=(2M+3)^2-(2M+1)^2=8M+8`

blocks exclude `x` but can see it in their boundary. Each adds expected Hamming distance at most `K`. Other blocks add none. Thus the unnormalized block generator has gap at least `T-SK`, by the finite Lipschitz/eigenfunction argument of MOSPROOF Lemma 5.1. Since `SK/T <= 1/500`, this is at least `499T/500`. This argument counts translated blocks; it needs no invariant eigenvector.

Every conditional block law has single-cell heat-bath gap at least

`g=alpha^(T+1)/T`,

by MOSPROOF's elementary finite-volume path bound. Summing its fiber Poincaré inequalities over placements counts every cell exactly `T` times. Consequently

`gap_cell(torus) >= (499/500) alpha^(T+1)/T`.

The manuscript's four-site comparison and quantum comparison now give

`gap(H) >= (499/1000) g_star c_0 alpha^(T+1)/T`

for even physical periods at least `4M+6`. Plane-square conditional laws lift to these tori exactly as in `l:boxcell`; the two spare cell columns/rows avoid boundary identifications. Fix the offset-zero partition globally. No offset-one box is needed.

**Cost/value/recommendation: DO; highest value.** Paper: replace several reductions by this argument and the stopped-shell lemma. Lean: retain finite coupling, finite self-adjoint matrices, fiber variances and elementary placement counts; omit periodic autocorrelation, quadratic weights and clamping. This also gives a much smaller explicit size threshold than choosing a box side of order `1/(c_0 m_0)`. It does not affect the trail inputs or their certificates. The only fix needed in the standalone MOSPROOF criterion is the positive `alpha` hypothesis identified by [REF-MOS](../REF-MOS/report.md).

**2. Replace the continuous sphere measure throughout the core proof by a finite positive fourth-moment functional.**

**Statement: true, with a small qualification to the proposed “degree at most four” slogan.** Use an exact positive spherical 4-design for each U spin and `3/5` of that law plus `2/5 delta_0` for each D spin. The necessary moments are only

`M(1)=1`, `M(n_i)=M(n_i n_j n_k)=0`, `M(n_i n_j)=delta_ij/3`,

and `M(n_i n_j n_k n_l)=(delta_ij delta_kl+delta_ik delta_jl+delta_il delta_jk)/15`.

All partition functions, conditionings, the three-field mean bound, local operators and the needed inserted pair/four-point observables use these moments. In particular, at an inserted pair endpoint the removed center leaves at most three incident factors, so adding the observable still gives degree at most four. The four-point term in a cut seed has distinct endpoints with the same property. Free positivity need only be stated for these admissible insertions: expanding them gives positive contractions of Kronecker deltas. The all-orders Gaussian moment formula is unnecessary.

The printed first step identity allows `k=4`, which produces degree five after inserting `a.n`. Either use the existing 5-designs, or restrict that identity to `k<=3`, its entire used range. A U departure starts with at most three present bonds; a subsequent arrival has already deleted its incoming bond. Also, an arbitrary product of many inserted scalar products need not have degree at most four. Delete that unused generality instead of claiming exactness for every observable.

The finite functional has the required rotation covariance on the bounded-degree polynomial space even though the finite set itself is not invariant under all rotations. Prove polynomial covariance from the displayed moment tensors; do not assert covariance of its law for arbitrary functions. Define the spin-2 inner product directly in the monomial basis, with squared norms `1/binom(4,k)`, and prove the finite frame identity algebraically. The exact icosahedron/dodecahedron moments and their placement are already established in [ADJ-MINOR](../ADJ-MINOR/report.md).

For the Pauli inversion argument, use the density matrix `rho(a)=(I+a.sigma)/2` and `F(u)=Tr[O(F^I) tensor_i rho((u^I)_i)]`. Positivity of the operator and product density matrix proves nonnegativity. This avoids selecting spinor phases on the whole sphere. Only the finitely many frame evaluations need actual spinors.

For arbitrary real pin vectors, positivity of a partition sum also has a finite proof: a U site has twelve design letters and at most four factors, each of which can forbid at most one letter. Choose letters successively avoiding the incident zeros. This replaces the open-neighborhood argument for sphere integrals.

**Cost/value/recommendation: DO.** Paper: modest notation changes, or a finite-moment formulation followed by a remark identifying the continuous model. Lean: remove surface measure, Gaussian integration, product-measure Fubini and almost-everywhere conditional expectations. Unit spheres and elementary real inequalities remain; (H1) still quantifies over arbitrary unit pins. General continuous Gibbs measures, if desired as a corollary, can be introduced after the core theorem.

**3. Thicken the cut by one nearest-neighbor layer and delete the no-diagonal-only-block argument.**

**Statement: true.** Write `X=partial_infty U'` as in Section 5 and replace it by

`Xplus={z : dist_1(z,X)<=1}`.

Only star-connectivity of `X` is needed. Steps 1–2 of [the topology appendix](../../manuscript/bundle/manuscript/app-lattice-topology.tex) already prove it from star-connectivity of `U'` and its complement: linked cut edges have outer endpoints in the same triangle, hence equal or star-adjacent. The third hypothesis and the final nearest-neighbor bridging argument can be dropped. The much longer check that no block meets `U` in two opposite cells, and its lift to sites, then disappears from `l:Xconn`.

The union of nearest-neighbor crosses around a star-connected set is nearest-neighbor connected: crosses around diagonally adjacent centers share bridging sites. The displayed estimates in `l:cutgeom` actually give `b(x)>=5` at `l_0=20`, once `s` is large; therefore every point of `Xplus` has `b>=4`. In particular the enlarged cut lies in `G`, avoids the window and all original pins, and satisfies the removal lemma's `b>=3` condition. It still separates the same regions; replace `G_1,G_2` by their differences with `Xplus`.

Since distance to `G^c` is 1-Lipschitz,

`sum_(z in Xplus) theta^b(z) <= 5 theta^(-1) sum_(x in X) theta^b(x)`.

The cut cost remains uniformly finite. One seed still suffices.

**Cost/value/recommendation: DO.** Paper: a factor `5/theta` in an existence-only cost. Lean: removes the most intricate local case analysis in Section 5 and weakens the topology lemma. It retains the appendix's parity/cycle argument; this proposal does not pretend all planar topology has vanished.

**4. Move the revisit mass into the walk coefficient; make traced domains carry only statuses and kept bonds.**

**Statement: true and numerically equivalent to the existing expansion.** Give a U departure coefficient `1/3` and a D departure coefficient `1/5`. At a U departure use the normalized D law as now; at a D departure delete the site, without putting a scalar mass on the traced object. Its conditional partition factor with at most one remaining bond is exactly one. The D departure then has ratio one and zero response.

The path coefficient is

`(1/3)^(number of U departures) (1/5)^(number of D departures)`.

This equals the manuscript's `3^(-length) (3/5)^(number of D departures)`. Thus the eventual lattice kernel and trail weights are unchanged, including initially D sites that the dominating lattice kernel treats as first visits. Products of first-visit partition ratios telescope exactly as before. Prove the expansion first for unnormalized numerators and divide by the initial partition function once.

Restrict its input to U starts with at most three bonds, or D starts with at most one. These are exactly the starts used in the pair recursion and both boundary-hitting estimates. An initial two-bond D departure has a pin-dependent normalization; it can be deleted from the used lemma instead of supporting the more general bound. This addresses, rather than bypasses, the distinction in [ADJ-R4](../ADJ-R4/report.md).

**Cost/value/recommendation: DO.** Several formulas change, but one elementary identity identifies the numerical kernel with the old one. Lean avoids a scalar-mass field and its propagation/cancellation through every trace. Auxiliary terminal networks are still necessary: arrival at `S` deletes a protected boundary bond, even with this convention.

**5. Detect all operator eigenvalues in the central weight sector by ladder identities, without decomposing arbitrary SU(2) representations.**

**Statement: true.** For `l:sector`, use the concrete operators `S_z,S_+,S_-`, their adjoints and `[S_+,S_-]=2S_z`. On weight `m>0`,

`||S_-v||^2=||S_+v||^2+2m||v||^2`,

so lowering is injective; on `m<0`, raising is injective. If an eigenspace of the Hermitian operator `O` has eigenvalue `lambda`, commutation makes it stable under the ladder operators. Choose a nonzero weight vector in it, then raise or lower, without vanishing, until weight zero, or weight `1/2` in the odd-parity case. Its eigenvalue remains `lambda`. All weights have the required integer/half-integer parity by the explicit tensor basis.

This proves exactly the eigenvalue-detection statement used by the central-sector positivity test. Exchange sectors are stable under the same ladder operators, so the proof applies to each existing sector.

**Cost/value/recommendation: DO if representation-theory infrastructure is not already available.** Paper: about one paragraph. Lean: finite matrices, adjoints, commutators and a finite ladder induction replace the general theorem that every unitary SU(2) representation decomposes into spins. Proving commutation with the three concrete generators is sufficient. No certificate or target constant changes.

**6. Prove the quantum edge lemma using the Cartan multiplication map instead of the full Clebsch–Gordan rule.**

**Statement: true.** Let `Delta: V_4 tensor V_4 -> V_8` be `p(z_x,z_y) -> p(z,z)`. It is equivariant and surjective on monomials. Its kernel has dimension `25-9=16`. Multiplication by `q_xy` injects the 16-dimensional space of bidegree `(3,3)` into this kernel, so these spaces coincide. The adjoint image is the total-spin-4 space: it is a copy of `V_8`, and the top-weight space of weight four is one-dimensional, which also proves that another spin-4 copy cannot occur.

**Cost/value/recommendation: DO if it shortens the chosen Lean foundation.** This proves `ker P_e=q_e V_(3,3)` without decomposing the tensor product into spins zero through four. Paper cost is small; Lean uses dimensions, polynomial multiplication and the explicit spin-4 representation. Keep the existing proof if a usable Clebsch–Gordan theorem has already been formalized. This is an edge-lemma simplification, not work on the separately assigned finite-volume uniqueness extension.

**7. Replace existence/minimization definitions of the four-site comparison constant by `c_0 >= 9^(-4)`.**

**Statement: true.** Put `a=1-gamma_+`, `b=1+gamma_+`, and `r=a/b`. The exact frame placement gives `gamma_+<4/5`, hence `r>1/9`. In one cell, absorb all exterior bond factors and site weights into a product reference law `pi`. Only the four internal bond factors remain as a density perturbation. Thus, for `rho=dmu/dpi`,

`max rho/min rho <= (b/a)^4`.

For any positive density between `m` and `M`, the variational definition of conditional variance gives `D_mu(f)>=m D_pi(f)` and `Var_mu(f)<=M Var_pi(f)`. The product heat bath has gap one. Therefore `gap(mu)>=m/M>=r^4>9^(-4)`, uniformly in the exterior letters. This also works for arbitrary positive product boundary fields.

For later use, the cell finite-energy constant can simultaneously be fixed at

`alpha=1/(57600 * 9^12)`:

there are four internal and eight crossing factors, and the site weights are constant over the 57,600 cell letters.

**Cost/value/recommendation: DO.** A short variance-comparison lemma replaces a minimum over many finite chains and the much weaker `beta^5/4` bound in MOSPROOF. Both constants are rational. There is no cell-matrix computation to replay in Lean.

**8. Supply explicit formulas for `c` and `L_0`; do not promise a useful numerical gap.**

**Statement: true with the elementary quantitative replacements below.** The frozen paper does not currently have an explicit chain. Its gaps include `g_star,c_0`, the continuity choice of `theta`, the response prefactor, the eventual geometry/cut threshold, and the imported mixing thresholds. MOSPROOF fixes the last part only. Entries 1 and 7 remove several of these issues.

A reproducible formula package is as follows. Take any certified positive rational vector `h` and rational `rho_0<1` with `M_1 h<=rho_0 h`; the archived row bounds allow the deliberately slack target `rho_0=99/100`. The harmless conversion from the stored dyadic `h_C` to rational `123/100` can be bounded by a relative error much smaller than the available slack. Let `H=max h/min h`, and take certified rational `q<1,C_V`. Define

`b=(1+q)/2`, `r=q/b`, `K_0=H C_V (alpha_bar+2 beta_bar)`,

`B=2 K_0 b^(-2) r/(1-r)^3`,

`epsilon=min((1-b)/2, (1-rho_0)/(2B))`, `theta=1-epsilon`, `rho_1=(1+rho_0)/2`.

The shift bound `s<=n/2+1<=n+1`, followed by the geometric-series identity `sum n(n+1)r^n=2r/(1-r)^3`, proves

`(M_theta h)_X/h_X <= rho_0+B(1-theta)<=rho_1<1`.

Thus no spectral-radius continuity or eigenvector selection is needed. With the manuscript's safe `C_T=2(12/5)^24(C_V/(1-q))^2`, entry 9's renewal argument permits

`A=H max(2,C_T)/(1-rho_1)`.

Here and below all exponents can remain symbolic; Lean should prove positivity and inequalities, not expand gigantic denominators.

For completeness, even the star gap can be bounded explicitly without diagonalization. In the unnormalized monomial basis the pair Casimir `C` is an integer matrix and

`P_4=C(C-2)(C-6)(C-12)/40320`.

Hence `40320 h_star` is an integer matrix of dimension `5^5=3125`, similar to a positive self-adjoint matrix, with eigenvalues at most `4*40320=161280`. The product of its nonzero eigenvalues is a nonzero integer coefficient of its characteristic polynomial, hence at least one. It follows that

`g_star >= 161280^(-3125)`.

This is intentionally crude; the numerical `0.047238` is not being promoted to a certified lower bound.

One can make the remaining cut threshold explicit as well. Fix `l_0=20`. Choose an integer `R>=1000` such that

`R^2 >= 36 theta^(-7) 10! 24^10/(1-theta)^10`.

For example, take `R=1000+ceil(the right-hand side)`. The geometry inequalities in Sections 4–5 hold for `s>=R`. For `M=s^4`, the far-cut term is at most `36 theta^(-7) s^8 theta^(s/6) <=1`: use `n=floor(s/6)`, the binomial bound `theta^n <=10!/((1-theta)^10(n-9)^10)`, and `n-9>=s/24`. This is a uniform bound for every larger real `s`, not just a successful test at one scale. Put

`C_near=192 theta^5 (6+1/(1-theta^2))`,

`E=1+4A+10 A theta^(-4)(C_near+1)`.

This uses the thickened cut of entry 3 and the coarse removal constants in entry 10. The window overlap permits `p_0=3^(-2 ceil(E))`. Set `M_star=R^4`, `d=min(1/2,p_0 alpha^320)`, and choose `n` satisfying MOSPROOF's explicit conditions

`n>=44`, `n^8>=M_star`, `n^2>=max(50000,126)`,

`n^12 d^20 >= 50000 * 2^20 * 20!`.

An explicit integer choice, avoiding roots, is `D=ceil(1/d)` and `n=(50000*2^20*20!) D^20+M_star+50170`. Indeed `Dd>=1`, and this larger choice meets all four conditions. Finally set `M=n^8`, `T=(2M+1)^2`. Entries 1 and 7 give the concrete strengthened theorem with

`L_0=4M+6`,

`c=(499/1000) 161280^(-3125) 9^(-4) alpha^(T+1)/T`.

**Cost/value/recommendation: DO as explicit formulas, ASK THE AUTHOR before pursuing a useful decimal bound.** Paper: an explicit-constants appendix of roughly this length. Lean: elementary geometric/binomial bounds and one general integer-characteristic-polynomial lemma; alternatively leave `g_star` as an explicitly specified finite eigenvalue and certify a practical lower bound separately. The formulas are far too small/large to have numerical physical value. Their value is removing nonconstructive choices and documenting every dependency. The outstanding certificate owner must still supply accepted kernel proofs of its numerical premises.

**9. Use positive-vector contraction as the analytic input; simplify the final pair recursion to a renewal lemma.**

**Statement: true.** The proof needs `M_theta h<=rho h` for some positive `h`, `rho<1`, and `q^2<theta<1`. It never needs a numerical spectral radius, the full matrix spectrum, or Perron–Frobenius theory. Entry 8 obtains such a weighted witness from the current `M_1` witness and (H2), without changing any certificate search.

There is also a direct alternative to the truncated suprema `Phi_N`. Extend `F(d)` constantly to negative integers, and define `g(d)=2` for `d<=0`, `g(d)=C_T q^(2d)` otherwise. Then `F<=K F+g` on all integers, where `K` is the nonnegative shift kernel. Since `F<=2`, iteration gives

`F <= K^k F + sum_(j<k) K^j g`.

The remainder is bounded by `(2/min h) rho^k h`, using `M_1<=M_theta`; and `g_X(d)<=max(2,C_T) h_X theta^d/min h`. The sum is therefore bounded by a geometric series in `rho`. Letting `k` grow proves the displayed `A theta^d` bound in entry 8. All sums are nonnegative and the weighted kernel sum is finite.

**Cost/value/recommendation: DO for the witness interface; choose the renewal proof if it is shorter in Lean.** This removes spectral-radius continuity and the Neumann-series construction of a second vector. The renewal proof trades the `Phi_N` supremum for finite iteration plus nonnegative series; both are sound, and neither needs a fixed-point theorem.

**10. Use a common minorization for the cut laws; simplify existence-only removal constants.**

**Statement: true.** `l:cut` already proves `p_eta(s)>=exp(-2E) nu(s)` for one common probability law `nu`. Therefore

`TV(p_eta,p_xi)=1-sum_s min(p_eta(s),p_xi(s)) <=1-exp(-2E)`.

One may take `p_0=exp(-2E)`, instead of `1-tanh(2E)`. This is both shorter and substantially better for large `E`. The optimal estimate from the oscillation of the unnormalized tilts is `TV<=tanh(E)`; it follows by optimizing the usual likelihood-ratio bound. The elementary common minorization is sufficient and avoids formalizing that optimization or hyperbolic functions.

The removal estimate can also be replaced by

`cut_cost <= 1+4 F(b(first)-3)+2 sum_(later sites) F(b(x)-3)`.

Indeed a nonseed has at most three neighbors, its integrated factor is at least `0.82>=1/2`, and its pair-response numerator is at most `F`. At the seed, conditional means bound the quadratic part below by `-0.24`, while the raw four-point bracket is at least `-3`; hence the factor is at least `1-0.24-3/15>1/2`. The six pair responses contribute at most `2F`, and the difference of the two brackets at most `6/15`; division by `1/2` gives `4F+0.8<=4F+1`. No sharp four-point estimate is needed.

**Cost/value/recommendation: DO for Lean; optionally retain the tighter constants in the paper.** Only finiteness is consumed by the window estimate. This deletes several decimal verifications and the longer TV argument. If a usable quantitative gap becomes an objective, retain the sharper removal estimate while still using the better overlap bound.

**11. Add volume-uniform exponential clustering for the VBS state and for its classical outcome measures.**

**Statement: true for the torus volumes covered by the gap theorem.** For local observables supported on disjoint `X,Y`, there are `mu>0` and constants `C_(|X|,|Y|)` independent of the torus volume such that

`|omega_B(A B)-omega_B(A) omega_B(B)| <= C_(|X|,|Y|) ||A|| ||B|| exp(-mu dist_torus(X,Y))`.

The norm-one, nearest-neighbor AKLT terms have uniformly bounded interaction strength and degree. The uniform gap and nondegenerate finite-volume ground state therefore meet the exponential-clustering theorem. Connected torus distance, including wraparound, is the right metric. Bounds persist in any local thermodynamic limit. This is an application of [Nachtergaele–Sims, Theorem 2 and Section 4](https://arxiv.org/pdf/math-ph/0506030), whose constants depend on the gap and local interaction bounds, not the number of sites.

The classical statement follows particularly cheaply. The frame law is exactly the outcome law of the product coherent-state POVM on `B`. A bounded function `f` supported on `X` quantizes to

`A_f=sum_(s_X) f(s_X) tensor_(x in X)[5 w_x(s_x) |s_x><s_x|]`,

with `||A_f||<=||f||_infty`; disjoint functions satisfy `A_(fg)=A_f A_g`. The same construction with the coherent-state integral proves the identical covariance bound for arbitrary bounded local functions in the continuous classical torus measure. Apply the staggered sign change to get the manuscript's ferromagnetic convention. This is a POVM argument; it does not incorrectly transfer arbitrary inserted observables by fourth-order quadrature.

**Cost/value/recommendation: DO in the paper; ASK THE AUTHOR about inclusion in the first Lean milestone.** Paper: a concise corollary plus the POVM observation. Lean: a substantial Lieb–Robinson/clustering development if no existing theorem is available; the final POVM transfer itself is short. This gives exponential decay of full connected correlations, much stronger than simply renaming (P), which concerns responses of a restricted pair observable near a removed center.

**12. Add uniqueness of the infinite-volume finite-frame Gibbs measure.**

**Statement: true directly from the existing window coupling, without invoking the full strong-mixing theorems.** In a centered square of radius `M`, a fixed local target lies farther than `sqrt(M)` from every exterior boundary cell for large `M`. Telescope changes over the `8M+8` boundary cells and use the corrected surgery estimate. The target marginal diameter is at most

`(8M+8)(1-delta)^(M^(1/4)-4) ->0`,

uniformly over boundary letters. Gibbs measures exist by compactness of the finite-alphabet product space. By the DLR equations, the marginal of any such measure is a mixture of these finite-volume conditional marginals; their diameter tends to zero, proving uniqueness. This also proves boundary-independent local convergence and tail triviality. It does not claim exponential boundary mixing from the stopped estimate: the displayed rate is stretched exponential.

**Cost/value/recommendation: DO.** Paper: less than a page, no new numerical inputs. Lean: infinite products, construction of a Gibbs measure and DLR/disintegration, or first formalize just the finite-volume marginal-diameter theorem. This argument survives entry 1's removal of the full MOS/MO statements.

**13. The continuous classical Gibbs measure is also unique, but its identification needs an extra finite-dimensional argument.**

**Statement: true; not an immediate consequence of 12 for the original 12/20-letter alphabets.** Those alphabets do not determine every degree-four spherical polynomial: that polynomial space has dimension 25. Equality of their grid marginals alone cannot identify a continuous marginal density.

Here is a way to close the gap with the same machinery. Choose two finite positive 4-designs whose evaluations are injective on degree-at-most-four spherical polynomials and whose opposite sublattices have no antipodal coincidences. Such designs exist: union finitely many rotated icosahedra, adding a rotation whenever the evaluation kernel is nonzero; each step lowers its dimension. Generic perturbations preserve full evaluation rank and avoid the finitely many forbidden cross coincidences. The proof of (P), and hence the cut/window estimate, applies to any such designs, with no change to the trail inputs. Their fixed positive bond minima provide finite energy.

For any finite target `A`, a continuous finite-volume marginal density is polynomial of degree at most four in each target variable. Exact quadrature expresses its values on the product design grid as discrete marginal probabilities divided by the product design weights. Conditioning on an outer cell layer handles arbitrary continuous exterior pins: after summing that layer by quadrature, the law further inside is a mixture of finite-frame boundary laws, even if some outer letters have zero weight. Entry 12 gives a common limit for their target marginals. Injectivity of evaluation identifies the entire polynomial density. On this finite-dimensional space, coefficient/norm convergence follows from convergence on the fixed grid.

Compactness and continuity of the finite-volume kernels give existence of a continuous DLR measure; the same density argument proves its uniqueness, including arbitrary Gibbs boundary states. The classical thermodynamic limit in entry 11 is consequently this measure.

**Cost/value/recommendation: ASK THE AUTHOR.** Paper: approximately one additional lemma and a careful paragraph on conditioning. Lean: polynomial interpolation, positive design construction, compact probability measures and DLR. No new numerical certificate is needed. Do not replace this argument by a claim that the original designs are informationally complete, or that arbitrary observables transfer by quadrature.

**14. Add the GNS gap for every periodic thermodynamic-limit VBS state.**

**Statement: true without first proving uniqueness among all infinite-volume states.** Let `omega` be any local weak limit of the normalized torus VBS states with both periods tending to infinity. For every local operator `A`, finite-volume gap and frustration-freeness give

`omega(A* [H,A]) >= c (omega(A*A)-|omega(A)|^2)`.

Only the finitely many bonds meeting the support of `A` appear in the commutator, so this inequality passes directly to the limit. Also `omega(P_e)=0` for each edge. The inequality is the GNS spectral-gap form with a one-dimensional zero eigenspace; after constructing the local dynamics and its positive implementer, it yields `spec(H_GNS) subset {0} union [c,infinity)` and `ker H_GNS=C Omega`.

**Cost/value/recommendation: DO the local form inequality in the paper; ASK THE AUTHOR about a fully formal GNS theorem now.** The new mathematical argument is short. Lean needs compatible local algebras, states, GNS, unbounded generators and a form-core argument for the operator-language conclusion. The displayed local inequality is already a meaningful precise infinite-volume conclusion with a much smaller formalization cost. A simple GNS vacuum is not a proof that every algebraic ground state is the same state.

**15. Uniqueness of the infinite-volume frustration-free quantum state can be proved with an informationally complete frame extension.**

**Statement: true with the following additional argument; it does not follow from periodic finite-volume uniqueness alone.** On a finite open region, the edge lemma gives every frustration-free vector as `B_internal chi_boundary`, where the residual polynomial depends only on boundary sites. The same holds termwise for a density matrix supported on the local frustration-free space. Its product coherent-state measurement law therefore has the usual bond weight times a nonnegative boundary factor. Conditional on the boundary letters, its interior is the same finite-frame Gibbs law. Arbitrary entanglement of boundary virtual spins is allowed; the nonnegative boundary factor is not assumed to factor over sites.

Use the enlarged designs from 13. Their spin-2 coherent effects span all Hermitian matrices, since every coherent diagonal matrix element is a spherical polynomial of degree at most four and its vanishing identically forces the operator to vanish. Thus product effects determine every local density matrix. The uniform boundary-independence estimate in 12 makes the interior effect probabilities identical in all infinite-volume frustration-free states. Informational completeness then proves equality of the states. Existence follows from a periodic thermodynamic limit. It follows that all periodic VBS limits coincide and that their common state's GNS Hamiltonian has the gap in 14.

**Cost/value/recommendation: ASK THE AUTHOR; strong result, medium paper cost, high Lean cost.** It needs open-region polynomial divisibility, informational completeness, and a compatible-family/state construction. The original 12/20 coherent POVMs have too few effects to justify this proof on their own. Claim uniqueness of the frustration-free state; uniqueness among all locally stable infinite-volume ground states would require a separate argument that such states are frustration free. Fixed-support boundary independence also should not be silently upgraded to a quantitative LTQO theorem for growing supports.

**16. Remove 2x2 blocking entirely if the author accepts a slightly broader finite-state coupling lemma.**

**Statement: true with a small geometric rederivation; not literally a consequence of the present cell-window statement.** MOSPROOF's coupling, path-gap and finite-matrix arguments allow site-dependent finite alphabets. The direct periodic argument in 1 does too. Translation invariance is only a way of transporting a coupling estimate to every placement. Work instead with the physical checkerboard sites, their uniform one-site lower bound `beta>=1/(20*9^4)`, and a window estimate imposed at every translated physical square.

Derive that physical window estimate from (P) using the same tapered `U`, now on sites rather than on a lattice subsequently expanded by two. The distance estimate loses that factor two: the near-cut bound becomes `b>=max(t,l_0/4)-2`, and the far part has distance of order `s/12`. Choose a larger fixed even `l_0` if using the thickening in 3. The count per level stays bounded, so the cost is finite. All moment and cut identities already allow the site-dependent frames. Then run the stopped coupling and direct torus blocks on physical sites.

**Cost/value/recommendation: DO if optimizing the final Lean architecture; otherwise keep the one fixed cell partition of 1.** This deletes the 57,600-letter alphabet, the cell-to-site comparison and all offset bookkeeping, and replaces `alpha` by a much better physical-site constant. The price is restating and proving the site-scale geometric estimate. Do not simply erase blocking while continuing to cite the translation-invariant MOS/MO statements.

**17. Retain the stronger classical rectangular-box Poincaré theorem as an optional result.**

**Statement: already proved in MOSPROOF, after REF-MOS's positive-`alpha` fix.** Both cell side lengths can be arbitrary above its explicit threshold; there are no compatibility or divisibility conditions on cell rectangles, and all fixed frame boundary conditions are allowed. Its single-site physical version follows by the cell comparison, or directly by 16. This is a real strengthening of the classical part, even if the main quantum proof uses only 1.

The limiting finite-frame Gibbs measure also satisfies the corresponding uniform Poincaré inequality on local cylinder functions: take finite-volume inequalities for a fixed local function and pass to the unique local limit. The conditional variance term is a local function of that support and its neighbors. No infinite-time Markov process needs to be constructed merely to state this inequality.

**Cost/value/recommendation: DO in the paper if the MOSPROOF appendix is retained; optional for the first Lean target.** Formalizing the clamped-square construction is necessary for this stronger box statement, but is unnecessary for the periodic quantum theorem. A physical open-boundary quantum gap does not follow from this classical statement; see 19.

**18. Fixed-width periodic strips have a separate cheap-in-principle route, independent of the two-dimensional computer inputs.**

**Statement: true for each fixed even circumference `L>=4`, with a constant depending on `L`.** Treat a column as one finite letter, combining two adjacent columns if a common alphabet is wanted. The transfer weights are strictly positive, because all vertical/internal and horizontal frame bond factors are positive. Positivity yields a uniform contraction of boundary messages in one dimension. Taking a sufficiently long fixed column interval gives a Hamming block contraction; its finite conditional chain has a positive uniform gap. Comparing column updates with the finitely many physical updates in a column proves `inf_N gap(H_(L,N))>0` along even `N>=4`, with a possible finite collection of small lengths handled separately. This uses the existing four-regular quantum comparison, not a new uniqueness extension.

For `L>=L_0`, the paper already covers arbitrarily large aspect ratios with the same two-dimensional constant; no condition `L/N` bounded away from zero is needed. The separate strip argument matters for `L<L_0`. Its constants may deteriorate rapidly in `L`, so it cannot replace the two-dimensional proof.

**Cost/value/recommendation: ASK THE AUTHOR.** Paper: a one-dimensional positive-transfer/block-coupling lemma and a comparison. Lean: finite positive matrices and one-dimensional geometry, but a new auxiliary theorem. Avoid asserting a uniform constant simultaneously over all widths from this argument. Odd-width/frame choices remain with the separately assigned agent.

**19. Separate periodic geometry extensions from open quantum boundaries.**

**Statement: sufficiently large skew periodic quotients are accessible; free cylinders and boxes require new gap arguments.** Entry 1 uses only injective embeddings and translation counts for a fixed square and its exterior ring. It therefore works on quotients `Z^2/Gamma` with that injectivity property. In the cell implementation require `Gamma subset 2Z^2` and apply the criterion on the cell quotient; these conditions ensure the fixed partition descends. Entry 16 would allow checkerboard-compatible periods more generally. No rectangular aspect-ratio bound is used. This is a short geometry corollary, not a claim about arbitrary four-regular graphs: the trail proof still needs the square lattice.

For an `L by N` open rectangle, with spin 2 at every site and `L,N>=3`, the actual ground-space dimension is

`3^4 * 2^(2L+2N-8)`.

Indeed multiplication by `B_internal` identifies its kernel with polynomials of residual degree `4-deg(x)` at each boundary site: degree two at each corner and degree one at other boundary sites. On a cylinder of circumference `L>=3` and open length `N>=2`, the dimension is `2^(2L)`. Hence a unique open-boundary ground state is false. The rank-one multiplication/heat-bath comparison in Section 2 cannot control the entire degenerate boundary ground space. A gap above it may hold, but is not supplied by the present argument. Fixed virtual boundary caps or different boundary spins change the model and need a new comparison.

**Cost/value/recommendation: DO the skew-quotient observation if desired; DO NOT claim the free-boundary quantum extension.** The obstruction is algebraic and explicit. This also prevents confusing MOSPROOF's classical rectangular-box theorem with a quantum open-box theorem.

**20. State only the mixing and numerical hypotheses that are consumed; avoid rebuilding the proof merely to weaken them.**

**Statement: several weakenings are valid.** (H1) is used as a uniform step-ratio inequality on the corrected covered class, and only through upper bounds on departures occurring in the closure argument. It need not assert a global optimum for `c_s,c_t`, identify minimizing pins, or compute exact infima. A supplied inversion choice is a witness, not an optimization problem to formalize. The purported global minima in the constants table must stay corrected as in ADJ-R6/ADJ-MINOR.

(H3′) can be replaced by the positive-vector inequality of 9. The orderings can be any fixed admissible choices; optimality of the short-trail ordering is unnecessary for the abstract implication. They must be fixed before the continuation in `theta`. The open-trail estimate must explicitly use an absent incoming bond/forbidden first reversal, as required by ADJ-R5. Uniformity over all pins and all ordinary consistent domains in the response envelope is essential; typical-boundary or only untraced-domain estimates do not close the recursion. Auxiliary terminal networks need only support the two stopped expansions, not the whole response supremum.

Exponential (P) is stronger than the cut argument needs. A nonincreasing response bound with `sum F(d)<infinity` and `sup d^2 F(d)<infinity` suffices with the sharper `O(s^2)` long-side count, so decay of order `(1+d)^(-2)` would work. Even the frozen crude count needs only `O(d^(-8))`, not little-o, because bounded cost suffices; REF-R3 explicitly identifies that correction. A sufficient corresponding replacement for exponential (H2) is finiteness of the third moment `sum n^3 W_n`: it makes the kernel's second shift moment finite. Weighting by `(1+d/R)^(-2)` and then taking large `R` preserves contraction, since `sum M_s(1+s/R)^2 -> M_1`; the stopped two-walk source decays faster than quadratically.

**Cost/value/recommendation: DO narrow the formal interfaces; DO NOT switch to polynomial renewal unless another proof route benefits.** These are analytical weakenings, not new certificate searches. With an available geometric growth certificate, exponential sums are simpler to formalize and also give better corollaries.

**21. Make the closed-form/FKG part of (H1) optional; prefer a single proof path if kernel cost is comparable.**

**Statement: true using existing archived certificates.** `certificates_covered_operator_only.jsonl` already gives an operator witness for all 7,962 patterns. Using it removes the general three-field radius lemma, finite FKG theorem, pruning recursion and exact minimization from the main proof. The closed forms can remain examples and upper obstructions. Conversely, the mixed file reduces the number of operator patterns to 3,227 but adds the closed-form theory.

Before the scope change I counted the actual exchange-sector dimensions from the pattern graphs and selected representations; see [h1_sizes.py](h1_sizes.py) and [the saved counts](experiments/h1_sizes.json). The mixed file needs 6,551 central exchange blocks, at most 179 by 179, and 55,754,578 upper-triangle Bareiss cell updates. The operator-only file needs 12,173 blocks and 58,961,514 updates. Thus eliminating the closed-form theory increases this particular arithmetic count by only about six percent, not by the ratio of pattern counts. The paper's 245 is a combined historical diagnostic; ADJ-R6 established that the actual largest split block is 179.

A previously identified further option is full highest-weight compression. Representation multiplicities predict maximum blocks of size 59, and 4,493,291 upper-triangle updates for the operator-only family. These are exact dimension/operation counts, **not generated or verified compressed matrix certificates**; rational basis construction and coefficient growth remain costs. Entry 5 already removes representation classification from the existing central-sector proof and requires no new matrices.

**Cost/value/recommendation: DO choose one main proof path; ASK THE AUTHOR before adding full highest-weight compression.** The all-operator path can save much more Lean theory than its modest arithmetic increase costs. PROBE1 also makes it necessary to shard large matrix verifications or supply smaller congruence blocks; total arithmetic throughput alone is not a memory estimate. The most attractive choice depends on the certificate owner's final checker architecture.

**22. Distinguish a better proof constant from a useful physical gap; omit unused optimizations from the core formalization.**

**Statement: true, with limited payoff.** Raising the two local constants slightly is constrained by explicit decoupled patterns and does not remove the large-scale losses. The stronger bound near `0.91825` is a contraction-kernel bound, not a quantum gap. It must not be advertised as such. Entry 1 and the explicit cell comparison improve the final quantitative chain much more directly.

If retaining Section 3, choosing a larger flat box gives heat-bath gap at least `(1-epsilon)c_0 m_0`, and hence quantum gap at least `(1-epsilon)g_star c_0 m_0/2`, for each fixed positive `epsilon`, instead of the displayed factor `1/4`. The weighted threshold reduces the needed box size from order `m_0^(-1)` to order `m_0^(-1/2)`, but needs its additional autocorrelation and weighted-operator proof. These facts do not produce a physically useful numerical lower bound when the preceding `m_0` is extremely small.

Likewise, bulk-field perturbations or a general stability theorem are not cheap corollaries of the periodic gap alone. Bulk fields alter the bounded-degree identities and closure; gap stability needs further local information, not just finite-volume uniqueness and clustering. Related AKLT work proves additional boundary-indistinguishability/LTQO estimates for other lattices before invoking stability; it is not a theorem about this square-lattice model ([Jackson–Nachtergaele–Young](https://arxiv.org/abs/2605.12184)).

**Cost/value/recommendation: DO remove the unused weighted criterion from the main Lean dependency; DO NOT spend the preformalization budget on a useful decimal gap or perturbation theorem without a separate author decision.** The direct periodic proof supplies a cleaner constant and removes the need for that criterion altogether.

**23. Prior certificate work, handed off after the scope change — no further search undertaken here.**

**Ideas already considered:** smaller one-step (H2) windows; block lookahead; using the already documented type-dependent response coefficients; smaller (H3′) memories/quotients; and static right-potential inequalities `U>=reward+T U` in place of replaying a long walk evolution. A valid nonnegative Bellman supersolution would bound every finite tail by induction and then the infinite tail, without a remainder-vector division or a spectral-radius computation. It would still need a correct unbounded-space/quotient domination and a cheap prefix construction. Merely supplying a short final row-sum file is not a certificate for the computation that produced it.

The following are **measurements from runs started before the transfer**, retained for the other agent. C runs were single-core; the scan launcher used at most three simultaneous jobs. All outputs and sources are under this directory, with resource/time records. No run approached the prescribed RAM/disk limits.

| Existing experiment | Size | Result | Measured time |
| --- | --- | --- | --- |
| One-step H2, memory 6 | 916 windows, 115 dihedral classes, 2,628 transitions | Exact rational row check passed; quotient `81907642/81943429`, `q=0.9996`, computed `C_V<8` | 0.035 s Python search/check |
| One-step H2, memory 8 | 7,500 windows, 938 classes, 21,268 transitions | Exact rational row check passed; `q=0.988`, computed `C_V<176` | 0.303 s Python search/check |
| H3 diagnostic finite-box Bellman, C row, memory 6, prefix 10, radius 12 | 2,290,000 scalar states | Relaxed-bound ratio about 1.43653; failed | 7.31 s, 37,428 KiB RSS |
| Same, memory 8, prefix 14, radius 16 | 32,670,000 scalar states | Ratio about 1.08672; failed | 56.31 s, 454,716 KiB RSS |
| Same, memory 8, prefix 20, radius 21 | 55,470,000 scalar states | Ratio about 1.00706; failed | 183.51 s, 777,276 KiB RSS |

The H2 rows use an independent exact `Fraction` check with weights `1000/2883, 200/561, 1/5`; the candidate vectors are [memory 6](experiments/h2_m6_certificate.json) and [memory 8](experiments/h2_m8_certificate.json), with [checker](h2_small.py) and [saved summary](experiments/h2_small_summary.json). These are mathematical rational checks, not Lean-accepted theorems. The H3 prototypes used floating-point iteration and killed paths leaving a finite box. Their exact finite-box targets are **lower bounds on the corresponding relaxed infinite-walk totals**; the floating outputs are diagnostic approximations, not certified lower or upper bounds. They are not valid upper certificates for the manuscript kernel. These numerical failures suggest that those particular relaxations lose too much; they are not counterexamples to (H3′). Forward quotient trials also failed to close at the tested smaller memories. Their logs, and the scan sources, are in [experiments](experiments/).

**Cost/value/recommendation: HAND OFF as high priority; no successful cheap (H3′) replacement is claimed.** The exact small H2 witnesses are worth retaining, subject to the other agent's preferred rate/cost tradeoff. The failed H3 experiments should prevent duplicating these particular trials. The existing PROBE1 kernel measurements remain the appropriate warning against replaying the original large floating computation as kernel reduction.
