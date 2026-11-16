STATUS: COMPLETE

**Conclusion.** The recommended route is a division-free Gram/residual certificate for H1, a small one-step rational-vector certificate for H2, and a stationary Bellman supersolution for the type-dependent H3 kernel. The last route replaces every long-walk iteration and the geometric remainder by one finite inequality check. The cheapest complete option found by scalar product count uses [M] **memory 9, radius 80, prefix 18 for B and 16 for C**, gives **ρ≤0.998187**, and contains **1,206,889,257 compressed bytes**. A second option uses [M] **memory 10, radius 70, prefix 12**, gives **ρ≤0.993015**, and has much less exact-prefix work. All cases pass independent integer checks, including the rational prefix. I recommend the short-prefix option for the first packed Lean implementation; the probe results should decide between them. Kernel memory remains the principal feasibility uncertainty. A separate minimized periodic computation recovers the literal original H3′ numerical bound if that stronger target is required.

This is a computational feasibility study, not a Lean formalization. No Lean executable is installed on this Mac. The included Lean probes are **uncompiled**, and every kernel time and kernel memory forecast is **estimated**. C/Python checks, including exact integer checks, are evidence for the proposed implementation; they do not yet meet the requested kernel-checking standard.

**Numerical labels and reproduction.** **[M]** means measured, counted by instrumentation, exactly recomputed, or inspected as an exact input in the supplied files. **[E]** means extrapolated or estimated. A table's label applies to every numerical entry in it. Mathematical formulas and code parameters specify exact quantities rather than measured timings. Bounds reported from C are its upward enclosures, subsequently combined as rational numbers; displayed final bounds are rounded upward. Source-stated constants are identified explicitly rather than treated as benchmarks.

All commands below run in `/Users/paronow/aklt-lean/reports/COMPFEAS`. The bundle was copied to `programs/`; modifications and new code are in `experiments/`. The original bundle was not modified. Experiments used no subagents. Numerical libraries were copied from an existing local cache into `vendor/`. Python numerical processes used `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1`; concurrent experiment batches used at most the authorized six cores. Compiler [M]: Apple clang `21.0.0`, arm64 Darwin. Python [M]: `3.14.7` for orchestration/stdlib arithmetic and `3.12.13` with cached NumPy for H1. RSS values in logs are **bytes**, as returned on macOS, not Linux's KiB.

The frozen manuscript is the source of the definitions: `sec6-walks.tex` defines patterns/H1; `sec7-recursion.tex`, especially `e:kernel`, defines H3′ and the implication to the recursion theorem; `sec8-computer-assisted.tex` defines the finite H2 test; Appendix C is `app-tail.tex` and Appendix D is `app-local.tex`. I also read the remaining sections to check what numerical conclusions the main theorem actually needs. The main spectral-gap theorem needs contracting bounds and existence of constants; it does not need the particular advertised numerical growth rates.

**H1: what must be checked from the definitions.** A stored pattern index, a precomputed matrix, an inversion mask, or a stored list of positive pivots is not by itself a certificate of H1. The proof must establish all of the following:

1. Enumerate the permitted status/kept-bond configurations, including consistency condition (C), the allowed out-neighbour, reflection, and cancellation of disconnected factors. Relate this enumeration to the list being checked.
2. Derive the site moments, tip radius and optional leaf reductions from the integrals in the paper. Construct the ring tensor network from each pattern. Its integer tensors represent `3 D Zcur` and `5 D Znext`; the positive common denominator `D` must be justified, not imported as a physical assumption.
3. Apply the inversion mask to the computed coefficients, substitute the Pauli matrices, and restrict/conjugate into the exchange and spin sectors justified by Appendix D. The matrix to test at `c=p/q` is exactly `5 q A − 3 p A′`.
4. Establish positivity of the computed matrix, and use the coherent-state, reduction and sector lemmas to return to the original integrals on the product of spheres.

The only search information that needs to be supplied is the representation/inversion choice and a positivity witness. Neither optimizer output nor floating eigenvalues enter the proof. Uniform sphere moments, the diluted measure and the radius `3/5` are mathematical inputs to be proved once. Checking a matrix that someone claims came from the pattern would leave the main trust gap open.

**H1 measurements.** The independent enumeration in `experiments/enumerate_patterns.py` starts with the kept-bond rules, rather than enumerating the supplied JSON records. It found [M] **106,101 valid status configurations**, **184,914 configurations with an out-neighbour marked**, and exactly the supplied **7,962 effective classes**, with no missing class. Restricting the marked out-neighbour to N/E before reflection gives [M] **123,339** cases. Thus the number **106,101** counts status configurations, not marked patterns. Pruning inconsistent corner choices needed [M] **26,550 consistency tests** in this implementation; enumeration and comparison took [M] **2.89 s**, peak RSS **67,518,464 B**. The source's raw Cartesian status space has [M, counted from the options] **2,048,000** choices before pruning.

```sh
python3 experiments/enumerate_patterns.py
PYTHONPATH=vendor OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  /opt/homebrew/bin/python3.12 experiments/profile_h1.py
PYTHONPATH=vendor OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  /opt/homebrew/bin/python3.12 experiments/profile_h1_sparse.py
PYTHONPATH=vendor OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  /opt/homebrew/bin/python3.12 experiments/profile_h1_operator.py
```

`profile_h1.py` rechecked all [M] **7,962** mixed certificates: **4,735** scalar closed-form certificates and **3,227** operator certificates. It took [M] **1,473.56 s**, peak RSS **637,698,048 B**. The integer contraction counters below count the contraction itself, not its extra floating shadow, tensor allocation, coefficient formation, operator assembly, or pattern enumeration.

| H1 workload | Counts [M] |
|---|---:|
| Mixed certificates: tested central exchange blocks | 6,551 |
| Mixed: matrix entries / pivots | 4,120,149 / 102,857 |
| Mixed: Bareiss upper-triangle updates | 55,754,578 |
| Mixed: Bareiss multiplications / subtractions / divisions | 106,843,606 / 51,089,028 / 55,754,578 |
| Mixed: largest input / pivot bit lengths | 56 / 9,111 |
| Mixed: dense tensor-contraction multiplications / additions | 49,604,635,748 / 45,770,980,272 |
| All operator certificates: blocks / matrix entries | 12,173 / 4,742,248 |
| All operator certificates: Bareiss updates implied by dimensions | 58,961,514 |
| All operator certificates: dense contraction multiplications / additions | 51,135,092,925 / 47,136,614,016 |
| Same contractions, skipping zero products | 95,447,163 multiplications; 3,441,984 additions |
| Both final coefficient tensors: nonzero / dense entries | 46,581,420 / 750,697,734 |
| Largest coefficient bit length in those tensors | 42 |

The sparse counts are obtained on the actual contraction inputs. For each contracted index, multiply the numbers of nonzero entries on its two sides; sum these products, matching the contraction axes in their specified order. Since these tensor entries are nonnegative, the number of additions after omitting the first term in each nonzero output is the number of products minus the number of nonzero outputs. They describe an executable sparse algorithm, not a measured speedup of Lean or a completed sparse Lean implementation. The final all-operator coefficient pass took [M] **247.66 s**, RSS **483,819,520 B**. Logs: `h1_summary.json`, `h1_sparse_summary.json`, `h1_profiles.jsonl`.

The current checker already splits diluted-corner exchange parities more finely than some stored certificate metadata. A stored block of size [M] **245** for pattern [M] **3596** becomes blocks of [M] **131, 48, 48, 18**. The largest block actually reconstructed by the present checker, for both certificate files, is [M] **179**. The paper's upper size bound remains valid, but using its largest stored size for every operation estimate would overstate the current work. `h1_dimensions.py` recomputes these dimensions without trusting stored sector sizes.

There is still substantial operator work after sparsifying the positive tensors. A full pass through the actual operator construction measured [M] **1,595,793,828 nonzero Pauli-entry placements**, **591,817,524 additions with both operands nonzero**, and **810,303,852 nonzero products in pair-basis/projection contractions**. Those latter basis entries are zero or signed units, so a sparse implementation can replace their products by copies/sign changes. Dense equivalents were [M] **11,704,562,352 Pauli additions** and **26,980,960,432 basis products**. Final operators contained [M] **20,971,976 nonzero entries** across both operators of all patterns. This pass took [M] **384.86 s**, RSS **656,965,632 B**. Sparse tensors help enormously, but they do not make operator assembly free. See `h1_operator_summary.json`.

**H1 certificate recommendation: dyadic Gram factor plus a diagonally dominant residual.** I generated and exactly checked this witness on *every* operator certificate, including the scalar-covered patterns. Across [M] **12,173** blocks:

- [M] **8,439** blocks were already strictly diagonally dominant with positive diagonal and needed no factor.
- [M] **3,734** blocks accepted a quantized lower-triangular Gram factor.
- [M] No block failed. The two complementary runs took [M] **286.62 s** in total; their largest RSS was [M] **699,777,024 B**.
- The factors have at most [M] **23-bit** entries, [M] **2,184,033** stored triangular entries in total, and require [M] **60,154,555** triangular dot-product multiplications. These are bounded-size products rather than divisions of the large Bareiss minors.

For generation only, divide the matrix by a common positive factor, choose a small positive rational diagonal shift below its numerical smallest eigenvalue, Cholesky-factor the shifted matrix, and round the factor to a common power-of-two denominator. The *check* uses none of those floating calculations. A witness can consist of positive integers `g,d,S` and an integer matrix `L`; check that

\[
E=d S^2 M-g LL^{\mathsf T},\qquad
E_{ii}>\sum_{j\ne i}|E_{ij}|.
\]

Symmetry of the matrix reconstructed from the pattern makes `E` symmetric. The elementary quadratic-form proof of strict diagonal dominance gives `E>0`; `g LLᵀ` is positive semidefinite, so `M>0`. This format needs no division, gcd, pivot sequence, inverse, determinant, rational normalization, or claimed eigenvalue in the inner check. The common-factor normalization used by the generator need not even be verified as a gcd: the displayed identity/inequalities are sufficient. The diagonal shift used to find the witness can be omitted from the certificate.

```sh
PYTHONPATH=vendor OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  /opt/homebrew/bin/python3.12 experiments/profile_h1_chol.py
PYTHONPATH=vendor OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  /opt/homebrew/bin/python3.12 experiments/profile_h1_chol_extra.py
```

Logs: `h1_chol_summary.json`, `h1_chol_extra_summary.json`, the corresponding JSONL files, and sample factors under `data/h1_chol_*.json`. The first command handles the mixed file's operator cases; the second handles the remaining cases of the operator-only file. The total is not a sample extrapolation.

Only representative factors were retained; the full set was generated and exactly checked in memory. Storing all triangular factors at the observed maximum width would take [E] about **6.3 MB** of packed coefficient data, plus scales, indices and pattern/representation metadata. A production exporter should emit them during the same reconstruction/check pass.

A rational LDLᵀ identity is also sound, but its exact entries can inherit large denominators. Bareiss is a useful fallback, not the preferred certificate. An approximate inverse congruence `RᵀMR` followed by diagonal dominance works mathematically, but usually needs two dense matrix products; the Gram-residual format uses fewer products and smaller data. The closed-form option remains attractive if the sharp-radius/FKG argument is already formalized. For this bundle it saves relatively little numerical work compared with the all-operator version, because most omitted blocks are tiny; using all operator witnesses avoids needing that extra mathematical development just for computation.

A further exact SU(2) multiplicity decomposition could reduce the largest positivity block to [M, dimensions counted] **59**. The all-operator sum of Bareiss updates would fall from [M] **58,961,514** to **4,493,291**, or [M] **5,240,823** Gram dot products if every multiplicity block were factored. This is a dimension calculation, **not** a generated/verified set of smaller matrices. Constructing integer/rational highest-weight bases, checking completeness, and forming their congruences costs work and mathematics. Since the tested Gram check is already small relative to operator construction, I would optimize the sparse/packed operator construction first.

**H1 kernel cost and risks.** A literal dense contraction implementation has [M] about **98.3 billion** multiply/add operations before operator assembly. At the provisional kernel rates below, even its arithmetic alone is [E] roughly **14–550 CPU-hours**; list/indexing/reduction caches can make it much worse. The tested division-free certificate reduces the positivity arithmetic to [M] about **60 million** small products plus sums and dominance checks. An engineered sparse or packed constructor plus these certificates is [E] roughly **2–200 CPU-hours** for H1, with wide uncertainty dominated by operator construction and allocation. Independent patterns/blocks can be checked in separate modules; [E] **1–8 GB per suitably small chunk** is a target, not a measured Lean result. A single monolithic reduction is a poor design.

For nonnegative tensor contractions, a second implementation worth probing is Kronecker packing: encode a coefficient array as base-`2^b` digits of a `Nat`. Slot sets of two factors are disjoint; after spacing one factor's exponents, one `Nat.mul` forms their outer product. Bound coefficients to exclude carries and add the contracted terms. Bit masks/shifts can implement batches of Pauli transforms. This replaces many scalar reductions by large GMP operations, but needs proved packing/stride lemmas and care with signed coefficients. It was not implemented for the full H1 constructor in this study. H1's main risks are construction correctness, completeness of pattern coverage, inefficient sparse-map implementations, and the formal sector/reduction lemmas—not whether floating optimization can find a positive witness.

An alternative mathematical constructor is to retain sphere-moment contractions as partial pairing diagrams instead of expanding all Pauli entries. Each external slot is affine and O(3) invariance gives products of disjoint dot products; the operator of a paired dot product is `2*Swap−Id`. This may allow construction directly in a permutation/sector representation. It still needs a proved diagram calculus and measured implementation, so no speedup is assumed in the H1 forecasts.

**H2: the exact statement and the finite check.** The paper's `M₈` sums extensions of a memory window, remembering the *whole window plus all new steps* during an extension. It is not the eighth power of the one-step memory-forgetting matrix. A step departing from a previously departed site gets the window revisit weight; all other steps get the straight/turn weights. Bond reuse is forbidden throughout that extension. The check is a positive rational vector `h` and a row inequality `M₈h ≤ λh`, followed by `λ ≤ 0.98075^8`. Dihedral invariance can be proved once and permits one row per orbit. To prove H2 as used in Theorem 7, any such contracting finite test is enough.

```sh
clang -O2 -frounding-math -ffp-contract=off experiments/alm_profile.c -o experiments/alm_profile
python3 experiments/sweep.py h2
python3 experiments/h2_grid.py
H2_VECTOR=data/h2_m8k8_vector.txt experiments/alm_vector 8 8 9610 9350
python3 experiments/exact_h2.py 8 8 1/4 data/h2_m8k8_vector.txt
```

The native C reconstruction at the paper's parameters measured [M] **7,500 windows**, **28,856,252 stored nonzeros**, **44,993,196 extension-DFS nodes**, **44,985,696 weight multiplications**, and **28,856,252 leaves**. The clean rerun took [M] **7.10 s CPU time**, with [M] **549,797,888 B RSS** (`logs/h2_clean_m8k8.*`). Its power iteration is search only: [M] **200** iterations plus a final check entail [M] **5,800,106,652** sparse matrix multiply-accumulates. None of those search iterations should be replayed by Lean.

The supplied C source initializes a signed power-of-four table past its integer range, even when the requested memory uses only its safe prefix. Undefined-behavior instrumentation detected [M] overflow at the multiplication forming the table's index **16** (`logs/h2_original_ubsan.err`). The experimental copies use `uint64_t pw4[24]`; the clean rerun has the same counts and bounds. The original bundle is unchanged. This is another reason to check generated mathematical transitions in Lean rather than place trust in the executable.

The independent exact rational-vector check in `exact_h2.py` generated the windows from bonds and grouped them into [M] **938** dihedral classes. It checked [M] **5,627,018** extension weight multiplications and **3,609,484** leaves, with at most [M] **208-bit** row numerators; [M] **13.17 s**, RSS **20,430,848 B**. It reproduced [M]

\[
\max (M_8h)_i/h_i
=0.8559487103256669\ldots <0.98075^8.
\]

The integer vector has [M] `max h/min h = 100`. With common denominator [M] **2,156,484**, the three step numerators are [M] **748,000; 768,800; 539,121**. Store that vector and check generated extension sums against it using integers and a common denominator. A claimed CSR matrix or claimed orbit list is unnecessary. `data/h2_exact_m8k8_r4.json` contains the exact fractions and the proposed vector.

The extension counter does not include multiplication by the terminal vector entry. Including it gives [M, counted from the recursion] **9,236,502 integer multiplications** and **5,627,018 recursive-sum additions**, before geometric tests, lookup and the final row comparisons. Powers/common denominators can be precomputed once; no normalized rational is needed at every edge. In the one-step test below, omit multiplication by the initial unit weight, leaving [M] **330 weighted-vector products** on representative rows, or **2,628** if checking all raw windows as the supplied Lean probe does.

**Much cheaper H2, if the advertised numerical rate is not required.** The paper explicitly permits replacing the revisit weight by the true `1/5`. With that change, memory [M] **6**, extension length [M] **1**, already contracts. The exact orbit check has [M] **115 classes**, **330 admissible class-representative extensions**, and **62-bit** maximum row sums. It proves [M]

\[
\max (M_1h)_i/h_i
=\frac{1119948287353}{1120437614225}
=0.9995632716486955\ldots <\frac{2499}{2500}.
\]

There are [M] **916** raw windows and **2,628** raw edges. The exact check took [M] **0.0229 s**, RSS **17,989,632 B**. The common denominator/numerators are [M] **2,695,605** and **935,000; 961,000; 539,121**. The witness is positive and its measured ratio `max/min` is [M] about **5.37**, rather than requiring a nearly zero coordinate. Reproduce with:

```sh
clang -O2 -frounding-math -ffp-contract=off experiments/alm_fifth_vector.c -o experiments/alm_fifth_vector
H2_VECTOR=data/h2_fifth_m6k1_vector.txt experiments/alm_fifth_vector 6 1 9610 9350
python3 experiments/exact_h2.py 6 1 1/5 data/h2_fifth_m6k1_vector.txt
```

A weaker rate still gives an admissible `θ` sufficiently close to one in the recursion. For completeness, with the paper's revisit weight `1/4`, measured alternatives were: [M] `(m,k)=(7,1)` giving **0.99961279**, `(6,3)` giving per-step **0.99785571**, and `(6,4)` giving **0.99553594**. Memory [M] **4**, extension [M] **4**, fails. The successful true-weight test is the cheapest one-step memory tested here; this is a search result, not a proof of global optimality among every possible automaton/certificate.

**H2 kernel cost and risks.** The small test needs only an untrusted integer vector plus a checker whose enumeration and weights are proved to implement the definitions. [E] **1–300 seconds** is a reasonable first range for an engineered small test, possibly longer if point/bond lists or witness lookup are poorly represented. Allow [E] **0.2–2 GB**, including imports and reduction overhead, as an initial small-check memory budget. The original orbit-reduced `M₈` check is [E] **0.3–30 CPU-hours**, mainly geometric list traversal and row-vector lookup, not big-integer multiplication; target [E] **0.5–8 GB** with separately checked row chunks. Both need far less kernel memory than a stored dense rational matrix. Use a balanced lookup tree or a proved orbit map, never repeated linear lookup in the whole vector. The rate `0.98075` and the paper's explicit `C_V` estimate are separate optional numerical targets; the small test proves the H2 hypothesis needed for the gap, not those particular numbers.

**H3′: what the original computation actually does.** The quantity is the infinite nonnegative trail sum defining the two-by-two matrix, including first-hit stopping at `v`, exclusion of the removed centre `c`, exact dead response pairs, revisit factors, and the chosen exposure ordering. Bounding open trails only loses too much. The finite computation must connect every relaxation to those definitions.

The original implementation enumerates prefixes/short closed trails, then propagates four phases for the straights-first order. Mode A retains the first-step class and the geometric rules up to the intermediate cutoff. Mode B releases the rules earlier, allowing a valid bound for all long trails. After the final time, a left sub-invariant vector bounds each spatial entry and supplies the geometric remainder. The small sub-invariant-vector check is not the expensive part; constructing the vector by power iteration is untrusted search.

At the paper's parameters the measured/enumerated graph has [M] **60,092 windows**, **1,568 sites**, **4 phases**, hence **376,897,024** entries per whole vector. Two binary32 buffers occupy [M, formula] **3,015,176,192 B**. A raw run at the same memory/quotient size measured RSS [M] **3,021,717,504 B**. The full paper assembly uses [M, counted from its modes] **925** propagation steps across the required runs, not just the final time printed for a single run. There are [M] **54,124 straight**, **108,248 turn**, and **6,720 revisit** window edges.

Consequently the generic dense loops execute [M, exact loop-count formula] **245,251,036,800 transition/site visits** and at most [M, generic arithmetic count] **2,433,016,992,000 floating additions/multiplications**, before exceptional-site coefficient work, indexing, zeroing and search. A first-visit edge updates the four phases with five multiplications and five additions; a revisit uses four of each. Special rules can reduce these counts. Even a traffic estimate using four source reads, four destination reads and four writes per accepted transition is [E] on the order of **12 TB** across the full assembly, before vector resets. Prefix enumeration is also large: the same prefix trees in the minimized full-parameter run visited [M] **5,414,788,663 DFS nodes**, including [M] **15,950,865 closed-trail evaluations**.

Scalar kernel replay at these counts is not an affordable default. Storing every state at every time as a certificate is worse: it introduces enormous data while still requiring local checks. Simulating IEEE binary32 bit-for-bit is unnecessary; exact rational/dyadic upper bounds prove the mathematical inequality directly.

**An exact, much smaller memory automaton.** `minimize_windows.py` minimizes the deterministic finite automaton whose alphabet is the four *absolute* lattice directions, with each permitted transition labelled by its kind. It repeatedly refines equivalence classes until the successor classes and labels agree. For every raw window, `compress_windows` checks all of its transitions against the quotient before using it. This is an exact lumping, not a statistical approximation or an assumption of rotational symmetry.

| Memory | Raw windows [M] | Minimized states [M] | Minimized straight / turn / revisit edges [M] |
|---:|---:|---:|---:|
| 6 | 916 | 124 | 84 / 168 / 64 |
| 7 | 2,628 | 192 | 148 / 296 / 44 |
| 8 | 7,500 | 685 | 460 / 920 / 352 |
| 9 | 21,268 | 1,128 | 796 / 1,592 / 332 |
| 10 | 60,092 | 3,741 | 2,516 / 5,032 / 1,872 |
| 11 | 169,092 | 5,816 | 4,220 / 8,440 / 1,596 |
| 12 | 474,924 | 21,933 | 14,748 / 29,496 / 10,992 |

```sh
python3 experiments/minimize_windows.py 6 7 8 9 10 11 12
python3 experiments/compress_c.py
```

The memory-10 partition was generated and directly rechecked in [M] **1.51 s**, RSS **53,575,680 B**. An equivalence class may merge different arrival directions only when all its usable transitions are revisits; no response/straight coefficient then depends on that direction. This exceptional case was explicitly checked. A Lean checker should enumerate the raw windows and verify, for each direction, admissibility, kind, and the quotient successor. Prove aggregation once by induction. Do not trust minimization, a hash, or a purported quotient transition table. Spatial translations remain explicit; full dihedral reduction of the spatial problem is not automatically available once `u,c,v,D₀` are fixed.

**Parity halves the remainder.** The quotient periods preserve lattice parity. Since `u` and `v` have the same parity, only even arrival times contribute, also after the geometric rules are released. If the final time `T` is even, Lemma C's remainder improves from

\[
 a\,\frac{\lambda}{1-\lambda}\sum_\omega(z_C+z_D)
\quad\text{to}\quad
 a\,\frac{\lambda^2}{1-\lambda^2}\sum_\omega(z_C+z_D).
\]

Thus multiply the printed old remainder by `λ/(1+λ)`. No extra iteration is needed. The calculations in `parity_summary.py` use the upward printed bound on `λ` and exact fractions. This improvement applies to the original coefficients/order as well as the variants.

**Keeping the original H3′ and Theorem 8.1 numbers.** With the paper's coefficients and short-trail cutoff, the minimized run at [M] `m=10,L=20,K=28,T=260` gives row bounds, after the parity improvement, [M] **0.984737** and **0.966344**. Therefore it is strong enough to recover the claimed **0.98779** bound for the original matrix, with room for conservative rounding. Without the parity improvement this particular minimized-vector remainder gives [M] **0.987924**, still contracting but slightly above the advertised bound. The increased looseness comes from aggregating the entries in the final supremum; exact arithmetic does not require identical floating outputs after aggregation.

The minimized full-parameter computation has [M] **23,463,552** vector entries, [M] **187,708,416 B** for its two float buffers, and [M] **13,662,768,000** transition/site visits. It retains the expensive exact prefix tree. This provides a route to the literal original numerical theorem, not just a modified recursion theorem. Our unsplit run additionally forbids a memory-detected third departure at `u`; for true trails this is impossible because the removed centre leaves `u` degree three. This extra domination fact must be proved if reproducing this particular run instead of the original `tailmem4` rule.

**A cheap coefficient refinement sufficient for the gap.** The type-dependent remark's numbers need additional proof; they should not be imported as facts. A simple analytic route proves almost the same constants without an interval branch-and-bound program. Write

\[
 f(s)=\frac{-\log s}{1-s}=\frac1{L(s,1)}.
\]

H1 gives `Iτ ≥ c Jτ`; free positivity gives `I⁰ ≥ J⁰ ≥ 1`; and `Jτ ≥ 116/125`. Consequently

\[
 \beta\le f((116/125)c)/3,\qquad
 \beta'\le f(c)/3,\qquad
 \alpha\le f((116/125)c)/3-f(116/125)/5.
\]

For the last inequality, monotonicity of the logarithmic mean first bounds `α` by `1/(3L(cx,y))−1/(5L(x,y))`, where `x=Jτ,y=J⁰`. Its integral representation has integrand

\[
 \frac1{3((1-t)cx+ty)}-\frac1{5((1-t)x+ty)}.
\]

This is decreasing in both `x` and `y` when `3/5≤c≤1`: the derivative signs reduce to `5c(a+b)^2≥3(ca+b)^2` and `5(a+b)^2≥3(ca+b)^2`. Both follow from `c≤1` and `5c≥3`. Evaluate at the lower endpoints.

The resulting rigorous rational targets, checked against rational logarithm-series enclosures, are [M]:

| Passage | α | β | β′ |
|---|---:|---:|---:|
| Straight | 0.145217 | 0.352782 | 0.340008 |
| Turn | **0.150000** | 0.357549 | 0.344661 |

For the turn α, this argument bounds [M] **0.149982699225**; it does **not** establish the remark's smaller **0.149953**. All successful runs labelled `typedminsafe` use the larger, justified value. For each rational `s`, set `t=(1−s)/(1+s)` and bound `−log s` by its first eight odd-power terms, with remainder at most `2 t^17/(17(1−t²))`. `experiments/coeff_bounds.py` performs the exact rational endpoint checks; it does not assume the displayed decimal logarithms.

This variant changes the response coefficients in the kernel. It proves contraction of the modified kernel allowed by Remark 7, with a correspondingly modified proof of the recursion. It is **not a proof of the original fixed-coefficient H3′ matrix inequality by entrywise monotonicity**. All variants below keep the already certified H1 constants [M] `(961/1000,187/200)`. The weighted vector uses the exact dyadic binary64 value entered as `1.20`; the original run uses the exact dyadic value entered as `1.23`. Rational assembly uses these vectors, not a silently substituted decimal fraction.

**The measured H3′ trade-off.** `K` specifies the diagonal quotient with `2K²` sites; mode-A validity ends at `4K−5`, and mode B releases its rules at `2K−3`. The short-trail/exact-prefix cutoff is `L`. When `L` is smaller than the paper's cutoff, the exposure ordering is changed to optimal through `L` and straights-first afterwards. That remains a fixed, θ-independent ordering and is sufficient for the recursion; it need not reproduce the paper's particular order at every short length.

All values in the following table are **[M]** (counts derived from measured graphs and loop counts). Bounds greater than one mean that the test failed to certify contraction.

| Coefficients | m / L / K / T | Memory states | Whole-vector entries | ρ upper bound with parity | Transition/site visits |
|---|---|---:|---:|---:|---:|
| Original | 6 / 14 / 12 / 400 | 916 | 1,055,232 | 146.444624 | 701,612,928 |
| Safe type-dependent | 9 / 18 / 36 / 300 | 1,128 | 11,695,104 | 0.992788 | 8,312,232,960 |
| Safe type-dependent | 10 / 12 / 24 / 180 | 3,741 | 17,238,528 | 1.000661 | 8,041,213,440 |
| Safe type-dependent | 10 / 12 / 24 / 200 | 3,741 | 17,238,528 | 0.998379 | 8,475,287,040 |
| Safe type-dependent | 10 / 12 / 25 / 130 | 3,741 | 18,705,000 | 1.001886 | 7,783,275,000 |
| Safe type-dependent | 10 / 12 / 25 / 134 | 3,741 | 18,705,000 | 0.999708 | 7,877,475,000 |
| Safe type-dependent | 10 / 12 / 25 / 140 | 3,741 | 18,705,000 | 0.996931 | 8,018,775,000 |
| Safe type-dependent | 10 / 12 / 26 / 120 | 3,741 | 20,231,328 | 0.998011 | 8,418,390,240 |
| Safe type-dependent | 11 / 13 / 22 / 160 | 5,816 | 22,519,552 | 0.988505 | 9,025,074,432 |
| Original | 10 / 20 / 28 / 260 | 3,741 | 23,463,552 | 0.984737 | 13,662,768,000 |

The table does not extrapolate a successful spectral-radius bound from reduced parameters: each displayed successful periodic bound has both rows and all required first-step classes. Native scripts and commands are recorded verbatim in `logs/h3_*.jsonl`; `h3_parity_summary.json` contains row decompositions, and `h3_final_stats.json` contains the counted graph/step costs. The exact-count rerun for the cheapest set is:

```sh
python3 experiments/make_exact_counts.py
clang -O2 -frounding-math -ffp-contract=off experiments/tailmem6_count.c -o experiments/tailmem6_count
python3 experiments/run_best.py
python3 experiments/summarize_h3.py > logs/h3_summary.json
python3 experiments/parity_summary.py
python3 experiments/h3_final_stats.py
```

For the cheapest successful periodic set [M] `m=10,L=12,K=25,T=134`, the two phase buffers occupy [M] **149,640,000 B**, measured maximum RSS [M] **157,581,312 B**. Its full assembly visits [M] **1,556,175 DFS nodes**, performs [M] **7,877,475,000 transition/site loop visits**, and uses [M] **37,801,666,080 multiplications plus the same number of additions** in the four-phase value updates, including the special-site reductions. Coefficient formation, indexing, comparisons and zeroing are additional. The float-update total is [M] **75,603,332,160**, not a count of kernel operations. The measured combined C CPU time is [M] **33.97 s**; timings are hardware/load dependent.

This set's bound is [M] **ρ≤0.999708**, so its margin is small. I recommend the nearby [M] `T=140` set, bound **ρ≤0.996931**, if retaining periodic iteration. Its transition count is only [M] about **1.8%** higher. The table's cheapest means cheapest measured transition/site count among successful tested periodic configurations, not a globally optimal proof certificate.

Two reduced-parameter hazards matter. Memory [M] **4** and **5** have growth above one; the bundled code nevertheless prints a remainder and even a misleading final “rigorous” style output. Those remainders are invalid and were discarded. Also the known-start/second-site third-visit rule needs the initial window to have forgotten those initial visits. I require `L≥m+2`. Runs with `L=m` were exploratory and are explicitly excluded from the passing table/ranking; the program does not enforce this stronger condition. These restrictions are proof obligations, not numerical tuning preferences.

**Recommended H3 route: one stationary supersolution, with no tail iteration.** Work on the actual lattice, rather than a periodic spatial quotient. Keep the minimized memory automaton, the four phases, the removed centre, first-hit target stopping, and the known initial bond/site rules forever. For each of the five first-step cases, supply a nonnegative potential `F(phase,window,position)` satisfying the backward Bellman inequality `TF≤F`. Set its target values to `0,0,1,1` and its centre values to zero. Induction on any finite remaining length bounds the stopped continuation by `F`. Taking the supremum of these nonnegative finite sums proves the infinite-trail bound. No equality to a computed resolvent, convergence rate, floating calculation, or spectral-radius estimate for the huge walk is required.

This potential is stationary in time. It retains more geometric information than a free-walk remainder. The relaxation still forgets older bonds and dead neighbours, so it dominates true trails. On a visit to either of the two known initially departed sites, use `1/5`, prohibit reuse of the initial bond, and kill a memory-detected additional departure. The condition `L≥m+2` ensures the initially known departures are no longer in the memory window. At other sites, use the memory-detected revisit rule and only the removed centre as a dead response neighbour. All these are local domination lemmas to prove from the paper's definitions. They are the same kind of relaxations used in Appendix C, without quotient aliasing or eventual rule release.

Make the infinite lattice finite as follows. On the square `[-R,R]²`, store `F`; outside it set `F(p,w,x)=z(p,w)`, independent of position. Check the small free backward operator inequality `Wz≤z`, positivity of `z`, and `z_C,z_D≥1`. Check `F≤z` at every stored site and the correct centre/target values. For an outside site, each successor has value at most its corresponding `z`, so the free inequality proves the global Bellman inequality there. For an inside site, check its row directly, substituting `z` for a successor outside the square. This proves the infinite-lattice continuation bound from finite data. A plain window-only sub-invariant vector would not give this point-to-point improvement; the spatial defect in `F` is essential.

The short-prefix compact certificate uses [M] **m=10, L=12, R=70**, hence **3,741** memory states, **19,881** sites and **297,499,284** stored phase/window/site values per first-step case. A smaller-state successful variant is described after its measurements below. The last number is larger than the successful periodic vector, but it is checked **once**, with no time history. The suffix values are integers `U`, interpreted as `U/2^16`; coefficient upper bounds are `p/2^48`, with `p` computed by exact rational ceiling from the justified type-dependent constants and the exact dyadic `h_C`. Check each Bellman row by the integer inequality

\[
 \sum_{(q,w',x')} p_{p,w,x;q,w',x'} U_{q,w',x'}
 \;\le\; 2^{48} U_{p,w,x}.
\]

At the target the `C,D` integer value is exactly `2^16`. Outside values use integers `Z` with the same value scale. The common value scale cancels in every local inequality. There is no per-step rounding error to propagate. Floating Gauss–Seidel iteration was used only to find the untrusted candidates; the checker accepts candidates on their inequalities alone. The retained B-north candidate was coarsened from a finer candidate, while the other four were generated directly at the coarse scale. This history is irrelevant to their checks.

All values in the following table are **[M]**, exact rational prefix evaluations displayed with upward rounding. Direction names use the code's first-step convention: north `d=1`, west `d=2`, south `d=3`; the starting site is `(-1,0)` and the centre is `(0,0)`.

| First-step case | Bound before row-vector division | Short closed trails | Prefix leaves at L |
|---|---:|---:|---:|
| B, north (also south by reflection) | 0.351208 | 937 | 89,150 |
| B, west | 0.290600 | 922 | 103,257 |
| C, north | 0.527873 | 715 | 66,947 |
| C, west | 0.380755 | 1,036 | 99,168 |
| C, south | 0.273049 | 861 | 92,748 |

Assembling the **exact fractions**, rather than these rounded table entries, gives [M]

\[
 (Mh)_B/h_B=0.9930142698310279\ldots,
 \qquad (Mh)_C/h_C=0.9847287213394736\ldots.
\]

Thus [M] **ρ(M)≤0.993015<1** for the modified type-dependent kernel sufficient for the recursion theorem. This does not identify `M` with the paper's original uniform-coefficient matrix. The periodic original-coefficient computation above supplies the separate route for that literal assertion.

The independent prefix evaluator uses an edge set and departure counts to generate trails, computes the short-trail exposure ordering with exact rational comparisons, and computes the four phase weights for all surviving length-`L` prefixes with integers. It then takes their dot products with the supplied potential. It uses no C prefix result or floating weights. Its [M] **84-bit** common step denominator gives accumulators of at most **1,014 bits**. Across the five cases it visits [M] **708,097 nodes**, **451,270 leaves**, **4,471 short closed trails**, and performs **3,516,794 phase-weight multiplications**. The sum of its measured per-case wall times, including reading compressed certificates, is [M] **14.70 s**; maximum RSS is **53,673,984 B**. Exact fractions and headers are in `logs/final_stationary_summary.json` and the five `*_coarse_exact_prefix.json` files.

**One-pass checking cost and retained data.** The standalone integer verifier regenerates the raw windows, checks the proposed automaton quotient, checks `WZ≤2^48 Z`, the terminal lower bounds on `Z`, all caps `U≤Z`, all target/centre values, and every nonterminal Bellman inequality. It does not call the floating generator. Its counts are [M]:

| Work for all five stored cases | Count [M] |
|---|---:|
| Nonterminal local component inequalities | 1,487,346,780 |
| Weighted products, including the small free-vector checks | 4,495,437,360 |
| Stored cell cap comparisons | 1,487,496,420 |
| Largest stored U / Z | 43,674,194 / 45,149,758 |
| Scalar certificate payload per case, excluding header/Z | 1,189,997,136 B |
| Combined compressed files | 2,595,319,526 B |
| Maximum verifier RSS | 1,198,129,152 B |

Every integer-file run reports [M] zero failed inequalities, caps or terminal checks. The final rerun's combined measured checking-loop CPU time is [M] **19.28 s**; gzip loading, allocation and window construction are outside that timer. Timings vary substantially with load. The verifier uses unsigned 128-bit accumulators: with 48-bit coefficients and uint32 inputs, even six incoming terms fit well below that width. The observed values fit in [M] **26 bits**, providing an even tighter checked bound for a packed implementation. Native arithmetic safety is checked independently of whether the kernel will use the same representation.

A scalar Lean design also needs one addition per weighted term, a scale shift per checked component, and cap/row comparisons. Those major operations together are [E, implementation count from the measured graph] about **13.5 billion**, before geometry, indexing and bounds on the small `Z` array. The product count alone should not be mistaken for the whole scalar kernel cost.

The retained files are `data/stationary_{B,C}_m10_R70_d*_coarse.bin.gz`. After gzip decoding, their format is nine little-endian signed 64-bit header fields `[m,L,R,nw,sites,vx,vy,valueScaleBits,D0]`, then `4*nw` little-endian uint32 `Z` entries, then `4*nw*sites` uint32 `U` entries. Both arrays are phase-major, then window-major; spatial index is `(x+R)*(2R+1)+(y+R)`. The SHA-256 values in the summary identify these artifacts; hashes are **not** proof evidence. A Lean checker must relate the literal data to its own regenerated windows/positions and prove the Bellman soundness lemma.

Reproduce the exact verification without regenerating any potential:

```sh
python3 experiments/stationary_exact_header.py
clang -O2 -frounding-math -ffp-contract=off experiments/check_stationary_integer.c \
  -o experiments/check_stationary_integer -lz
python3 experiments/check_all_stationary_files.py
PYTHONPATH=vendor OPENBLAS_NUM_THREADS=1 /opt/homebrew/bin/python3.12 \
  experiments/exact_stationary_prefix.py stationary_B_m10_R70_d1_coarse
python3 experiments/final_stationary_summary.py > logs/final_stationary_summary.txt
```

Run the prefix command also with B/d2 and C/d1,d2,d3 before summarizing if independently rebuilding the prefix logs. Generation commands, when wanted, are recorded in `logs/stationary*_commands.jsonl`; `make_stationary.py`, `make_stationary_exact.py`, and `make_stationary_exact16.py` generate the experimental sources. Generation needs hundreds of sweeps and is deliberately excluded from the kernel cost. A fresh coarse candidate is allowed to differ; it must pass the checks and the final row inequality.

**Stationary trade-offs and recommendation.** Reduced stationary experiments found [M] memory **8**, radius **100**, unsplit B bound **1.16505**; memory **9**, radius **80**, short-prefix assembled B bound **1.04087**; memory **10**, radius **50**, assembled B bound **1.83444**. Each fails. At [M] memory **10**, radius **70**, finer 48-bit value certificates passed all local integer checks and gave assembled bound **0.952369**, but retaining all their uint64 files would exceed the study's disk allowance. Those numerical results/logs remain; the large intermediate files were deleted. The retained 16-bit-scale/uint32 certificates trade margin for size. No claim of global optimality over potentials, boxes or precisions is made.

**Cheapest complete scalar-count option found: memory 9 with different row cutoffs.** Reusing the same stationary potential after a longer exact prefix requires no additional memory-walk computation: its Bellman inequalities hold at every suffix time. The exact exposure ordering may use different fixed cutoffs in B and C; it is still a function of the trail independent of θ. With [M] **m=9,R=80**, the [M] **L=14** test gives row ratios **1.030958, 1.014973** and fails; **L=16** gives **1.012234, 0.998187**, so C already passes. Extending only B to **L=18** gives exact row ratios [M] **0.9891143536526144…** and **0.9981862648791905…**. Thus this complete design proves [M] **ρ≤0.998187<1** for its chosen orderings.

All entries in the comparison below are **[M]**. Product counts separate the local certificate check from prefix phase-weight arithmetic; their operand sizes and geometric overhead differ.

| Stationary design | B / C prefix lengths | ρ upper bound | Bellman weighted products | Exact prefix phase products | Prefix nodes | Compressed certificate bytes |
|---|---|---:|---:|---:|---:|---:|
| m=10,R=70, both rows | 12 / 12 | 0.993015 | 4,495,437,360 | 3,516,794 | 708,097 | 2,595,319,526 |
| m=10,R=70 for B; m=9,R=80 for C | 12 / 16 | 0.998187 | 2,829,858,000 | 121,367,432 | 24,458,661 | 1,762,396,753 |
| m=9,R=80, both rows | 18 / 16 | 0.998187 | **1,719,471,760** | **801,223,835** | **161,516,061** | **1,206,889,257** |

The last row uses [M] **1,128** memory states, **25,921** sites and **116,955,552** phase/window/site values per case. Its combined major product count is [M] **2,520,695,595**, the smallest among the complete successful tested designs, but the prefix products reach [M] **1,518 bits** and require substantial geometric traversal. Its local check has [M] **584,732,640** inequalities and **584,777,760** cell caps. The five independent integer-file checks all have zero failures; their maximum RSS is [M] **473,759,744 B**. The B-prefix exact checks took [M] **173.11 s** and **196.36 s**, respectively, on this Mac; they are not Lean timings.

These files use value scale [M] **2^20**, coefficient scale **2^48**, and uint32 storage. Their maximum `Z` is [M] **737,810,237**, so checked values fit **30 bits**. Use [E, proposed packing] **84-bit fields**, guard bit **83**, and **2,177,364-bit** square planes. The generic packed graph has [M] **66,340 weighted whole-plane terms** across the five cases before exceptions. The files are `data/stationary_{B,C}_m9_L14_R80_d*_q20.bin.gz`. Their header retains the generation/evaluation cutoff **14**; the potential inequalities themselves are independent of that cutoff. The verified final cutoffs **18/16** are in the exact-prefix logs and `logs/stationary_routes.json`.

Reproduce the longer-prefix evaluation and comparison with:

```sh
AUTOMATON=data/windows_m9_min.txt experiments/check_stationary_integer_flexible \
  data/stationary_B_m9_L14_R80_d1_q20.bin.gz B 1
OPENBLAS_NUM_THREADS=1 /opt/homebrew/bin/python3.12 \
  experiments/exact_stationary_prefix_extend.py stationary_B_m9_L14_R80_d1_q20 18
python3 experiments/compare_stationary_routes.py
```

Use the corresponding B/d2 file with cutoff **18** and C/d1,d2,d3 with cutoff **16**. Exact commands for all cases are recorded in `logs/integer_file_m9_commands.jsonl`, `logs/exact_prefix_m9_L16_commands.jsonl` and `logs/exact_prefix_m9_L18_commands.jsonl`. The flexible verifier is built by the same compiler command as the original verifier, substituting `check_stationary_integer_flexible.c` and its output name. It regenerates and checks the memory-9 quotient. The two original short-prefix certificate files for B plus the three memory-9 files for C also form the complete middle-row alternative; rows may be bounded with different automata because they bound the same analytically defined kernel at the same constants and vector.

For a **packed** Lean implementation I would still start with **m=10,L=12,R=70**: it avoids the last row's [M] roughly **228-fold** increase in prefix nodes. The measurements below must decide the crossover. The mixed-memory middle row is a useful compromise. Supply a compact balanced table of reachable-prefix endpoint values and check its relation to the full potential once; do not extract a component from a huge packed plane separately at every leaf or trust an unrelated endpoint table.

The short-prefix stationary certificate replaces the periodic check's [M] **37.80 billion products plus 37.80 billion additions** by [M] **4.50 billion weighted products plus sums**, eliminates the entire late-time remainder, and permits packed checks without keeping previous time slices. A generic packed row uses one weighted plane per phase edge: [M, graph count] **226,140 weighted whole-plane terms** across the five cases before special-site/boundary handling. Routing, masking and guards add operations; [E] **a few million large-Nat operations** is the appropriate initial scale to probe, not billions of scalar Lean list operations.

With [M] values below `2^26`, 48-bit weights, and at most six terms, use [E, proposed representation] **80-bit fields** with guard bit **79**. A full square plane is then **1,590,480 bits**. Guarded subtraction checks all component inequalities in parallel once carry/borrow and routing semantics have been proved. This packing has not been implemented end-to-end for the stationary witness. Its source data occupy [M] about **1.19 GB per case** as uint32, but a direct 80-bit widening would occupy [E, representation formula] about **2.98 GB per case** even before kernel overhead. Stream row/spatial chunks, release temporary packed expressions, and avoid loading all five widened cases together. The observed C RSS does not bound kernel RSS. The estimated kernel range below is conditional on this engineering; a monolithic literal check can fail the memory budget even though its arithmetic count is modest.

**A kernel representation that uses GMP rather than a scalar memory walk.** The bit-packing prototype is in `experiments/packed_walk.py`. It represents a spatial plane as

\[
 P=\sum_{s=0}^{Q-1} u_s 2^{bs},\qquad u_s\in\mathbb N.
\]

All plane arithmetic is exact integer arithmetic. Coefficients are upper dyadic rational bounds. Accumulate the weighted incoming planes before rounding once per destination. With a per-lane guard and a proved size bound, adding a repeated rounding bias, shifting and masking computes the upward fixed-point rounding of every lane simultaneously. The spatial translations on the diagonal quotient are shifts/masks and row/column wraps. Exception sites are masked out and handled by the correct coefficient masks. No mutable kernel array is assumed.

A reduced full-walk comparison at [M] `m=6,L=8,K=9` agreed with the C walk to within [M] **5.24·10⁻⁶ relative** through its intermediate horizon; the packed enclosure was tighter because it rounds more accurately. A large-plane prototype at [M] `m=10,L=12,K=25` propagated [M] **8** steps from a C prefix enclosure, checking the lane bounds and site permutation. It used [M] **200,000-bit planes**, **160 bits per lane**, value scale **2⁶⁴**, and weight scale **2⁴⁸**. Measured wall time [M] **20.60 s**, RSS **1,454,751,744 B**; [M] **824,768** large-integer multiplications, **944,480** additions, **1,325,488** shifts, **2,389,680** masks and **904,332** ORs. This Python prototype uses CPython integers, not Lean or GMP, and starts from an imported C prefix enclosure. It is a representation/timing test, **not an end-to-end certificate from the pattern/trail definitions**.

The full periodic packed replay is [E] on the order of **several hundred million** large-`Nat` operations on planes of this size, rather than tens of billions of scalar arithmetic operations. Prove the packing and no-carry lemmas once; verify input/output lane bounds, quotient transitions, exact coefficient bounds, prefix enumeration and the small remainder vector. A particular improvement is to check proposed inequalities using packed guarded subtraction: with all lane values below the guard, a repeated high guard bit in `guard+B−A` tests every component inequality `A_s≤B_s` in one mask. This is especially useful for stationary certificates.

Memory behavior remains a decisive uncertainty. Kernel reductions have immutable terms, allocation, expression caches and proof dependencies. A native packed vector fitting in RAM does not imply a long single kernel reduction fits. Use incoming adjacency lists, streamed plane lists, balanced certificate definitions and separate modules/chunks. Test whether repeated normalization retains previous time slices before committing to replay. Do not solve this by trusting a precomputed endpoint vector. A supplied transition/checkpoint must have its relation to the previous mathematically defined state checked by the kernel.

**Other H3′ approaches evaluated or rejected.** A one-vector Collatz/sub-invariant certificate on the *small window graph* only proves open growth; it cannot replace the closed point-to-point sum. A potential on window × position × phase, satisfying a Bellman inequality with the target reward, can replace the sum and is the stationary route tested above. A free-quotient resolvent potential after the rule-release time can remove the late iteration/remainder, but still leaves the initial killed evolution. Its certificate could be checked once by the same packed inequalities; I did not construct a complete successful free-resolvent certificate here.

Longer exact block extensions in the style of H2 are another valid relaxation if their intermediate geometric rules are retained. Measured [M] memory-6 block growth with revisit `1/5` was **0.99088014** per step for extension four and **0.98269779** for extension eight. This uses smaller persistent state but many continuations; it does not automatically give a cheaper closed-walk certificate. A pure open-trail remainder based on `C_V q^n`, even with an extra length factor for responses, is too coarse near the present growth rates. Symmetry beyond the exact automaton quotient requires proving preservation of the fixed centre, target and first-step rules; dividing state counts by the dihedral-group size without that proof is invalid. Slightly increasing H1 constants may help, but no strengthened H1 claim is used in this report.

**What Lean's kernel can accelerate, and what it cannot.** Lean's natural-number literals use an arbitrary-precision representation and built-in arithmetic; one should use the actual `Nat` operations rather than recreate Peano arithmetic. `Int` arithmetic still has sign/case wrappers, but reaches the underlying `Nat` operations. This is documented in the [Lean reference on natural numbers](https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/). The [versioned kernel implementation](https://github.com/leanprover/lean4/blob/v4.35.0/src/kernel/type_checker.cpp) explicitly recognizes `Nat.add/sub/mul/pow/gcd/div/mod/beq/ble` and bitwise operations including shifts. It does not turn a list into a mutable machine array, accelerate arbitrary recursive arithmetic that happens to be equivalent to these functions, or supply a general GMP override for every arithmetic API. Avoid computing bit lengths with an unaccelerated function when a proposed width can instead be checked by comparison with a power of two.

The logical model of `Array` is list based; the efficient mutable/copy-on-write implementation belongs to compiled execution, not to this proof path. Repeated array updates/pushes or repeated `List.getD` in a large vector can introduce an additional linear factor. Use a proved streaming traversal, balanced lookup, or packed arithmetic. See the [array logical model](https://lean-lang.org/doc/reference/latest/Basic-Types/Arrays/). A compiled timing of a checker does not measure its kernel representation.

Use explicit structural recursion on a list or a `Nat` fuel parameter. A natural-number literal used as fuel does not materialize its entire unary expansion in advance; the recursor can expose one predecessor at a time. Do not assume a general well-founded function reduces. The treatment of accessibility and well-founded fixpoints is version sensitive; [Lean PR 14892](https://github.com/leanprover/lean4/pull/14892) changes that implementation. A safe alternative is a structurally recursive, sufficiently fueled checker, together with a proved equivalence/soundness theorem; no runtime override is needed.

`decide +kernel` requests kernel reduction, whereas ordinary `decide` may first reduce in the elaborator and `rfl` may trigger its own elaborator conversion work before the kernel checks the result. These all produce kernel-checked proofs when used normally; native reduction is a different trust path. The [tactic reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#decide) describes the option. This project should not use `native_decide`, native reduction axioms, or a custom `implemented_by` escape hatch.

For context, a published kernel-checking study reports [M, external measurements] a certificate with **959,442** LRAT hints checking in **247 s** and peaking at **7.8 GiB**, and about **0.22–0.25 ms per hint** on its synthetic cases. Those are composite proof-checking steps, not timings of a `Nat.mul`, and should not be transferred as an AKLT throughput benchmark. The same study illustrates how representation and splitting affect memory. Its evidence supports measuring the actual checker before extrapolating, rather than a universal native-to-kernel slowdown factor. [Tomar, *Re-proving native_decide facts in Lean's kernel*, §7](https://hexagonmath.org/pdf/2611.00373v1).

**Kernel cost ranges are conditional forecasts.** There is no honest universal “elementary operations per second” number for these programs. As a planning prior, use [E] **0.5–20 μs** per small accelerated arithmetic operation with modest surrounding reduction, and allow [E] **several to hundreds of μs** for an operation embedded in allocating/indexing code or on large Bareiss integers. These are deliberately broad unmeasured priors, not published throughput claims. Large packed operations process many limbs at once, so their cost depends on the plane width and must be probed separately. Reduction caches, repeated evaluation and data representation can dominate arithmetic.

| Input/checking design | Kernel forecast [E]; mathematical development excluded |
|---|---|
| H1 dense source-style tensors, then Bareiss | Arithmetic alone roughly 14–550 CPU-hours before operator assembly; naive list construction can extend this to weeks or fail for memory. |
| H1 sparse/packed constructor plus tested Gram/DD witnesses | Roughly 2–200 CPU-hours; independent pattern/block modules permit parallel checking. Peak memory must be controlled by chunking. |
| H2 small true-revisit one-step test | Roughly 1–300 seconds for an engineered checker; a poor list/lookup implementation can take longer. |
| H2 original orbit-reduced extension-eight check | Roughly 0.3–30 CPU-hours; do not replay power iteration or materialize exact-rational CSR arrays. |
| H3 original scalar dense walk | Roughly 14–560 CPU-days for the generic arithmetic alone at the stated prior; list/indexing or float emulation adds overhead. Not recommended. |
| H3 minimized short-prefix scalar periodic walk | Roughly 11–420 CPU-hours for value-update arithmetic alone, with additional representation costs. |
| H3 packed periodic replay | Provisionally 3–300 CPU-hours, with memory retention the main go/no-go question; this must be replaced by measured plane-step timings. |
| H3 packed stationary certificate, recommended | Provisionally 0.5–100 CPU-hours for an engineered, chunked check; literal-data loading and cache retention are unresolved. A scalar check has about 4.50 billion weighted products plus sums/comparisons. |
| H3 smaller memory-9 stationary certificate | Provisionally 1–500 CPU-hours including the much longer exact prefix; lower data and local-check cost do not imply a faster packed kernel proof. Prefix geometry/lookup is the main additional uncertainty. |

These are CPU totals, not promises of wall time divided by the workstation's core count. One kernel reduction is essentially serial. Independent certificates/chunks can run concurrently, but sequential time slices have dependencies, and all workers share RAM and memory bandwidth. First test a single process and then at most the authorized six independent chunks. The reports' native experiments stayed below the process-memory limit; forecasts for a future kernel build require their own measurement.

**Certificate/data engineering.** For H1, keep coefficients/operators in a verified sparse or packed representation and check Gram residuals in row order. For H2, store the small integer vector as data and regenerate the finite transition sums. For H3, use natural-number dyadic coefficients and integer lane bounds. A proposed certificate file can be read/decompressed by untrusted generation/elaboration code and emitted as literal data; the kernel must check every mathematical obligation against those literals. A hash, gzip checksum, C exit code, quoted decimal bound, or an opaque IO function cannot discharge an obligation. Literal numeric data avoids making the kernel parse a huge string or run a native parser. Split data and checks across modules without replacing their relation to the definitions by assumptions.

**Resource and artifact audit.** The final audit [M] compared **116** copied program/data files byte-for-byte with the original bundle, with **zero differences**; generated Python bytecode caches are excluded. It measured [M] about **3.94 GB** total retained workspace data, including both stationary witness sets and cached numerical libraries. The largest measured experimental process RSS was [M] **3,021,717,504 B**, from a raw original-sized H3 walk; the stationary generator was below that. Numerical processes were single-threaded and experiment batches were kept within the six-core limit. Intermediate large potentials were deleted after checking/hashing to maintain disk headroom. Reproduce the audit with `python3 experiments/final_audit.py`; see `logs/final_audit.json`, per-command JSONL records and per-run output/error files. Incomplete exploratory runs, tests with invalid remainder growth, and `L=m` tests are not counted as successful certificates. The study and final review finished within the requested approximately three-hour wall-clock budget; no Lean kernel timing is claimed.

**Ranked workstation probe plan.** The exact files to time are in [`probes/`](probes/README.md). They are uncompiled because Lean is absent here. Pin and record Lean and Mathlib commits. In a Mathlib project, use one fresh process per file, an external memory/time limit, and `/usr/bin/time -v` on Linux or `/usr/bin/time -l` on macOS. Check the process exit status and the printed axioms. First time `Baseline.lean` to separate import overhead. Keep the successful proof terms; wall-clock `#eval` measurements are not a substitute.

1. **Packed arithmetic first.** If using the stationary route, first time `BellmanGuard1.lean` and `BellmanGuard16.lean`: they test the guarded componentwise comparison on [M, exact probe parameters] **19,881 lanes**, **80-bit fields**, and **1,590,480-bit planes**, at the actual spatial scale of the retained stationary certificate. These are performance probes; their simple right-hand side is not the AKLT potential. For periodic replay, time `Packed1.lean`, `Packed16.lean`, then `Packed128.lean`. These contain a nonuniform literal plane, actual east-routing masks for the diagonal quotient, fixed-point rounding, and a structural iteration. They test the proposed GMP route and whether memory retains earlier iterations. If a small number of steps already exceeds the memory budget, stop scaling and prioritize the stationary certificate/checkpoint design. The literal packing parameters are [M, exact probe parameters] **1,250 lanes**, **160-bit fields**, **200,000-bit planes**, with **48-bit** dyadic coefficients. The core code being timed is:

```lean
-- Constants and a nonuniform inputPlane are literal Nats in probes/Packed*.lean.
def east (p : Nat) : Nat :=
  let odd := Nat.land p oddMask
  let shifted := Nat.lor (Nat.shiftLeft (Nat.land odd notLastMask) 160)
      (Nat.shiftRight (Nat.land odd lastMask) 3840)
  let a := Nat.lor (Nat.land p evenMask) shifted
  Nat.lor (Nat.land (Nat.shiftLeft a 4000) allMask)
      (Nat.shiftRight a 196000)

def oneStep (p : Nat) : Nat :=
  let numerator := p * 140737488355328 + east p * 140737488355328
  Nat.land (Nat.shiftRight (numerator + roundBias) 48) lowMask

def packedLoop : Nat → Nat → Nat
  | 0, p => p
  | n+1, p => packedLoop n (oneStep p)

theorem checked : Nat.land (packedLoop 16 inputPlane) highMask = 0 := by
  decide +kernel
#print axioms checked
```

This is a performance probe, not a proof of the no-carry/packing semantics. After it passes, prove and time those lemmas and one actual full memory-walk or Bellman row. Measure ordinary `decide`/`rfl` on a copy if useful, but distinguish elaborator time from kernel reduction.

For the memory-9 certificate also time `Bellman9Guard1.lean` and `Bellman9Guard16.lean`, using its [M, exact probe parameters] **25,921 lanes** and **84-bit fields**. Before choosing the longer-prefix design, time `PrefixLeaves8.lean`, `PrefixLeaves10.lean`, `PrefixLeaves12.lean`, then optionally `PrefixLeaves14.lean`. They stream the actual B/north bond-trail enumeration with the removed centre and first-hit stopping, checking [M] **1,466; 11,482; 89,150; 688,590** surviving leaves. These isolate geometry, omitting phase weights and potential lookup, so they give a lower bound for a full prefix checker. Their complete code and literal expected counts are in the files. The principal recursion is:

```lean
def leaves : Nat → Point → List (Point × Point) → Nat
  | 0, p, _ => if eqP p (1,0) then 0 else 1
  | n+1, p, es =>
    if eqP p (1,0) then 0 else
      [0,1,2,3].foldl (fun acc d =>
        let q := move p d
        if eqP q (0,0) || used es p q then acc
        else acc + leaves n q ((p,q)::es)) 0
theorem checked : leaves 11 (-1,1) [((-1,0),(-1,1))] = 89150 := by
  decide +kernel
```

The stationary probe's exact core is below; its masks and nonuniform plane are literal data in `BellmanGuard*.lean`. Start with `rows 1 plane`, then `rows 16 plane` as supplied. It deliberately isolates guarded arithmetic rather than claiming to implement an AKLT row.

```lean
def rotate (p : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.shiftLeft p 80) allMask)
    (Nat.shiftRight p 1590400)
def rowOK (p : Nat) : Bool :=
  let lhs := p * 93824992236886 + rotate p * 93824992236886
  let rhs := upper * 281474976710656
  Nat.land (guard + rhs - lhs) guard == guard
def rows : Nat → Nat → Bool
  | 0, _ => true
  | n+1, p => rowOK p && rows n (rotate p)
theorem checked : rows 16 plane = true := by decide +kernel
#print axioms checked
```

2. **Close the small H2 test from generated trails.** `H2Small.lean` contains the proposed integer witness as a balanced decision tree. It generates the windows from the bond-trail definition in Lean, checks every raw window, and uses no imported matrix/orbit correctness assertion. Its final predicate is:

```lean
def check : Bool :=
  let ws := grow 6 { pos := (0, 0), dirs := [], edges := [], departed := [] }
  (ws.length == 916) && ws.all rowOK

theorem checked : check = true := by decide +kernel
#print axioms checked
```

`rowOK` checks positivity and `2500 * rowSum ≤ 2499 * 2695605 * h`. The full definitions and witness are in the file; there is no missing external library-specific checker. A soundness lemma connecting this Boolean statement to the weighted growth theorem is still required. After timing it, optionally add the orbit-reduced original extension-eight test if the numerical rate itself is desired.

3. **Time an actual H1 factor check, then its constructor.** `H1Gram.lean` contains a measured [M] **131-dimensional** sample matrix/factor and checks its residual in integer arithmetic. It isolates positivity-check cost; the matrix is **literal benchmark data**, so this is not yet H1. The core is:

```lean
def dotI : List Int → List Int → Int
  | a::as, b::bs => a*b + dotI as bs
  | _, _ => 0

def offSum (diag : Nat) : Nat → List Int → Nat
  | _, [] => 0
  | j, x::xs => (if j == diag then 0 else x.natAbs) + offSum diag (j+1) xs

def checkRows (whole : List (List Int)) :
    Nat → List (List Int) → List (List Int) → Bool
  | _, [], [] => true
  | i, mr::ms, lr::ls =>
    let er := mr.zipWith (fun a l => a*factor-dotI lr l) whole
    let diagonal := er.getD i 0
    (mr.length == whole.length) && decide (0 < diagonal) &&
      Nat.ble (offSum i 0 er + 1) diagonal.natAbs &&
      checkRows whole (i+1) ms ls
  | _, _, _ => false

theorem checked : checkRows lData 0 mData lData = true := by
  decide +kernel
```

Next implement **one** pattern's moment contraction, inversion and sector matrix from the pattern data inside Lean, prove the constructor's agreement with the integrals, and rerun the same certificate. Time a small case, the sample, and a largest block. This stage is more informative for total H1 feasibility than running many more literal matrix checks.

4. **Calibrate arithmetic and recursion.** `Nat64/256/4096/16384.lean` and `Int64/4096.lean` contain structural loops at those exact operand-width parameters. For example:

```lean
def natLoop : Nat → Nat → Nat
  | 0, x => x
  | n+1, x =>
    let y := (x*x + 17*x + 19) % modulus
    let g := Nat.gcd (y+1) (x+2)
    natLoop n ((y+g) % modulus)
```

The supplied files force evaluation with a closed theorem proved by `decide +kernel`. Start with the smaller loop counts, then double the count and record both time and RSS. Check for superlinear growth from repeated reduction before extrapolating. These loops intentionally use the built-ins and avoid a general well-founded recursor.

5. **Measure representation overhead and parallelism.** Compare `ListZip1000.lean` with `ListIndex1000.lean`, then their larger variants. The indexed version repeatedly calls linear list lookup; its purpose is to expose the trap, not recommend the algorithm. Finally build independent H1/H2/H3 chunks with several simultaneous processes, respecting the resource limits. An axioms audit alone is insufficient if environments were produced by bypassing the kernel; use clean normal builds and the project's independent checking procedure as well.

Example timing commands, from the pinned Mathlib project, with absolute paths adjusted on the workstation:

```sh
/usr/bin/time -v lake env lean /path/to/COMPFEAS/probes/Baseline.lean
/usr/bin/time -v lake env lean /path/to/COMPFEAS/probes/Packed16.lean
/usr/bin/time -v lake env lean /path/to/COMPFEAS/probes/H2Small.lean
/usr/bin/time -v lake env lean /path/to/COMPFEAS/probes/H1Gram.lean
```

The first decision should be based on the packed-row or Bellman-guard and generated-H2 measurements. They distinguish a viable kernel computation from a native computation that only looks small in C. Formal proof development, especially connecting the constructors and all relaxations to the paper's definitions, remains necessary whichever numerical checker is chosen.
