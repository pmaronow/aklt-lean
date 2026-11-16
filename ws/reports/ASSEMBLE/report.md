STATUS: COMPLETE

# Revised paper assembly

The complete paper is in `/home/ubuntu/aklt/manuscript-v2/`, with the unchanged title, a new abstract and introductory first paragraph, all twelve section files in the plan's order, the cited bibliography, and the built [main.pdf](/home/ubuntu/aklt/manuscript-v2/main.pdf). The theorem states uniqueness for every integer L,N>=3 and a uniform positive gap for all integers L,N>=L0, with either parity for each period.

The final build has 82 pages, zero undefined references, zero undefined citations, zero duplicate labels, and no TeX errors or layout warnings. The inventory contains 105 labelled statement environments, 137 labels, and 353 reference commands. All 182 cross-file reference occurrences are reviewed below, grouped into 103 file/label pairs with every use line listed.

All section inputs and lane reports were read, together with the plan's ownership table and full statement inventory and the previous main.tex. Original section hashes remain unchanged. Six section files are byte-for-byte copies; the other six have only the explicitly requested introduction, comment removal, and removal of editorial history documented below. No mathematical hypothesis, formula, constant, proof step, or conclusion was changed during assembly.

## Build and repository

Build command, run from the manuscript directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error main.tex
```

Evidence: [build.log](build.log), [main.log](/home/ubuntu/aklt/manuscript-v2/main.log), [audit.json](audit.json), and [integration-checks.json](integration-checks.json). The 42 integration checks passed, including exact rational interface arithmetic and preservation of every source statement after the three explicitly recorded editorial substitutions inside statements. The exhaustive H1/H2/H3 certificate calculations were not rerun during assembly; their supplied exact verification evidence and finite contracts were inspected. This report does not claim completed Lean verification.

The directory was initialized as a Git working tree with metadata in `.git-metadata/`. The managed environment reserves the empty `.git/` directory as read-only, so repository commands must specify the metadata directory:

```sh
git --git-dir=/home/ubuntu/aklt/manuscript-v2/.git-metadata \
    --work-tree=/home/ubuntu/aklt/manuscript-v2 status
```

No commit was made. All writes were confined to the manuscript-v2 and ASSEMBLE directories; no sub-agents were launched.

## Main file and bibliography

The preamble inherits the previous macros and theorem environments. The unused editorial `gapnote` macro is omitted. A one-em emergency stretch resolves a 3.01181-point line overflow caused by the resolved lemma number, without editing a section's typesetting or mathematics. The title is unchanged. The abstract and first paragraph state both size ranges, the unrestricted parities, the redesigned three computational inputs, and exact arithmetic. Their new prose uses American spelling and serial commas.

Only AKLT88 and KLT88 are cited, in the new opening paragraph, and both entries are retained from the supplied bibliography, with serial commas in the author lists. The nine uncited entries are removed. The delivered section files had no other citation keys, so no additional bibliography entry was needed. The eight sections and appendices A--D follow the ownership table exactly. Hard-coded section and appendix locators were also checked against this order.

## Mismatches and propagation of source deviations

No additional mathematical mismatch was found in the delivered cross-file uses. Two necessary hypothesis repairs and one certificate-method clarification already appear in the supplied sources; they are retained and checked, not silently reverted to the plan.

| ID | Mismatch with the plan or initial formulation | Owning statement and action | Consumer check |
|---|---|---|---|
| M1 | The parallel-side clearance sentence lacked its nonexceptional index restriction. The supplied counterexample shows the unrestricted sentence is false. | `l:shellgeom`, sec5-window.tex:31: retained the source's one-line restriction to 2<=i<=i1 outside I0. | Section 4 uses the unconditional geometry and cap bounds only in their proper ranges. The only parallel-clearance application, sec5-window.tex:598--602, explicitly checks u>=390^4=M_g(64), 2<=i<=s<i1, nonexceptionality, and intersection with the square. No downstream strengthening is needed. |
| M2 | A second trace cannot start at a protected target v in S. | `l:terminalcover`, sec7-recursion.tex:171: retained the source's one-line hypothesis v not in S and its mathematical counterexample. | The recursion establishes min(d(u,S),d(v,S))>=d>=1 before the use, so both starts are outside S. For d=0 the envelope bound and renewal apply directly; no inadmissible second trace is invoked. The target e already lost an arrival bond, and the second stopping set is S union {e}=S. |
| M3 | The plan's method clause suggested a full set of nonzero Gram factors, while only two were supplied. | `t:inputs`, sec8-inputs.tex:270: retained the supplied clause allowing the Appendix D Bareiss fallback. | Section 8 uses l:integercheck directly for the 3,732 fallback blocks, with positive scales, all divisions exact, and all pivots positive. The 8,439 directly dominant blocks and two nonzero Gram factors complete all 12,173 blocks. It does not apply the Gram-only proposition to a Bareiss certificate. Sections 1 and 4 consume the unchanged H1 conclusion; the new abstract says matrix positivity certificates. |

The original plan and all source directories remain untouched. The following table accounts for every lane's deviations and reported review responses.

| Source | Listed deviation / response | Propagation result |
|---|---|---|
| REV_A1 | No statement deviation. Review clarifications identify t:mainW and l:density and explicitly check their hypotheses. | Both actual owner files are included. The quantum conclusion and positive product probability substitutions match; all previously external labels resolve. |
| REV_A2 | No statement deviation. Review clarifications identify the same-lane color, lift, star, quantum-comparison, and uniqueness results and the final target. | All owner files are included. M>=1, L,N>=2M+3, proper coloring, full conditional finite energy, the factor 1/2, and the exact t:main conclusion are checked at their uses. |
| REV_B | The nonexceptional shell-clearance repair M1; the review also clarified original-volume, metric, degree, connectivity, and counting conventions. | M1 is already satisfied by the only clearance application. Original S(G), arbitrary unit pins, the raw/thick depths, and the factor 5/theta are retained throughout. |
| REV_C1a | No deviation. H1/H2/P remain definitions here, with the computational conclusions assigned elsewhere. | Section 8 supplies the unconditional inputs; Section 7 proves P independently of windows, frames' finite energy, or a gap. All bounded-degree moment uses match Section 2. |
| REV_C1b | The protected-target repair M2. Review correction derives the canonical response coefficients rather than attributing that identity to a stronger imported statement. | Both recursion starts and the terminal degree budget are checked; the coefficient derivation is retained, and the typed bounds use the actual Section 6 ratios/local estimate. All twelve-exception and sum-of-maxima hypotheses match. |
| REV_C2 | Certificate-method clarification M3; no numerical conclusion changes. | The fallback is retained as explained above. H2 uses q_*=1119948287353/1120437614225 and C_V=10; H3 uses the exact type table, dyadic h, five stationary cases, and L=12>=m+2. No consumer needs the older stronger H2 rate. |
| REV_C3 | No deviation. Integer reconstruction, supported sectors, positive scales, division-free Gram soundness, and optional Bareiss are explicit. | Section 8 checks groupwise inversion and every supported central sector, then uses the correct positivity route and ladder implication. No invertibility of a Gram factor or trusted stored matrix is assumed. |

The final plan comparison has six textual statement differences: M1, M2, M3, and three purely editorial changes in d:kernel, h:H3, and l:stationary-assembly. All mathematical source statements are preserved. No unresolved mathematical issue remains from this assembly check.

## Cross-file statement checks

Each row lists every occurrence in the assembled file. “Yes” records comparison of the actual use and the owning statement's hypotheses and conclusion; it is not inferred merely from successful reference resolution. Source-location and paragraph evidence is also retained in [cross-file-contexts.txt](cross-file-contexts.txt) and [cross-file-reviews.json](cross-file-reviews.json). Definition and appendix locators are included alongside theorem applications. Unlabelled imports of H1/H2/H3/P/W, the roadmap, and the abstract were checked against the same contracts.

| Use (all assembled line numbers) | Owner | Match? / hypotheses and conclusion |
|---|---|---|
| [app-finite.tex:221](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:221) (`d:frame`; lines 221) | [sec3-quantum-frames.tex:264](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:264) | Yes. The reference laws have positive weights and precisely the degree-four moments required by the frame definition; no invariance for arbitrary functions is assumed. |
| [app-finite.tex:17](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:17) (`d:framemodel`; lines 17, 221) | [sec3-quantum-frames.tex:490](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:490) | Yes. The laws use the specified three 12-letter frames, proper colorings, uniform site weights, the appropriate interaction sign, and rate-one physical-site updates. |
| [app-finite.tex:222](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:222) (`l:threeframes`; lines 222) | [sec3-quantum-frames.tex:341](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:341) | Yes. The three rotations are antipodal unit-vector fourth-moment frames with weights 1/12 and exact bond bounds b..2-b for both signs; b=(5-sqrt(5))/505 and r_b=b/(2-b). |
| [app-input-contracts.tex:8](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:8) (`d:kernel`; lines 8, 441, 519, 532, 879, 1063) | [sec7-recursion.tex:517](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:517) | Yes. True kernel weights, pair types, shifts, and departure-based dead-site counts match. The stationary suffix operator explicitly relaxes forgotten revisits and dead non-outgoing neighbors, using bprime_type<=b_type for domination; equality of relaxed and true trail classes is never assumed. Exact short and prefix sums retain the actual counts. |
| [app-input-contracts.tex:9](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:9) (`d:kernel-order`; lines 9, 504, 901) | [sec7-recursion.tex:572](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:572) | Yes. The exact dyadic h, rho0, cutoff 12, short rational sorting with index ties, and long straight-before-turn ordering agree. Phase formulas are used for long continuations, with short sums evaluated separately. |
| [app-input-contracts.tex:8](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:8) (`d:weights`; lines 8) | [sec6-walks.tex:655](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:655) | Yes. The lattice revisit weight is exactly 1/5 and records earlier departures. The virtual incoming bond is unused, initial reversal is forbidden, and straight/turn weights are x_type/3. |
| [app-input-contracts.tex:123](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:123) (`h:H2`; lines 123) | [sec6-walks.tex:684](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:684) | Yes. The import is the all-length open-trail sum, uniform over start and incoming direction, with C_V>=1 and 0<q<1. No stronger historical rate bound is required. |
| [app-input-contracts.tex:1228](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:1228) (`h:H3`; lines 1228) | [sec7-recursion.tex:594](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:594) | Yes. The imported assertion bounds every finite cutoff of the specified type-dependent kernel by rho0*h. The same exact positive vector and fixed orderings are used. |
| [app-input-contracts.tex:760](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:760) (`l:log-mean-bounds`; lines 760) | [sec7-recursion.tex:260](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:260) | Yes. The same rational type table is used, including turning a_t=150000/10^6 and bprime_type<=b_type. Appendix C ceilings reconstruct these exact fractions with the exact dyadic h_C. |
| [app-local-operator.tex:15](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:15) (`d:moment`; lines 15) | [sec2-moments.tex:8](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:8) | Yes. Finite U/D laws, separate degree at most four, ambient plane distances, and empty-product conventions agree; no surface integral or arbitrary-function rotation is imported. |
| [app-local-operator.tex:6](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:6) (`d:pattern`; lines 6, 45, 104) | [sec6-walks.tex:488](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:488) | Yes. The covered template retains all twenty slots, both corner slots, full U kept sets except the passage, and covering U tips; effective-record reductions keep precisely its present factors. |
| [app-local-operator.tex:17](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:17) (`h:H1`; lines 17) | [sec6-walks.tex:531](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:531) | Yes. The pointwise inequality is on the complete covered pattern class and every unit slot assignment, at the same thresholds 961/1000 and 187/200; no optimality assertion is consumed. |
| [app-local-operator.tex:117](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:117) (`l:35`; lines 117) | [sec2-moments.tex:197](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:197) | Yes. A covering U tip has exactly three unit slot fields and one optional internal bond. The degree-four numerator and degree-three denominator give a normalized mean of norm <=3/5, exactly the radius required by the leaf reduction. |
| [app-local-operator.tex:66](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:66) (`l:finitefacts`; lines 66) | [sec2-moments.tex:126](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:126) | Yes. The networks have at most four incident factors. Inserted observables are included in the degree-four budget; free positivity is used only without pins, and conditional independence only on positive fibers at nonneighbors. |
| [app-local-operator.tex:59](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:59) (`l:moments`; lines 59, 82, 123, 197, 640) | [sec2-moments.tex:35](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:35) | Yes. Every use is a polynomial calculation of separate degree at most four, including observables. Tight-frame products have degree four, and the Pauli/local formulas use the same U second/fourth and diluted D moments. |
| [sec1-result.tex:66](/home/ubuntu/aklt/manuscript-v2/sec1-result.tex:66) (`d:framemodel`; lines 66) | [sec3-quantum-frames.tex:490](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:490) | Yes. The laws use the specified three 12-letter frames, proper colorings, uniform site weights, the appropriate interaction sign, and rate-one physical-site updates. |
| [sec1-result.tex:13](/home/ubuntu/aklt/manuscript-v2/sec1-result.tex:13) (`d:poly`; lines 13) | [sec3-quantum-frames.tex:14](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:14) | Yes. V4 has the prescribed inverse-binomial monomial norms and finite frame spinor choices. The first paragraph merely locates this normalization. |
| [sec1-result.tex:47](/home/ubuntu/aklt/manuscript-v2/sec1-result.tex:47) (`p:toruskernel`; lines 47) | [sec3-quantum-frames.tex:191](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:191) | Yes. Every invocation has L,N>=3. The owner proves B nonzero and the one-dimensional kernel at every parity, independently of frames or numerical inputs; no assertion for a plane or open box is imported. |
| [sec1-result.tex:96](/home/ubuntu/aklt/manuscript-v2/sec1-result.tex:96) (`t:QD`; lines 96) | [sec3-quantum-frames.tex:646](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:646) | Yes. The periods are at least three, the torus coloring is proper, and the specified frame law is used. The imported lower bound is exactly (g_star/2)*lambda(mu_af), with both local orientation signs retained by its proof. |
| [sec1-result.tex:60](/home/ubuntu/aklt/manuscript-v2/sec1-result.tex:60) (`t:cutMOS`; lines 60) | [sec5-window.tex:696](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:696) | Yes. P(A,theta) supplies A>=2 and 0<theta<1 on arbitrary original unit pins. The conclusion is W(64,p0,Mstar) with common positive constants for every proper plane coloring and translate, as needed by t:mainW. |
| [sec1-result.tex:49](/home/ubuntu/aklt/manuscript-v2/sec1-result.tex:49) (`t:inputs`; lines 49) | [sec8-inputs.tex:270](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:270) | Yes. The import supplies H1 at the prescribed thresholds, H2 with C_V=10 and the exact 0<q<1, and H3_h for the same type-dependent kernel/orderings. Consumers use these conclusions, without assuming a complete family of nonzero Gram factors. |
| [sec1-result.tex:65](/home/ubuntu/aklt/manuscript-v2/sec1-result.tex:65) (`t:mainW`; lines 65, 95) | [sec4-periodic-gap.tex:404](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:404) | Yes. The premise is exactly the uniform W estimate for the plane frame family. Its conclusion is already a quantum torus gap and uniqueness for all sufficiently large integer periods of either parity. |
| [sec1-result.tex:57](/home/ubuntu/aklt/manuscript-v2/sec1-result.tex:57) (`t:rec`; lines 57) | [sec7-recursion.tex:1008](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:1008) | Yes. H1 thresholds, arbitrary C_V>=1 and 0<q<1, and the same type-dependent H3_h/orderings are supplied by t:inputs. Its conclusion P has arbitrary original unit pins and all removed-site pairs required by Section 5. |
| [sec3-quantum-frames.tex:201](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:201) (`d:model`; lines 201) | [sec1-result.tex:15](/home/ubuntu/aklt/manuscript-v2/sec1-result.tex:15) | Yes. The torus edge set is simple and unoriented, each edge appears once, and L,N>=3 gives four distinct neighbors and the stated degree-four valence-bond polynomial. |
| [sec3-quantum-frames.tex:258](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:258) (`d:moment`; lines 258) | [sec2-moments.tex:8](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:8) | Yes. Finite U/D laws, separate degree at most four, ambient plane distances, and empty-product conventions agree; no surface integral or arbitrary-function rotation is imported. |
| [sec3-quantum-frames.tex:772](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:772) (`l:density`; lines 772) | [app-finite.tex:163](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:163) | Yes. The reference law is a positive product probability, with every boundary factor absorbed into its site weights. The density bounds give m/M=r_b^\|E(Q)\|; the frame reference measure of mass 5^\|Lambda\| is not substituted for this probability. |
| [sec3-quantum-frames.tex:262](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:262) (`l:moments`; lines 262, 301, 361) | [sec2-moments.tex:35](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:35) | Yes. Every use is a polynomial calculation of separate degree at most four, including observables. Tight-frame products have degree four, and the Pauli/local formulas use the same U second/fourth and diluted D moments. |
| [sec4-periodic-gap.tex:7](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:7) (`a:finite`; lines 7) | [app-finite.tex:2](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:2) | Yes. Locator: Appendix A contains precisely the finite coupling, conditional-expectation, and Poincare tools used here. |
| [sec4-periodic-gap.tex:436](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:436) (`d:framemodel`; lines 436, 505) | [sec3-quantum-frames.tex:490](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:490) | Yes. The laws use the specified three 12-letter frames, proper colorings, uniform site weights, the appropriate interaction sign, and rate-one physical-site updates. |
| [sec4-periodic-gap.tex:131](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:131) (`l:CE`; lines 131) | [app-finite.tex:22](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:22) | Yes. All relevant laws are strictly positive on finite products with nonempty alphabets. Conditional projections preserve those laws, including complex variance identities and empty resampling sets. |
| [sec4-periodic-gap.tex:448](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:448) (`l:boxlift`; lines 448, 461, 481) | [sec3-quantum-frames.tex:801](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:801) | Yes. Every actual square has integer M>=1 and L,N>=2M+3. Halo reduction is injective, bonds correspond exactly, and the local antipodal sign map transports conditional laws, updates, variances, and Hamming costs. |
| [sec4-periodic-gap.tex:425](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:425) (`l:colour`; lines 425) | [sec3-quantum-frames.tex:434](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:434) | Yes. The periods satisfy L,N>=3; the supplied cycle coloring, including period three and odd periods, gives the proper torus three-coloring actually used. |
| [sec4-periodic-gap.tex:383](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:383) (`l:comparison`; lines 383) | [app-finite.tex:253](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:253) | Yes. The translated squares are a nonempty labelled family of nonempty blocks. Every exterior fiber has gap g_M, the block gap is c>0, and the label multiplicity is T_M. |
| [sec4-periodic-gap.tex:382](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:382) (`l:contraction`; lines 382) | [app-finite.tex:297](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:297) | Yes. P is the average over A=LN block labels; the constructed coupling has expected distance <=1-c/A, with 0<c=T_M-S_M*K<=A. The conclusion uses unnormalized block rates. |
| [sec4-periodic-gap.tex:472](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:472) (`l:density`; lines 472) | [app-finite.tex:163](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:163) | Yes. The reference law is a positive product probability, with every boundary factor absorbed into its site weights. The density bounds give m/M=r_b^\|E(Q)\|; the frame reference measure of mass 5^\|Lambda\| is not substituted for this probability. |
| [sec4-periodic-gap.tex:125](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:125) (`l:finitecoupling`; lines 125, 215) | [app-finite.tex:68](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:68) | Yes. The maximal overlap construction includes zero and full overlap, and marginalization/completion has the asserted direction. The stopped construction retains both full marginals. |
| [sec4-periodic-gap.tex:413](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:413) (`l:planeenergy`; lines 413, 438, 471) | [sec3-quantum-frames.tex:691](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:691) | Yes. Only admissible frame letters are used. Proper colorings give alpha=(1/12)*r_b^4 in (0,1], consistency, and conditional block gap r_b^internal-edge-count; no claim about arbitrary unit pins is imported. |
| [sec4-periodic-gap.tex:82](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:82) (`l:shellgeom`; lines 82) | [sec5-window.tex:27](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:27) | Yes. The stopped-coupling scale satisfies u>=M_g(l0), and all surgery indices lie in 2..i1. Cap estimates are used only outside I0. The parallel-side clause is used in l:cutgeom only after checking its corrected nonexceptional range. |
| [sec4-periodic-gap.tex:500](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:500) (`l:star`; lines 500, 513) | [sec3-quantum-frames.tex:223](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:223) | Yes. L,N>=3 gives five distinct star sites. The same finite positive g_star is used, and sum_x H_x=2H yields precisely the later quantum factor 1/2. |
| [sec4-periodic-gap.tex:133](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:133) (`l:surgery`; lines 133) | [app-finite.tex:132](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:132) | Yes. Each selected joint resampling has, for every fixed input pair, the correct two conditional marginals on F_i; complements stay fixed. Thus each deterministic-index step preserves both full laws. |
| [sec4-periodic-gap.tex:521](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:521) (`p:toruskernel`; lines 521, 538) | [sec3-quantum-frames.tex:191](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:191) | Yes. Every invocation has L,N>=3. The owner proves B nonzero and the one-dimensional kernel at every parity, independently of frames or numerical inputs; no assertion for a plane or open box is imported. |
| [sec4-periodic-gap.tex:503](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:503) (`t:QD`; lines 503) | [sec3-quantum-frames.tex:646](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:646) | Yes. The periods are at least three, the torus coloring is proper, and the specified frame law is used. The imported lower bound is exactly (g_star/2)*lambda(mu_af), with both local orientation signs retained by its proof. |
| [sec4-periodic-gap.tex:546](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:546) (`t:cutMOS`; lines 546) | [sec5-window.tex:696](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:696) | Yes. P(A,theta) supplies A>=2 and 0<theta<1 on arbitrary original unit pins. The conclusion is W(64,p0,Mstar) with common positive constants for every proper plane coloring and translate, as needed by t:mainW. |
| [sec4-periodic-gap.tex:540](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:540) (`t:inputs`; lines 540) | [sec8-inputs.tex:270](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:270) | Yes. The import supplies H1 at the prescribed thresholds, H2 with C_V=10 and the exact 0<q<1, and H3_h for the same type-dependent kernel/orderings. Consumers use these conclusions, without assuming a complete family of nonzero Gram factors. |
| [sec4-periodic-gap.tex:531](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:531) (`t:main`; lines 531, 537) | [sec1-result.tex:38](/home/ubuntu/aklt/manuscript-v2/sec1-result.tex:38) | Yes. The final Section 4 assembly proves exactly the two unconditional conclusions stated in Section 1: uniqueness for all L,N>=3 and one positive gap for all L,N>=L0, without parity restrictions. |
| [sec4-periodic-gap.tex:544](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:544) (`t:rec`; lines 544) | [sec7-recursion.tex:1008](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:1008) | Yes. H1 thresholds, arbitrary C_V>=1 and 0<q<1, and the same type-dependent H3_h/orderings are supplied by t:inputs. Its conclusion P has arbitrary original unit pins and all removed-site pairs required by Section 5. |
| [sec5-window.tex:769](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:769) (`d:W`; lines 769) | [sec4-periodic-gap.tex:31](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:31) | Yes. The conclusion is the same marginal inequality on B_i, for all proper plane colorings, translates, nonexceptional indices, and arbitrary admissible boundaries; l0=64. |
| [sec5-window.tex:4](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:4) (`d:framemodel`; lines 4, 177) | [sec3-quantum-frames.tex:490](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:490) | Yes. The laws use the specified three 12-letter frames, proper colorings, uniform site weights, the appropriate interaction sign, and rate-one physical-site updates. |
| [sec5-window.tex:5](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:5) (`d:pinmodel`; lines 5, 248) | [sec2-moments.tex:97](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:97) | Yes. Every use keeps the original G, original legs, and S(G). Pins are arbitrary unit vectors, and removal creates no pins; the ordinary U/X specialization has exactly these partition sums. |
| [sec5-window.tex:3](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:3) (`d:shells`; lines 3) | [sec4-periodic-gap.tex:10](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:10) | Yes. The physical-site shells use ambient infinity distance, s=u^(1/4), integer floors k_i, the same protected cap A_i, and the same exceptional set I0. |
| [sec5-window.tex:10](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:10) (`h:P`; lines 10, 714) | [sec2-moments.tex:338](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:338) | Yes. Uses concern finite G, arbitrary original unit pins, removed Y disjoint from S(G), and distance-two surviving pairs with a common removed neighbor. Distances remain to the original S(G). |
| [sec5-window.tex:300](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:300) (`l:35`; lines 300) | [sec2-moments.tex:197](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:197) | Yes. After x_j is removed, its distinct surviving neighbors are unpinned, conditionally independent, and have at most three present bonds. Their conditional means therefore have norm <=3/5 on positive fibers, as used in the removal lower bound. |
| [sec5-window.tex:679](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:679) (`l:boundaryconn`; lines 679) | [app-topology.tex:10](/home/ubuntu/aklt/manuscript-v2/app-topology.tex:10) | Yes. At the use, U is finite, nonempty, and star-connected, and U-complement is star-connected by l:cutgeom; hence its raw outer boundary is nonempty and star-connected. |
| [sec5-window.tex:172](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:172) (`l:exact`; lines 172) | [sec2-moments.tex:297](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:297) | Yes. Only summed-out partition polynomials are transferred. Each integrated variable has at most four factors; fixed window letters and their actual frame weights remain in the reference window law. |
| [sec5-window.tex:176](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:176) (`l:finitefacts`; lines 176, 279, 298) | [sec2-moments.tex:126](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:126) | Yes. The networks have at most four incident factors. Inserted observables are included in the degree-four budget; free positivity is used only without pins, and conditional independence only on positive fibers at nonneighbors. |
| [sec5-window.tex:258](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:258) (`l:moments`; lines 258) | [sec2-moments.tex:35](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:35) | Yes. Every use is a polynomial calculation of separate degree at most four, including observables. Tight-frame products have degree four, and the Pauli/local formulas use the same U second/fourth and diluted D moments. |
| [sec5-window.tex:682](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:682) (`l:thicken`; lines 682) | [app-topology.tex:138](/home/ubuntu/aklt/manuscript-v2/app-topology.tex:138) | Yes. X0 is finite, nonempty, and star-connected, so its nearest-neighbor crosses form a connected cut. The ambient-distance weighted comparison has factor 5/theta for 0<theta<1. |
| [sec5-window.tex:163](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:163) (`l:threeframes`; lines 163) | [sec3-quantum-frames.tex:341](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:341) | Yes. The three rotations are antipodal unit-vector fourth-moment frames with weights 1/12 and exact bond bounds b..2-b for both signs; b=(5-sqrt(5))/505 and r_b=b/(2-b). |
| [sec5-window.tex:679](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:679) (`s:topology`; lines 679) | [app-topology.tex:2](/home/ubuntu/aklt/manuscript-v2/app-topology.tex:2) | Yes. Locator: Appendix B contains the exact star-boundary and cross-thickening lemmas invoked by the connected-cut proof. |
| [sec6-walks.tex:4](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:4) (`d:moment`; lines 4) | [sec2-moments.tex:8](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:8) | Yes. Finite U/D laws, separate degree at most four, ambient plane distances, and empty-product conventions agree; no surface integral or arbitrary-function rotation is imported. |
| [sec6-walks.tex:44](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:44) (`d:pinmodel`; lines 44) | [sec2-moments.tex:97](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:97) | Yes. Every use keeps the original G, original legs, and S(G). Pins are arbitrary unit vectors, and removal creates no pins; the ordinary U/X specialization has exactly these partition sums. |
| [sec6-walks.tex:340](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:340) (`l:35`; lines 340, 585, 599, 611) | [sec2-moments.tex:197](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:197) | Yes. Each conditional site has at most three incident factors with fields of norm at most one. The mean bound is 3/5 for U or D; the covering step uses the proved full ball of means from three unit fields. |
| [sec6-walks.tex:40](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:40) (`l:finitefacts`; lines 40, 275, 339, 358, 526, 647) | [sec2-moments.tex:126](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:126) | Yes. The networks have at most four incident factors. Inserted observables are included in the degree-four budget; free positivity is used only without pins, and conditional independence only on positive fibers at nonneighbors. |
| [sec6-walks.tex:121](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:121) (`l:moments`; lines 121) | [sec2-moments.tex:35](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:35) | Yes. Every use is a polynomial calculation of separate degree at most four, including observables. Tight-frame products have degree four, and the Pauli/local formulas use the same U second/fourth and diluted D moments. |
| [sec7-recursion.tex:8](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:8) (`d:domain`; lines 8) | [sec6-walks.tex:8](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:8) | Yes. Ordinary domains use full U kept sets, two-element D kept sets, consistency between nonremoved endpoints, the original protected layer, and no new leg factors. |
| [sec7-recursion.tex:5](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:5) (`d:moment`; lines 5) | [sec2-moments.tex:8](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:8) | Yes. Finite U/D laws, separate degree at most four, ambient plane distances, and empty-product conventions agree; no surface integral or arbitrary-function rotation is imported. |
| [sec7-recursion.tex:151](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:151) (`d:pattern`; lines 151, 222) | [sec6-walks.tex:488](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:488) | Yes. The covered template retains all twenty slots, both corner slots, full U kept sets except the passage, and covering U tips; effective-record reductions keep precisely its present factors. |
| [sec7-recursion.tex:6](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:6) (`d:pinmodel`; lines 6, 1041) | [sec2-moments.tex:97](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:97) | Yes. Every use keeps the original G, original legs, and S(G). Pins are arbitrary unit vectors, and removal creates no pins; the ordinary U/X specialization has exactly these partition sums. |
| [sec7-recursion.tex:17](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:17) (`d:ratios`; lines 17, 419, 426, 508, 797) | [sec6-walks.tex:240](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:240) | Yes. The ratios are post-step/pre-step partition sums: D departures have ratio one, and U departures use J/I with the correct one-, two-, or three-neighbor cases. Section 7 derives its canonical coefficients directly. |
| [sec7-recursion.tex:16](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:16) (`d:trace`; lines 16, 91, 176, 256, 829) | [sec6-walks.tex:50](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:50) | Yes. Starts are unpinned and outside S, with at most three U or one D present bonds; tracing drops both bond flags, retains original legs, and gives the stated mass-free coefficients and ratios. |
| [sec7-recursion.tex:653](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:653) (`d:weights`; lines 653) | [sec6-walks.tex:655](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:655) | Yes. The lattice revisit weight is exactly 1/5 and records earlier departures. The virtual incoming bond is unused, initial reversal is forbidden, and straight/turn weights are x_type/3. |
| [sec7-recursion.tex:11](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:11) (`h:H1`; lines 11) | [sec6-walks.tex:531](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:531) | Yes. The pointwise inequality is on the complete covered pattern class and every unit slot assignment, at the same thresholds 961/1000 and 187/200; no optimality assertion is consumed. |
| [sec7-recursion.tex:11](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:11) (`h:H2`; lines 11) | [sec6-walks.tex:684](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:684) | Yes. The import is the all-length open-trail sum, uniform over start and incoming direction, with C_V>=1 and 0<q<1. No stronger historical rate bound is required. |
| [sec7-recursion.tex:1035](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:1035) (`h:P`; lines 1035) | [sec2-moments.tex:338](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:338) | Yes. Uses concern finite G, arbitrary original unit pins, removed Y disjoint from S(G), and distance-two surviving pairs with a common removed neighbor. Distances remain to the original S(G). |
| [sec7-recursion.tex:464](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:464) (`l:35`; lines 464) | [sec2-moments.tex:197](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:197) | Yes. Each conditional site has at most three incident factors with fields of norm at most one. The mean bound is 3/5 for U or D; the covering step uses the proved full ball of means from three unit fields. |
| [sec7-recursion.tex:29](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:29) (`l:exposure`; lines 29, 778, 779) | [sec6-walks.tex:437](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:437) | Yes. The stopped trails have admissible starts, and x_type>=1 bounds each covered U ratio. The given fixed ordering is restricted to actual U departures before comparison with all lattice first visits. |
| [sec7-recursion.tex:56](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:56) (`l:finitefacts`; lines 56, 457, 464) | [sec2-moments.tex:126](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:126) | Yes. The networks have at most four incident factors. Inserted observables are included in the degree-four budget; free positivity is used only without pins, and conditional independence only on positive fibers at nonneighbors. |
| [sec7-recursion.tex:26](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:26) (`l:local`; lines 26, 155, 223, 422, 769) | [sec6-walks.tex:546](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:546) | Yes. Closure provides the covered non-tip template at each invoked U departure. The lemma explicitly allows arbitrary original pins, outside fields of norm <=1, missing factors, both corner slots, and the actual ordinary tip data. |
| [sec7-recursion.tex:31](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:31) (`l:onepoint`; lines 31, 180, 242, 883, 903) | [sec6-walks.tex:695](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:695) | Yes. When the estimate is applied, H1/H2 hold, the incoming bond is absent, starts are admissible, and there are at most twelve uncovered U departures anywhere along the trail. The maximum over the two pin ratios is taken before summation. |
| [sec7-recursion.tex:398](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:398) (`l:response`; lines 398, 441) | [sec6-walks.tex:286](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:286) | Yes. The untyped response identity uses the same positive logarithmic-mean coefficients, zero D response, free ratio <=1, and pinned ratio <=12/5. The refined coefficient choice is explicitly derived in Section 7. |
| [sec7-recursion.tex:20](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:20) (`p:pairwalk`; lines 20, 185, 204, 726, 753, 871) | [sec6-walks.tex:148](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:148) | Yes. Both starts meet the U<=3/D<=1 bounds. The first target has the required degree, and the second protected target e has already lost its first arrival bond. The second stopping set is S union {e}=S; target constants and degree-four insertions match. |
| [sec8-inputs.tex:260](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:260) (`c:reduce`; lines 260) | [app-local-operator.tex:172](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:172) | Yes. The chosen allowed representation has a common positive leaf factor; Pauli positivity supplies the sphere/ball positivity needed to recover every original twenty-slot assignment. |
| [sec8-inputs.tex:322](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:322) (`d:kernel`; lines 322) | [sec7-recursion.tex:517](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:517) | Yes. The consumer uses center-avoiding first-hit trails, departure-based revisits, the same live/dead rule, mass-free coefficients, pair types, and shifts. Short/long ordering choices remain those of d:kernel-order. |
| [sec8-inputs.tex:280](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:280) (`d:kernel-order`; lines 280, 324) | [sec7-recursion.tex:572](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:572) | Yes. The exact dyadic h, rho0, cutoff 12, short rational sorting with index ties, and long straight-before-turn ordering agree. Phase formulas are used for long continuations, with short sums evaluated separately. |
| [sec8-inputs.tex:31](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:31) (`d:pattern`; lines 31, 167) | [sec6-walks.tex:488](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:488) | Yes. The covered template retains all twenty slots, both corner slots, full U kept sets except the passage, and covering U tips; effective-record reductions keep precisely its present factors. |
| [sec8-inputs.tex:289](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:289) (`h:H1`; lines 289) | [sec6-walks.tex:531](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:531) | Yes. The pointwise inequality is on the complete covered pattern class and every unit slot assignment, at the same thresholds 961/1000 and 187/200; no optimality assertion is consumed. |
| [sec8-inputs.tex:297](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:297) (`h:H2`; lines 297) | [sec6-walks.tex:684](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:684) | Yes. The import is the all-length open-trail sum, uniform over start and incoming direction, with C_V>=1 and 0<q<1. No stronger historical rate bound is required. |
| [sec8-inputs.tex:306](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:306) (`h:H3`; lines 306) | [sec7-recursion.tex:594](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:594) | Yes. The imported assertion bounds every finite cutoff of the specified type-dependent kernel by rho0*h. The same exact positive vector and fixed orderings are used. |
| [sec8-inputs.tex:296](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:296) (`l:H2-CV`; lines 296) | [app-input-contracts.tex:275](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:275) | Yes. The consumer uses precisely m=6 and q=q_* from p:H2-test; the finite-base bound permits the same explicit C_V=10. |
| [sec8-inputs.tex:78](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:78) (`l:Iw`; lines 78, 210) | [app-local-operator.tex:24](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:24) | Yes. Passage integration yields Zcur=Zw[I] and Znext=Zw[J] with removed neighbors set to zero. Every pair insertion replaces a lost passage bond, maintaining separate degree four. |
| [sec8-inputs.tex:249](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:249) (`l:Ostruct`; lines 249, 254) | [app-local-operator.tex:320](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:320) | Yes. The inversion is checked to be a union of groups. The resulting real symmetric operator has the required spin commutators, symmetric U-pair support, and D-pair exchange decomposition. |
| [sec8-inputs.tex:295](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:295) (`l:alm`; lines 295) | [app-input-contracts.tex:66](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:66) | Yes. The positive m=6 vector satisfies the regenerated one-step inequality with 0<q<1; the maximum over finite bases is included, giving the uniform all-length H2 conclusion. |
| [sec8-inputs.tex:216](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:216) (`l:gram-residual`; lines 216) | [app-local-operator.tex:527](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:527) | Yes. The matrices are regenerated symmetric integer forms and g,d,S are positive. Every residual row is checked; strict dominance implies positive diagonal. L=0 is allowed, and no invertibility is assumed. |
| [sec8-inputs.tex:18](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:18) (`l:integercheck`; lines 18, 85, 211, 224, 237, 248) | [app-local-operator.tex:582](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:582) | Yes. The thresholds lie in (0,1), D0 is justified and positive, and sector bases are the unnormalized integer-coordinate bases. The scale is 15*D0*q. Bareiss is invoked only with exact divisions and positive pivots, including the proved positive-common-scalar reduction. |
| [sec8-inputs.tex:258](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:258) (`l:inversion`; lines 258) | [app-local-operator.tex:271](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:271) | Yes. One checked groupwise inversion has a positive semidefinite Pauli operator; the product density trace identity then gives polynomial positivity on closed unit balls and hence all unit slots. |
| [sec8-inputs.tex:66](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:66) (`l:leaf`; lines 66, 178, 209) | [app-local-operator.tex:89](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:89) | Yes. The retained leaf data satisfy the covered-template hypotheses: bonded-tip radius 3/5, reduced one-bond corner radius 1/2 or 1/3, and positive common factors for isolated leaves. |
| [sec8-inputs.tex:279](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:279) (`l:log-mean-bounds`; lines 279) | [sec7-recursion.tex:260](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:260) | Yes. The same rational type table is used, including turning a_t=150000/10^6 and bprime_type<=b_type. Appendix C ceilings reconstruct these exact fractions with the exact dyadic h_C. |
| [sec8-inputs.tex:77](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:77) (`l:moments`; lines 77, 210) | [sec2-moments.tex:35](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:35) | Yes. Every use is a polynomial calculation of separate degree at most four, including observables. Tight-frame products have degree four, and the Pauli/local formulas use the same U second/fourth and diluted D moments. |
| [sec8-inputs.tex:251](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:251) (`l:sector`; lines 251) | [app-local-operator.tex:472](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:472) | Yes. The supported tensor-sector operators are Hermitian, preserve the sectors, and commute with all three spin generators. The central weight uses the parity of the singles, so positivity extends to exactly those full supported sectors. |
| [sec8-inputs.tex:304](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:304) (`l:stationary-assembly`; lines 304) | [app-input-contracts.tex:1175](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:1175) | Yes. Its exact five prefix ceilings give the stated B/C row bounds with the same dyadic h_C and rho0=993015/10^6, uniformly in the true-trail cutoff; this is exactly H3_h. |
| [sec8-inputs.tex:293](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:293) (`p:H2-test`; lines 293) | [app-input-contracts.tex:199](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:199) | Yes. The integer vector is on the same memory-six automaton and thresholds. Its positive row test has common denominator 2695605 and exactly the rational q_* consumed by H2 and the recursion. |
| [sec8-inputs.tex:300](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:300) (`p:automaton10`; lines 300) | [app-input-contracts.tex:367](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:367) | Yes. The imported raw/quotient reconstruction has 60092 windows and 3741 classes, absolute direction labels, and the required final-direction condition for non-revisit transitions; no spatial symmetry or class-size factor is assumed. |
| [sec8-inputs.tex:301](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:301) (`p:stationary-check`; lines 301) | [app-input-contracts.tex:1069](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:1069) | Yes. The same five cases, memory 10, prefix 12>=10+2, radius 70, value scale 2^16, coefficient scale 2^48, and exact prefix upper bounds are used. All rows, caps, terminal values, and array indices remain required. |

## Every edit to a section file

Locations below are the final assembled file's starting line and the corresponding source starting line. Before/after blocks are exact differing lines. Comments were replaced with blank lines, preserving their source line positions before other edits. All eight source comment lines were removed; none remain in main.tex or any section. The new first paragraph is expressly authorized by the task. All other prose edits remove history of prior methods or certificate preparation and leave the present mathematical conditions intact.

### E1: [sec1-result.tex:3](/home/ubuntu/aklt/manuscript-v2/sec1-result.tex:3)

Source: `sec1-result.tex:3`. Before:

```tex
We study the spin-\(2\) AKLT Hamiltonian on the square-lattice torus.
The polynomial realization of the spin space, including its Hilbert
space normalization, is fixed in Definition~\ref{d:poly}.
```

After:

```tex
We study the spin-\(2\) square-lattice AKLT model of Affleck, Kennedy,
Lieb, and Tasaki~\cite{AKLT88,KLT88}. We prove uniqueness of its ground
state on every torus with integer periods \(L,N\ge3\) and a uniform
positive spectral gap for all integers \(L,N\ge L_0\), with no parity
restriction, for one fixed threshold \(L_0\). The computational inputs
are local operator inequalities, an open-trail growth bound, and a
type-dependent positive-vector bound obtained from stationary Bellman
inequalities and finite prefix sums. All computations are checked in
exact arithmetic. The polynomial realization of the spin space,
including its Hilbert space normalization, is fixed in
Definition~\ref{d:poly}.
```

### E2: [sec4-periodic-gap.tex:402](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:402)

Source: `sec4-periodic-gap.tex:402`. Before:

```tex
% Same-lane results l:colour, l:boxlift, l:star, t:QD and p:toruskernel
% are stated and proved in sec3-quantum-frames.tex, as assigned by PLAN.md.
```

After: 2 blank line(s).

### E3: [sec4-periodic-gap.tex:530](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:530)

Source: `sec4-periodic-gap.tex:530`. Before:

```tex
% Theorem t:main is stated in sec1-result.tex; its final assembly is below.
```

After: 1 blank line(s).

### E4: [sec7-recursion.tex:168](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:168)

Source: `sec7-recursion.tex:168`. Before:

```tex
% Deviation from the registry: v must be outside S for the second start.
```

After: 1 blank line(s).

### E5: [sec7-recursion.tex:552](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:552)

Source: `sec7-recursion.tex:552`. Before:

```tex
trace coefficients. This \(M\) is the modified type-dependent kernel,
not the original uniform-coefficient matrix.
```

After:

```tex
trace coefficients. This \(M\) is the type-dependent response kernel.
```

### E6: [sec7-recursion.tex:606](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:606)

Source: `sec7-recursion.tex:607`. Before:

```tex
No bound for the former uniform-coefficient matrix is part of this
contract. Its proof in this revision uses the stationary lattice
Bellman certificates, with no periodic spatial walk or remainder.
```

After:

```tex
The assertion is proved using the stationary lattice Bellman
certificates, with no periodic spatial walk or remainder.
```

### E7: [sec8-inputs.tex:1](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:1)

Source: `sec8-inputs.tex:1`. Before:

```tex
%% REV_C2: section file; no preamble or document environment.
```

After: 1 blank line(s).

### E8: [sec8-inputs.tex:19](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:19)

Source: `sec8-inputs.tex:19`. Before:

```tex
complete local input can be specified with the supplied data,
without finding any new inversion or Gram factor.
```

After:

```tex
complete local input is specified by the supplied data.
```

### E9: [sec8-inputs.tex:316](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:316)

Source: `sec8-inputs.tex:317`. Before:

```tex
exact and every pivot positive. The full nonzero Gram-factor
family was not retained by the feasibility study; the stated
fallback discharges exactly the blocks lacking those factors.
No new representation, inversion or factor search is needed.
```

After:

```tex
exact and every pivot positive. The fallback discharges exactly
the blocks without supplied nonzero Gram factors, using the fixed
representation and inversion records.
```

### E10: [app-input-contracts.tex:1](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:1)

Source: `app-input-contracts.tex:1`. Before:

```tex
%% REV_C2: section file; no preamble or document environment.
```

After: 1 blank line(s).

### E11: [app-input-contracts.tex:1185](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:1185)

Source: `app-input-contracts.tex:1185`. Before:

```tex
therefore (H3\(_h\)) holds for the modified kernel.
```

After:

```tex
therefore (H3\(_h\)) holds for the type-dependent kernel.
```

### E12: [app-local-operator.tex:1](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:1)

Source: `app-local-operator.tex:1`. Before:

```tex
% Appendix D.  Statement text follows the amended REV-PLAN contract.
% This is a section file: no document class, packages, or theorem declarations.
```

After: 2 blank line(s).

The unchanged section files are sec2-moments.tex, sec3-quantum-frames.tex, sec5-window.tex, sec6-walks.tex, app-finite.tex, and app-topology.tex. The retained source repairs M1--M3 are already present in those inputs and are not assembly edits. A full reproducible patch is provided in [section-edits.patch](section-edits.patch).

## Validation details

The static audit checks every label/reference/citation, all twelve input paths, the bibliography subset, the complete plan inventory, comments, and editorial-language candidates. Exact interface checks independently confirm the H2 rate and finite-base majorant, all typed coefficient majorants, the H2 denominator/numerators, the five H3 prefix-ceiling assembly inequalities, the dyadic witness, coefficient ceilings, phase common denominator, shared shell threshold, memory/prefix condition, supported-block coverage count, and the periodic-to-quantum factor 499/1000. These are assembly checks, not a new exhaustive certificate proof.

The final PDF text was checked for the title, both theorem size ranges, all section/appendix headings, and both cited bibliography entries. The final TeX log has no unresolved citations/references, multiply defined labels, TeX errors, or overfull/underfull boxes. The source-preservation check verifies every original section hash and every mathematical statement against the delivered source. The generated report contains a review row for every cross-file use group and an edit record for every source-to-assembly difference.

## ORCH-SUMMARY

STATUS: COMPLETE
Paper: /home/ubuntu/aklt/manuscript-v2/main.tex
PDF: /home/ubuntu/aklt/manuscript-v2/main.pdf (82 pages)
Title unchanged; new abstract and short introductory first paragraph.
Uniqueness: all integers L,N>=3; uniform gap: all integers L,N>=L0, any parity.
Twelve section files appear in the prescribed order.
Bibliography contains exactly the two cited supplied entries.
105 planned statements and 137 unique labels are present.
353 references resolve; 182 cross-file occurrences reviewed in 103 groups.
Retained source repairs: nonexceptional shell clearance and v not in S.
Retained method clarification: exact Bareiss fallback where Gram factors are absent.
No additional mathematical mismatch or mathematical edit was needed.
Eight comment lines removed; editorial history stripped.
All 12 section edit blocks are recorded with exact before/after text.
42 assembly/exact-interface checks passed; original section hashes unchanged.
latexmk -pdf succeeded with zero undefined references and no final warnings.
No exhaustive certificate rerun or completed Lean verification is claimed.
Git initialized with metadata in .git-metadata because managed .git is read-only.
No commit, input-directory writes, or sub-agents.
