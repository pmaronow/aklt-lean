RESULT: NO VIOLATION FOUND

All 38 model inequalities passed the independent exact checks. No target inequality, required mean bound, retained field ball, or reduction identity failed in the sampled actual-passage class. Independent enumeration reproduces the 7,962 catalogue classes, 20 nontrivial reduced geometries and 38 maximal radius boxes.

This result concerns the replacement stated in MATH_FIT: unpinned D sites with at most two kept bonds and actual external factors. The original paper also defines a larger, artificially filled-slot H1 input. I tested that larger input numerically, extending its slot vectors to balls by affinity, but the 38-model reduction does not assert coverage of all of its filled D slots. The distinction is exhibited explicitly below.

Models are numbered by their zero-based position in `cores_universal_final.json`; `pid` is provenance, not a model definition, and can repeat. In the table, s means c = 961/1000, t means c = 187/200, and margin is the minimum ratio found minus that c. Ratios are rounded to twelve decimals. The certificate column reports my exact check and the reconstructed central-sector size.

| Model | Type | pid | Minimum Zcur/Znext found | Margin to c | Exact certificate verified |
|---:|:---:|---:|---:|---:|:---|
| 00 | t | 1414 | 1.000000000000 | +0.065000000000 | yes; scalar |
| 01 | t | 1458 | 0.942237526783 | +0.007237526783 | yes; scalar |
| 02 | t | 4868 | 0.942237526783 | +0.007237526783 | yes; scalar |
| 03 | t | 5469 | 0.935771068758 | +0.000771068758 | yes; scalar |
| 04 | t | 548 | 1.000000000000 | +0.065000000000 | yes; scalar |
| 05 | t | 1349 | 0.995411644571 | +0.060411644571 | yes; 14 × 14 |
| 06 | t | 1125 | 0.970582575113 | +0.035582575113 | yes; scalar |
| 07 | t | 1342 | 0.943997317237 | +0.008997317237 | yes; scalar |
| 08 | t | 5287 | 0.937410229963 | +0.002410229963 | yes; scalar |
| 09 | t | 1904 | 0.991373400157 | +0.056373400157 | yes; scalar |
| 10 | t | 5906 | 0.991163616765 | +0.056163616765 | yes; scalar |
| 11 | t | 5907 | 0.984657647852 | +0.049657647852 | yes; scalar |
| 12 | t | 1306 | 0.977178925258 | +0.042178925258 | yes; 7 × 7 |
| 13 | t | 1341 | 0.982529178232 | +0.047529178232 | yes; 25 × 25 |
| 14 | t | 1342 | 0.967553202773 | +0.032553202773 | yes; 14 × 14 |
| 15 | t | 5908 | 0.998159591158 | +0.063159591158 | yes; 14 × 14 |
| 16 | t | 1126 | 0.972358943588 | +0.037358943588 | yes; 25 × 25 |
| 17 | t | 1307 | 0.935969335823 | +0.000969335823 | yes; 7 × 7 |
| 18 | t | 1342 | 0.935361473979 | +0.000361473979 | yes; 14 × 14 |
| 19 | t | 1342 | 0.952102625727 | +0.017102625727 | yes; 66 × 66 |
| 20 | t | 5441 | 0.937706979581 | +0.002706979581 | yes; 36 × 36 |
| 21 | s | 6904 | 1.000000000000 | +0.039000000000 | yes; scalar |
| 22 | s | 3507 | 0.978198017915 | +0.017198017915 | yes; scalar |
| 23 | s | 3609 | 0.978709003750 | +0.017709003750 | yes; scalar |
| 24 | s | 3628 | 0.962506966611 | +0.001506966611 | yes; scalar |
| 25 | s | 2838 | 1.000000000000 | +0.039000000000 | yes; scalar |
| 26 | s | 3628 | 0.995411644571 | +0.034411644571 | yes; 14 × 14 |
| 27 | s | 3638 | 0.977020198011 | +0.016020198011 | yes; scalar |
| 28 | s | 7111 | 0.980626036836 | +0.019626036836 | yes; scalar |
| 29 | s | 3499 | 0.964382500968 | +0.003382500968 | yes; scalar |
| 30 | s | 3500 | 0.962441314554 | +0.001441314554 | yes; scalar |
| 31 | s | 3596 | 0.971911491145 | +0.010911491145 | yes; scalar |
| 32 | s | 3621 | 0.966268708142 | +0.005268708142 | yes; scalar |
| 33 | s | 3500 | 0.983397142855 | +0.022397142855 | yes; 25 × 25 |
| 34 | s | 3621 | 0.978404899733 | +0.017404899733 | yes; 14 × 14 |
| 35 | s | 7766 | 0.997827486471 | +0.036827486471 | yes; 7 × 7 |
| 36 | s | 3621 | 0.995558391911 | +0.034558391911 | yes; 66 × 66 |
| 37 | s | 7766 | 0.977885943793 | +0.016885943793 | yes; 36 × 36 |

The search evaluated 622,592 random field configurations, 2,508 perturbed collinear seeds, and 19,456 BFGS starts: 16,384 random configurations and 512 local starts per model. Half the local starts came from the lowest sampled values and half were fresh random starts. The maximum was 350 iterations per local run. There were 18,248,269 double-precision objective evaluations; 7,017 local runs returned an optimizer success flag. The other runs still contributed their evaluated iterates. These are minima found, not claims of globally optimal ratios.

For each literal model I sum the twelve icosahedral U spins and the additional zero D spin with probabilities 1/12, or 1/20 and 2/5. A deterministic m vertex is its listed-radius vector, without a spin integration. Independent path transfer matrices compute Z and inserted Cij; I then use Zcur = Z + sum(Cij)/3 and Znext = Z + Cfg/5 when two non-outgoing marks remain. Missing marks contribute zero. This implements the model description without consulting pattern IDs. [The search results and all best field directions](/home/ubuntu/aklt/reports/H1TREE_NUM/data/model_search.json) retain Z, Zcur and Znext. [The independent 80-digit reevaluations](/home/ubuntu/aklt/reports/H1TREE_NUM/data/cross_checks.json) also retain every Cij. Their ratios agree with the double-precision results and a separate four-state moment contraction to within 2.22e-16. Random common rotations, 32 per model, changed ratios by at most 2.22e-16.

The closest model is 18. Every nonzero path field can be +e3 and its isolated outgoing mean can be −(5/14)e3. Exact integration gives Z = 244/125, Zcur = 674668/354375 and Znext = 171736/84375. Thus its ratio is 843335/901614 = 0.935361473978887 and its margin is 32591/90161400 = 0.000361473978886752. [The complete exact configuration](/home/ubuntu/aklt/reports/H1TREE_NUM/data/near_threshold_witness.json) is saved. This is an explicit admissible model configuration, not a counterexample or a proof that the minimum is attained there.

The exact checker uses Python integers, rational numbers, and integer pairs for Gaussian integers; its checking arithmetic has no floating-point matrix decisions. It first verifies all 35 monomials of degree at most four directly from the stated icosahedral coordinates. It also checks the polynomial identity behind the 3/5 three-unit-field mean bound, the orthogonal-decomposition identity for the special two-unit-field bound, and the arrival and D-mixture moment identities. [These definition checks](/home/ubuntu/aklt/reports/H1TREE_NUM/data/definition_identities.json) all pass.

For the 21 listed ordinary mean triples I reconstruct the numerator norm from its 3 × 3 Gram matrix, form the stated gap polynomial, transform it to the tensor Bernstein basis, compare all 567 rational coefficients with the supplied coefficients, and check nonnegativity. All coefficients match; the largest numerator or denominator has 53 bits. All three special `mean_unit_pair.json` cases, including r = 1/25, pass their degree-four check. There are 25 distinct coefficients per special case. The supplied `nonzero = 115` metadata counts five copies along an unused third axis; my 23 nonzero coefficients per case reproduce that number. There is no coefficient discrepancy. [Exact mean results](/home/ubuntu/aklt/reports/H1TREE_NUM/data/exact_means.json) include the reconstructed coefficients. My graph simplifications also encounter some sharper triples; all 62 encountered records pass an additional 1,664 exact coefficient comparisons, recorded in [the derived-mean checks](/home/ubuntu/aklt/reports/H1TREE_NUM/data/derived_mean_checks.json).

For each of the 22 scalar cases I independently compute ro, rf, rg, L, the coefficients of Q, its endpoint tests and its interior vertex test when applicable. All supplied radii, Q coefficients and tests match and are nonnegative. For the other 16 cases I reconstruct each Pauli-form matrix entry directly: build the local external Pauli matrix-element polynomial, integrate it using exact spin moments, and contract four-state bond messages. The basis is the unnormalized symmetric basis for two unit fields at a U vertex, singles otherwise, restricted to the central weight. Inversion indices use ring order with zero-radius fields removed. An isolated m vertex is encoded algebraically by a U field of 3R; its degree-one moment is exactly the deterministic mean R, so this imposes no physical field-radius assumption.

After removing a checked positive common scalar, every reconstructed matrix agrees entry by entry with the supplied normalized matrix. I use my reconstructed matrix for every residual calculation. All 16 integer factors are lower triangular, and every row of E = den·S²·M − L Lᵀ is strictly diagonally dominant with positive diagonal. All listed residual minima match. The sizes give 14,502 matrix entries, 7,443 triangular factor entries, 129,491 Gram products and largest dimension 66. This verifies the listed finite model certificates using the paper’s Pauli-sector and Bernstein implications; it is not a new Lean kernel check. [Per-model exact results](/home/ubuntu/aklt/reports/H1TREE_NUM/data/exact_checks.json) and files `data/matrix_05.json`, etc., contain the reconstructed matrices, positive physical-form scales and every residual row margin.

The geometry enumeration starts from the kept-set choices in the paper, independently of the catalogue. It imposes mutual keep decisions only between nonremoved, non-tip sites, marks each allowed outgoing neighbour, removes isolated common factors, and canonicalizes reflection. The catalogue is used afterward to compare keys and attach its pid labels. The counts are:

| Enumeration quantity | Independently obtained |
|---|---:|
| Consistent status/kept-set assignments | 106,101 |
| Marked outgoing choices | 184,914 |
| N/E outgoing choices | 123,339 |
| Effective reflection classes | 7,962 |
| Missing or extra catalogue keys | 0 |
| Convex reduction branches | 24,741 |
| Nonempty branches contained in a listed radius box | 23,760 |
| Empty, direct Zcur = Znext branches | 981 |
| Nontrivial reduced geometries | 20 |
| Distinct radius boxes before domination | 3,534 |
| Maximal radius boxes | 38 |
| Listed boxes missing from the independent regeneration | 0 |
| Additional maximal boxes | 0 |

The graph rewrites integrate leaves, retain the lower five-vertex correlation when required, expand a two-bond upper D kernel or a remaining D neighbour with weights 3/5 and 2/5, integrate isolated marked vertices, pad zero fields, identify paths preserving both kinds of marks, and compare radius boxes under all such isomorphisms. Domination is checked in exact rational arithmetic; it means containment of field balls, not a claim that a ratio is monotone in a radius. The 981 empty branches are not separate entries in the list: their inequality is immediate, or they can be padded by a zero deterministic marked vertex in model 00 or 25. No nonempty branch is uncovered. [The enumeration](/home/ubuntu/aklt/reports/H1TREE_NUM/data/enumeration.json), [geometry audit](/home/ubuntu/aklt/reports/H1TREE_NUM/data/geometry_audit.json) and [coverage for every pid](/home/ubuntu/aklt/reports/H1TREE_NUM/data/coverage_by_pattern.json) record these results.

A necessary ordering interpretation is that zero-spin terms are chosen before deciding whether to cut or preserve the lower path. For example, catalogue pid 7766 has a D outgoing N; choosing its zero term removes N and exposes the lower correlated path represented by model 37. Likewise, zero E/W terms permit sharper one-sided leaf bounds. The operations commute as integrations and positive decompositions, so this order is available. Cutting all lower connections according to the original pre-decomposition presence of N would lose information and would not regenerate the stated 38 boxes. The report’s prose must be read with this adaptive ordering.

I tested two catalogue slot interpretations and a separate set of passages generated directly by the paper’s trace:

| Sampling family | Passages/patterns | Configurations each | Total target tests | Smallest ratio | Smallest margin to its own c | Violations |
|---|---:|---:|---:|---:|---:|---:|
| Catalogue, actual-slot capacity | 7,962 | 128 | 1,019,136 | 0.952151064758 | 0.010509971510 | 0 |
| Catalogue, paper’s filled-slot class | 7,962 | 64 | 509,568 | 0.954747474747 | 0.001506966611 | 0 |
| Actual stopped-trail U departures | 8,192 | 32 | 262,144 | 0.978314643064 | 0.027049524174 | 0 |

The minimum ratio and minimum margin in a row can occur at different passage types. Catalogue actual-slot tests give U corners two slots and D corners at most 2 − k, with k present internal bonds. The configurations include independent unit directions, shared conditioned outside spins, shortened or missing factors, and collinear signs. Tips include U, D and removed cases; D tips have at most one external factor when attached. Every convex branch is checked for each of the 128 configurations, with random auxiliary directions on cut fibres. These catalogue tests are an overapproximation of actual outside configurations, not a claim that every independently assigned field configuration is a complete global trace.

The direct sampler starts U/X domains on G = [−12,12]², with original protected boundary S unchanged, and follows admissible bond-deleting trails until their first hit of S. It captured 8,192 U departures from 398 trails (9198 traversed steps), including 2,768 straight and 5,424 turning departures, and 792 distinct catalogue classes. Actual tip laws, kept sets and missing factors are retained. Spins shared by external bonds are assigned once per outside site from their actual U/D support; a common hemisphere avoids antipodal outside bonds. Original leg pins are independent arbitrary unit vectors. There were 23,904 sampled original-pin field incidences and 3,510,592 outside-spin field incidences. All captured normalized local geometries occur in the catalogue. [The generated passage records](/home/ubuntu/aklt/reports/H1TREE_NUM/data/actual_passages.jsonl) retain their statuses, kept masks, leg requests and outgoing directions.

Intermediate checks use finite quadrature rather than the mean formulas being tested. The check counts are:

| Check | Catalogue run | Direct-trail run | Failures |
|---|---:|---:|---:|
| Required mean-ball comparisons | 10,816,512 | 1,655,104 | 0 |
| Final retained field-ball comparisons | 8,751,616 | 2,182,144 | 0 |
| Integrated-leaf identities on all 13 parent support points | 36,328,448 | 7,601,152 | 0 |
| Current/next D-mixture identities | 4,295,424 | 116,864 | 0 |
| Direct passage-spin integration versus I/J identities | 15,924 | 16,384 | 0 |
| Current/next auxiliary-cut quadrature identities | 1,336 | 2,870 | 0 |
| Random auxiliary fibres tested | 85,504 | 45,920 | 0 |
| Final convex-branch target inequalities | 3,166,848 | 320,576 | 0 |
| Nonempty branch mappings outside the listed balls | 0 | 0 | 0 |

Passage I/J identities use the first configuration of every pattern/passage and sum the departure spin directly. Each auxiliary-cut identity uses all 12 auxiliary quadrature nodes for its first configuration, including the two lower-corner normalizers; conditional means are tested separately on all sampled fibres. Leaf identities are checked pointwise on all 13 parent spins. D-mixture identities compare both unnormalized partition functions on every sampled configuration. All removed normalizers are common positive factors; the smallest encountered one was 0.500056460051. The largest numerical identity defect was 1.33e-15 (absolute for leaf factors, relative to max(1,|value|) for partition identities). The largest mean or field-radius excess was 2.22e-16, consistent with rounding. A numerical failure threshold of 2 × 10⁻¹² was used. The smallest final branch margins were 0.004060580445 and 0.024256636522. [Catalogue numerical results](/home/ubuntu/aklt/reports/H1TREE_NUM/data/passage_checks.json) and [direct-trail results](/home/ubuntu/aklt/reports/H1TREE_NUM/data/actual_trace_checks.json) include counts by mean triple, model hit counts and complete worst-ratio local configurations.

The scope boundary has a simple explicit example. In catalogue pid 0 the D corner (1,−1) is a leaf attached to (1,0). In the paper’s filled class give both of its artificial slots the field e3. Its slot normalizer is 6/5 and its unnormalized mean is (2/5)e3, so its effective field is (1/3)e3. This exceeds the actual D-leaf radius 1/5 by 2/15. Such a D leaf has room for only one actual external factor, whose mean radius is at most 1/5. Thus applying the actual-slot reduction unchanged to the filled class would fail this intermediate radius claim. This is outside the replacement’s stated premise and does not violate its inequalities; pid 0 itself has Zcur/Znext = 1. [The exact scope example](/home/ubuntu/aklt/reports/H1TREE_NUM/data/scope_example.json) is saved. The 509,568 filled-class target tests found no target violation, but they do not turn the 38-model replacement into a certificate of the original larger H1 statement.

No listed certificate was left uninterpreted. Continuous passage fields are sampled rather than exhaustively searched, and the generated histories are first stopped trails. Exceptional second-trace departures outside the covered-template premise retain the paper’s existing exceptional estimate and were not claimed to be certified by these 38 models. Exhaustiveness here applies to the finite kept-set/radius-box enumeration and the exact listed arithmetic, not to an enumeration of every possible global trace history.

All programs and generated artifacts are under H1TREE_NUM. Supplied programs were inspected for slot order, unnormalized basis conventions, inversion indices and witness scales; none was imported, executed, or reused as a checking implementation. The exact matrix check uses direct local matrix-element integration, the model search uses finite-spin path transfers, and passage checks use a separate numerical four-state factorization. Source hashes, program hashes and dependency versions are in [provenance.json](/home/ubuntu/aklt/reports/H1TREE_NUM/data/provenance.json). The source prose report was edited during this run; [a saved snapshot](/home/ubuntu/aklt/reports/H1TREE_NUM/data/claim_report_snapshot.txt) records the H1 statement and decoder checked here. The five numerical inputs retain their hashes from initial inspection. Search, catalogue and direct-trail RNG seeds are 20261116, 20261117 and 20261118. CPU workers were capped at eight, with one BLAS thread each. The largest per-process RSS reported by the timed runs was 262,948 KiB; arrays and worker counts stayed well below the 30 GB limit.

To reproduce with the installed local dependencies, run:

```bash
cd /home/ubuntu/aklt/reports/H1TREE_NUM
bash programs/run_all.sh
```

The entry points are [model_search.py](/home/ubuntu/aklt/reports/H1TREE_NUM/programs/model_search.py), [exact_check.py](/home/ubuntu/aklt/reports/H1TREE_NUM/programs/exact_check.py), [geometry.py](/home/ubuntu/aklt/reports/H1TREE_NUM/programs/geometry.py), [passage_check.py](/home/ubuntu/aklt/reports/H1TREE_NUM/programs/passage_check.py) and [actual_traces.py](/home/ubuntu/aklt/reports/H1TREE_NUM/programs/actual_traces.py). The full dependency versions are recorded, and `deps/` contains the packages used. Logs preserve each completed run and the timed resource measurements.
