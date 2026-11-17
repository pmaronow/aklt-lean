"""Assemble the report from completed checks; refuse a false clean result."""
import hashlib, platform
from fractions import Fraction as F
from common import *

def read(name):return json.loads((ROOT/'data'/name).read_text())
search=read('model_search.json');exact=read('exact_checks.json');means=read('exact_means.json')
enumeration=read('enumeration.json');geometry=read('geometry_audit.json')
catalogue=read('passage_checks.json');actual=read('actual_trace_checks.json')
derived=read('derived_mean_checks.json');identities=read('definition_identities.json')
cross=read('cross_checks.json');near=read('near_threshold_witness.json')
assert len(search)==len(exact['models'])==38
assert all(r['verified'] for r in exact['models'])
assert exact['ordinary_means_verified'] and exact['special_means_verified']
assert not derived['failures'] and not identities['moment_failures'] and cross['verified']
assert all(identities[k] for k in ['three_unit_mean_identity','unit_pair_norm_identity','arrival_auxiliary_second_moment','D_mixture_nonzero_weight','top_D_kernel_weight'])
assert geometry['maximal_radius_boxes']==38 and geometry['geometries']==20
assert geometry['uncovered_branches']==0 and not geometry['extra_maximal_boxes'] and not geometry['listed_boxes_not_regenerated']
assert enumeration['missing_from_catalogue']==enumeration['extra_in_catalogue']==0
for d in (catalogue,actual):
    assert all(d[k]==0 for k in ['mean_failures','original_failures','covered_failures','mapping_failures','final_failures','field_ball_failures'])
    assert d['min_normalizer']>0
    assert all(d[k]<2e-12 for k in ['max_leaf_identity_error','max_decomposition_error','max_passage_identity_error','max_cut_identity_error','largest_mean_excess','maximum_field_excess'])
assert not actual['generation']['uncovered'] and min(r['margin'] for r in search)>0

claim_bytes=(SOURCE/'report.md').read_bytes()
(ROOT/'data/claim_report_snapshot.txt').write_bytes(claim_bytes)
paths=[SOURCE/'data'/n for n in ['cores_universal_final.json','universal_certificates.jsonl','universal_mean_checks.json','mean_unit_pair.json','universal_exact_summary.json']]
paths += [CATALOGUE]+[Path('/home/ubuntu/aklt/manuscript-v2')/n for n in ['sec2-moments.tex','sec6-walks.tex','sec8-inputs.tex','app-input-contracts.tex','app-local-operator.tex']]
provenance=dict(inputs=[dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths],
                programs=[dict(path=str(p.relative_to(ROOT)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted(list((ROOT/'programs').glob('*.py'))+list((ROOT/'programs').glob('*.sh')))],
                python=platform.python_version(),dependencies={})
provenance['claim_report']=dict(source_path=str(SOURCE/'report.md'),snapshot_path='data/claim_report_snapshot.txt',sha256=hashlib.sha256(claim_bytes).hexdigest())
initial_hashes={
    'cores_universal_final.json':'5fc87b2effda9fcd0fec8de3c841b680ae0f26434836ddd3c95663bab4d801ef',
    'universal_certificates.jsonl':'1cd6b2a04b76e8abd484b68fc7b5fcd85a6459df636dd909446a40854e3b7f49',
    'universal_mean_checks.json':'06cbdc5f86f8d2bc1b99218a17ffd56064ceceea3ee048df170b27bb6e7d4a55',
    'mean_unit_pair.json':'349387a476153bc7cf796d065c593d48fa1cbf8f8a2288795f58fac53295b58a',
    'pext7962.json':'fd0866f455505e2cd6317f4a5cc4ec45a1f7d6ed5816786cb6500c3b773caba2'}
for p in paths:
    if p.name in initial_hashes:assert hashlib.sha256(p.read_bytes()).hexdigest()==initial_hashes[p.name]
provenance['initial_numeric_input_hashes']=initial_hashes
for mod in ['numpy','scipy','sympy','numba','mpmath']:
    m=__import__(mod);provenance['dependencies'][mod]=m.__version__
dump('data/provenance.json',provenance)
summary=dict(result='NO VIOLATION FOUND',models=38,certificates_verified=38,
             catalogue_patterns=7962,catalogue_actual_slot_configurations=catalogue['original_samples'],
             catalogue_filled_slot_configurations=catalogue['covered_samples'],actual_trace_configurations=actual['original_samples'],
             reduction_geometries=20,maximal_radius_boxes=38,closest_model=18,closest_ratio=near['ratio'],closest_margin=near['margin'])
dump('data/result_summary.json',summary)

num=lambda n:f'{n:,}'
link=lambda label,path:f'[{label}]({ROOT/path})'
lines=['RESULT: NO VIOLATION FOUND','',
       'All 38 model inequalities passed the independent exact checks. No target inequality, required mean bound, retained field ball, or reduction identity failed in the sampled actual-passage class. Independent enumeration reproduces the 7,962 catalogue classes, 20 nontrivial reduced geometries and 38 maximal radius boxes.',
       '',
          'This result concerns the replacement stated in MATH_FIT: unpinned D sites with at most two kept bonds and actual external factors. The original paper also defines a larger, artificially filled-slot H1 input. I tested that larger input numerically, extending its slot vectors to balls by affinity, but the 38-model reduction does not assert coverage of all of its filled D slots. The distinction is exhibited explicitly below.',
       '',
       'Models are numbered by their zero-based position in `cores_universal_final.json`; `pid` is provenance, not a model definition, and can repeat. In the table, s means c = 961/1000, t means c = 187/200, and margin is the minimum ratio found minus that c. Ratios are rounded to twelve decimals. The certificate column reports my exact check and the reconstructed central-sector size.',
       '',
       '| Model | Type | pid | Minimum Zcur/Znext found | Margin to c | Exact certificate verified |',
       '|---:|:---:|---:|---:|---:|:---|']
for r,e in zip(search,exact['models']):
    cert='yes; scalar' if e['kind']=='scalar' else f"yes; {e['dimension']} × {e['dimension']}"
    lines.append(f"| {r['index']:02d} | {'s' if r['straight'] else 't'} | {r['pid']} | {r['minimum']:.12f} | {r['margin']:+.12f} | {cert} |")
lines += ['',
          f"The search evaluated {num(sum(r['random_starts'] for r in search))} random field configurations, {num(sum(r['collinear_starts'] for r in search))} perturbed collinear seeds, and {num(sum(r['local_starts'] for r in search))} BFGS starts: 16,384 random configurations and 512 local starts per model. Half the local starts came from the lowest sampled values and half were fresh random starts. The maximum was 350 iterations per local run. There were {num(sum(r['evaluations'] for r in search))} double-precision objective evaluations; {num(sum(r['converged'] for r in search))} local runs returned an optimizer success flag. The other runs still contributed their evaluated iterates. These are minima found, not claims of globally optimal ratios.",
          '',
          'For each literal model I sum the twelve icosahedral U spins and the additional zero D spin with probabilities 1/12, or 1/20 and 2/5. A deterministic m vertex is its listed-radius vector, without a spin integration. Independent path transfer matrices compute Z and inserted Cij; I then use Zcur = Z + sum(Cij)/3 and Znext = Z + Cfg/5 when two non-outgoing marks remain. Missing marks contribute zero. This implements the model description without consulting pattern IDs. '+link('The search results and all best field directions','data/model_search.json')+' retain Z, Zcur and Znext. '+link('The independent 80-digit reevaluations','data/cross_checks.json')+' also retain every Cij. Their ratios agree with the double-precision results and a separate four-state moment contraction to within '+f"{cross['maximum_double_error']:.3g}. Random common rotations, 32 per model, changed ratios by at most {cross['maximum_rotation_error']:.3g}.",
          '',
          'The closest model is 18. Every nonzero path field can be +e3 and its isolated outgoing mean can be −(5/14)e3. Exact integration gives Z = 244/125, Zcur = 674668/354375 and Znext = 171736/84375. Thus its ratio is 843335/901614 = '+f"{float(F(near['ratio'])):.15f}"+' and its margin is 32591/90161400 = '+f"{float(F(near['margin'])):.15g}. "+link('The complete exact configuration','data/near_threshold_witness.json')+' is saved. This is an explicit admissible model configuration, not a counterexample or a proof that the minimum is attained there.',
          '',
          'The exact checker uses Python integers, rational numbers, and integer pairs for Gaussian integers; its checking arithmetic has no floating-point matrix decisions. It first verifies all 35 monomials of degree at most four directly from the stated icosahedral coordinates. It also checks the polynomial identity behind the 3/5 three-unit-field mean bound, the orthogonal-decomposition identity for the special two-unit-field bound, and the arrival and D-mixture moment identities. '+link('These definition checks','data/definition_identities.json')+' all pass.',
          '',
          'For the 21 listed ordinary mean triples I reconstruct the numerator norm from its 3 × 3 Gram matrix, form the stated gap polynomial, transform it to the tensor Bernstein basis, compare all 567 rational coefficients with the supplied coefficients, and check nonnegativity. All coefficients match; the largest numerator or denominator has 53 bits. All three special `mean_unit_pair.json` cases, including r = 1/25, pass their degree-four check. There are 25 distinct coefficients per special case. The supplied `nonzero = 115` metadata counts five copies along an unused third axis; my 23 nonzero coefficients per case reproduce that number. There is no coefficient discrepancy. '+link('Exact mean results','data/exact_means.json')+' include the reconstructed coefficients. My graph simplifications also encounter some sharper triples; all 62 encountered records pass an additional 1,664 exact coefficient comparisons, recorded in '+link('the derived-mean checks','data/derived_mean_checks.json')+'.',
          '',
          'For each of the 22 scalar cases I independently compute ro, rf, rg, L, the coefficients of Q, its endpoint tests and its interior vertex test when applicable. All supplied radii, Q coefficients and tests match and are nonnegative. For the other 16 cases I reconstruct each Pauli-form matrix entry directly: build the local external Pauli matrix-element polynomial, integrate it using exact spin moments, and contract four-state bond messages. The basis is the unnormalized symmetric basis for two unit fields at a U vertex, singles otherwise, restricted to the central weight. Inversion indices use ring order with zero-radius fields removed. An isolated m vertex is encoded algebraically by a U field of 3R; its degree-one moment is exactly the deterministic mean R, so this imposes no physical field-radius assumption.',
          '',
          'After removing a checked positive common scalar, every reconstructed matrix agrees entry by entry with the supplied normalized matrix. I use my reconstructed matrix for every residual calculation. All 16 integer factors are lower triangular, and every row of E = den·S²·M − L Lᵀ is strictly diagonally dominant with positive diagonal. All listed residual minima match. The sizes give 14,502 matrix entries, 7,443 triangular factor entries, 129,491 Gram products and largest dimension 66. This verifies the listed finite model certificates using the paper’s Pauli-sector and Bernstein implications; it is not a new Lean kernel check. '+link('Per-model exact results','data/exact_checks.json')+' and files `data/matrix_05.json`, etc., contain the reconstructed matrices, positive physical-form scales and every residual row margin.',
          '',
          'The geometry enumeration starts from the kept-set choices in the paper, independently of the catalogue. It imposes mutual keep decisions only between nonremoved, non-tip sites, marks each allowed outgoing neighbour, removes isolated common factors, and canonicalizes reflection. The catalogue is used afterward to compare keys and attach its pid labels. The counts are:',
          '',
          '| Enumeration quantity | Independently obtained |',
          '|---|---:|',
          f"| Consistent status/kept-set assignments | {num(enumeration['consistent_assignments'])} |",
          f"| Marked outgoing choices | {num(enumeration['marked_choices'])} |",
          f"| N/E outgoing choices | {num(enumeration['NE_choices'])} |",
          f"| Effective reflection classes | {num(enumeration['reflection_classes'])} |",
          '| Missing or extra catalogue keys | 0 |',
          f"| Convex reduction branches | {num(geometry['branches'])} |",
          f"| Nonempty branches contained in a listed radius box | {num(geometry['nonempty_branches'])} |",
          f"| Empty, direct Zcur = Znext branches | {num(geometry['trivial_empty_branches'])} |",
          f"| Nontrivial reduced geometries | {geometry['geometries']} |",
          f"| Distinct radius boxes before domination | {num(geometry['distinct_radius_boxes'])} |",
          f"| Maximal radius boxes | {geometry['maximal_radius_boxes']} |",
          '| Listed boxes missing from the independent regeneration | 0 |',
          '| Additional maximal boxes | 0 |',
          '',
          'The graph rewrites integrate leaves, retain the lower five-vertex correlation when required, expand a two-bond upper D kernel or a remaining D neighbour with weights 3/5 and 2/5, integrate isolated marked vertices, pad zero fields, identify paths preserving both kinds of marks, and compare radius boxes under all such isomorphisms. Domination is checked in exact rational arithmetic; it means containment of field balls, not a claim that a ratio is monotone in a radius. The 981 empty branches are not separate entries in the list: their inequality is immediate, or they can be padded by a zero deterministic marked vertex in model 00 or 25. No nonempty branch is uncovered. '+link('The enumeration','data/enumeration.json')+', '+link('geometry audit','data/geometry_audit.json')+' and '+link('coverage for every pid','data/coverage_by_pattern.json')+' record these results.',
          '',
          'A necessary ordering interpretation is that zero-spin terms are chosen before deciding whether to cut or preserve the lower path. For example, catalogue pid 7766 has a D outgoing N; choosing its zero term removes N and exposes the lower correlated path represented by model 37. Likewise, zero E/W terms permit sharper one-sided leaf bounds. The operations commute as integrations and positive decompositions, so this order is available. Cutting all lower connections according to the original pre-decomposition presence of N would lose information and would not regenerate the stated 38 boxes. The report’s prose must be read with this adaptive ordering.',
          '',
          'I tested two catalogue slot interpretations and a separate set of passages generated directly by the paper’s trace:',
          '',
          '| Sampling family | Passages/patterns | Configurations each | Total target tests | Smallest ratio | Smallest margin to its own c | Violations |',
          '|---|---:|---:|---:|---:|---:|---:|',
          f"| Catalogue, actual-slot capacity | 7,962 | 128 | {num(catalogue['original_samples'])} | {catalogue['minimum_original_ratio']:.12f} | {catalogue['minimum_original_margin']:.12f} | 0 |",
          f"| Catalogue, paper’s filled-slot class | 7,962 | 64 | {num(catalogue['covered_samples'])} | {catalogue['minimum_covered_ratio']:.12f} | {catalogue['minimum_covered_margin']:.12f} | 0 |",
          f"| Actual stopped-trail U departures | 8,192 | 32 | {num(actual['original_samples'])} | {actual['minimum_original_ratio']:.12f} | {actual['minimum_original_margin']:.12f} | 0 |",
          '',
          'The minimum ratio and minimum margin in a row can occur at different passage types. Catalogue actual-slot tests give U corners two slots and D corners at most 2 − k, with k present internal bonds. The configurations include independent unit directions, shared conditioned outside spins, shortened or missing factors, and collinear signs. Tips include U, D and removed cases; D tips have at most one external factor when attached. Every convex branch is checked for each of the 128 configurations, with random auxiliary directions on cut fibres. These catalogue tests are an overapproximation of actual outside configurations, not a claim that every independently assigned field configuration is a complete global trace.',
          '',
          f"The direct sampler starts U/X domains on G = [−12,12]², with original protected boundary S unchanged, and follows admissible bond-deleting trails until their first hit of S. It captured 8,192 U departures from {actual['generation']['trails']} trails ({actual['generation']['steps']} traversed steps), including 2,768 straight and 5,424 turning departures, and 792 distinct catalogue classes. Actual tip laws, kept sets and missing factors are retained. Spins shared by external bonds are assigned once per outside site from their actual U/D support; a common hemisphere avoids antipodal outside bonds. Original leg pins are independent arbitrary unit vectors. There were {num(actual['actual_pin_fields'])} sampled original-pin field incidences and {num(actual['actual_outside_fields'])} outside-spin field incidences. All captured normalized local geometries occur in the catalogue. "+link('The generated passage records','data/actual_passages.jsonl')+' retain their statuses, kept masks, leg requests and outgoing directions.',
          '',
          'Intermediate checks use finite quadrature rather than the mean formulas being tested. The check counts are:',
          '',
          '| Check | Catalogue run | Direct-trail run | Failures |',
          '|---|---:|---:|---:|',
          f"| Required mean-ball comparisons | {num(catalogue['mean_tests'])} | {num(actual['mean_tests'])} | 0 |",
          f"| Final retained field-ball comparisons | {num(catalogue['field_ball_tests'])} | {num(actual['field_ball_tests'])} | 0 |",
          f"| Integrated-leaf identities on all 13 parent support points | {num(catalogue['leaf_identities'])} | {num(actual['leaf_identities'])} | 0 |",
          f"| Current/next D-mixture identities | {num(catalogue['decomposition_identities'])} | {num(actual['decomposition_identities'])} | 0 |",
          f"| Direct passage-spin integration versus I/J identities | {num(catalogue['passage_identities'])} | {num(actual['passage_identities'])} | 0 |",
          f"| Current/next auxiliary-cut quadrature identities | {num(catalogue['cut_quadrature_identities'])} | {num(actual['cut_quadrature_identities'])} | 0 |",
          f"| Random auxiliary fibres tested | {num(catalogue['cut_fibres'])} | {num(actual['cut_fibres'])} | 0 |",
          f"| Final convex-branch target inequalities | {num(catalogue['final_branch_samples'])} | {num(actual['final_branch_samples'])} | 0 |",
          '| Nonempty branch mappings outside the listed balls | 0 | 0 | 0 |',
          '',
          'Passage I/J identities use the first configuration of every pattern/passage and sum the departure spin directly. Each auxiliary-cut identity uses all 12 auxiliary quadrature nodes for its first configuration, including the two lower-corner normalizers; conditional means are tested separately on all sampled fibres. Leaf identities are checked pointwise on all 13 parent spins. D-mixture identities compare both unnormalized partition functions on every sampled configuration. All removed normalizers are common positive factors; the smallest encountered one was '+f"{min(catalogue['min_normalizer'],actual['min_normalizer']):.12f}. The largest numerical identity defect was {max(catalogue['max_leaf_identity_error'],actual['max_leaf_identity_error'],catalogue['max_decomposition_error'],actual['max_decomposition_error'],catalogue['max_passage_identity_error'],actual['max_passage_identity_error'],catalogue['max_cut_identity_error'],actual['max_cut_identity_error']):.3g}"+' (absolute for leaf factors, relative to max(1,|value|) for partition identities). The largest mean or field-radius excess was '+f"{max(catalogue['largest_mean_excess'],actual['largest_mean_excess'],catalogue['maximum_field_excess'],actual['maximum_field_excess']):.3g}"+', consistent with rounding. A numerical failure threshold of 2 × 10⁻¹² was used. The smallest final branch margins were '+f"{catalogue['minimum_final_margin']:.12f} and {actual['minimum_final_margin']:.12f}. "+link('Catalogue numerical results','data/passage_checks.json')+' and '+link('direct-trail results','data/actual_trace_checks.json')+' include counts by mean triple, model hit counts and complete worst-ratio local configurations.',
          '',
          'The scope boundary has a simple explicit example. In catalogue pid 0 the D corner (1,−1) is a leaf attached to (1,0). In the paper’s filled class give both of its artificial slots the field e3. Its slot normalizer is 6/5 and its unnormalized mean is (2/5)e3, so its effective field is (1/3)e3. This exceeds the actual D-leaf radius 1/5 by 2/15. Such a D leaf has room for only one actual external factor, whose mean radius is at most 1/5. Thus applying the actual-slot reduction unchanged to the filled class would fail this intermediate radius claim. This is outside the replacement’s stated premise and does not violate its inequalities; pid 0 itself has Zcur/Znext = 1. '+link('The exact scope example','data/scope_example.json')+' is saved. The 509,568 filled-class target tests found no target violation, but they do not turn the 38-model replacement into a certificate of the original larger H1 statement.',
          '',
          'No listed certificate was left uninterpreted. Continuous passage fields are sampled rather than exhaustively searched, and the generated histories are first stopped trails. Exceptional second-trace departures outside the covered-template premise retain the paper’s existing exceptional estimate and were not claimed to be certified by these 38 models. Exhaustiveness here applies to the finite kept-set/radius-box enumeration and the exact listed arithmetic, not to an enumeration of every possible global trace history.',
          '',
          'All programs and generated artifacts are under H1TREE_NUM. Supplied programs were inspected for slot order, unnormalized basis conventions, inversion indices and witness scales; none was imported, executed, or reused as a checking implementation. The exact matrix check uses direct local matrix-element integration, the model search uses finite-spin path transfers, and passage checks use a separate numerical four-state factorization. Source hashes, program hashes and dependency versions are in '+link('provenance.json','data/provenance.json')+'. The source prose report was edited during this run; '+link('a saved snapshot','data/claim_report_snapshot.txt')+' records the H1 statement and decoder checked here. The five numerical inputs retain their hashes from initial inspection. Search, catalogue and direct-trail RNG seeds are 20261116, 20261117 and 20261118. CPU workers were capped at eight, with one BLAS thread each. The largest per-process RSS reported by the timed runs was 262,948 KiB; arrays and worker counts stayed well below the 30 GB limit.',
          '',
          'To reproduce with the installed local dependencies, run:',
          '',
          '```bash',
          'cd /home/ubuntu/aklt/reports/H1TREE_NUM',
          'bash programs/run_all.sh',
          '```',
          '',
          'The entry points are '+link('model_search.py','programs/model_search.py')+', '+link('exact_check.py','programs/exact_check.py')+', '+link('geometry.py','programs/geometry.py')+', '+link('passage_check.py','programs/passage_check.py')+' and '+link('actual_traces.py','programs/actual_traces.py')+'. The full dependency versions are recorded, and `deps/` contains the packages used. Logs preserve each completed run and the timed resource measurements.']
(ROOT/'report.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(summary,indent=2))
