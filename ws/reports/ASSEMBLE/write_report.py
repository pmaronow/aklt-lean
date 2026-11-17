#!/usr/bin/env python3
"""Render the manually reviewed cross-file contracts and mechanical edit log."""
from collections import defaultdict
from pathlib import Path
import difflib
import json
import re

ROOT = Path('/home/ubuntu/aklt')
DEST = ROOT / 'manuscript-v2'
OUT = ROOT / 'reports/ASSEMBLE'
audit = json.loads((OUT / 'audit.json').read_text())
checks = json.loads((OUT / 'integration-checks.json').read_text())
assert checks['status'] == 'PASS'

# These are assessments made by reading each owning statement and each use,
# not conclusions inferred from the presence of a LaTeX label.
NOTES = {
 'a:finite': 'Locator: Appendix A contains precisely the finite coupling, conditional-expectation, and Poincare tools used here.',
 'c:reduce': 'The chosen allowed representation has a common positive leaf factor; Pauli positivity supplies the sphere/ball positivity needed to recover every original twenty-slot assignment.',
 'd:W': 'The conclusion is the same marginal inequality on B_i, for all proper plane colorings, translates, nonexceptional indices, and arbitrary admissible boundaries; l0=64.',
 'd:domain': 'Ordinary domains use full U kept sets, two-element D kept sets, consistency between nonremoved endpoints, the original protected layer, and no new leg factors.',
 'd:frame': 'The reference laws have positive weights and precisely the degree-four moments required by the frame definition; no invariance for arbitrary functions is assumed.',
 'd:framemodel': 'The laws use the specified three 12-letter frames, proper colorings, uniform site weights, the appropriate interaction sign, and rate-one physical-site updates.',
 'd:kernel': 'The consumer uses center-avoiding first-hit trails, departure-based revisits, the same live/dead rule, mass-free coefficients, pair types, and shifts. Short/long ordering choices remain those of d:kernel-order.',
 'd:kernel-order': 'The exact dyadic h, rho0, cutoff 12, short rational sorting with index ties, and long straight-before-turn ordering agree. Phase formulas are used for long continuations, with short sums evaluated separately.',
 'd:model': 'The torus edge set is simple and unoriented, each edge appears once, and L,N>=3 gives four distinct neighbors and the stated degree-four valence-bond polynomial.',
 'd:moment': 'Finite U/D laws, separate degree at most four, ambient plane distances, and empty-product conventions agree; no surface integral or arbitrary-function rotation is imported.',
 'd:pattern': 'The covered template retains all twenty slots, both corner slots, full U kept sets except the passage, and covering U tips; effective-record reductions keep precisely its present factors.',
 'd:pinmodel': 'Every use keeps the original G, original legs, and S(G). Pins are arbitrary unit vectors, and removal creates no pins; the ordinary U/X specialization has exactly these partition sums.',
 'd:poly': 'V4 has the prescribed inverse-binomial monomial norms and finite frame spinor choices. The first paragraph merely locates this normalization.',
 'd:ratios': 'The ratios are post-step/pre-step partition sums: D departures have ratio one, and U departures use J/I with the correct one-, two-, or three-neighbor cases. Section 7 derives its canonical coefficients directly.',
 'd:shells': 'The physical-site shells use ambient infinity distance, s=u^(1/4), integer floors k_i, the same protected cap A_i, and the same exceptional set I0.',
 'd:trace': 'Starts are unpinned and outside S, with at most three U or one D present bonds; tracing drops both bond flags, retains original legs, and gives the stated mass-free coefficients and ratios.',
 'd:weights': 'The lattice revisit weight is exactly 1/5 and records earlier departures. The virtual incoming bond is unused, initial reversal is forbidden, and straight/turn weights are x_type/3.',
 'h:H1': 'The pointwise inequality is on the complete covered pattern class and every unit slot assignment, at the same thresholds 961/1000 and 187/200; no optimality assertion is consumed.',
 'h:H2': 'The import is the all-length open-trail sum, uniform over start and incoming direction, with C_V>=1 and 0<q<1. No stronger historical rate bound is required.',
 'h:H3': 'The imported assertion bounds every finite cutoff of the specified type-dependent kernel by rho0*h. The same exact positive vector and fixed orderings are used.',
 'h:P': 'Uses concern finite G, arbitrary original unit pins, removed Y disjoint from S(G), and distance-two surviving pairs with a common removed neighbor. Distances remain to the original S(G).',
 'l:35': 'Each conditional site has at most three incident factors with fields of norm at most one. The mean bound is 3/5 for U or D; the covering step uses the proved full ball of means from three unit fields.',
 'l:CE': 'All relevant laws are strictly positive on finite products with nonempty alphabets. Conditional projections preserve those laws, including complex variance identities and empty resampling sets.',
 'l:H2-CV': 'The consumer uses precisely m=6 and q=q_* from p:H2-test; the finite-base bound permits the same explicit C_V=10.',
 'l:Iw': 'Passage integration yields Zcur=Zw[I] and Znext=Zw[J] with removed neighbors set to zero. Every pair insertion replaces a lost passage bond, maintaining separate degree four.',
 'l:Ostruct': 'The inversion is checked to be a union of groups. The resulting real symmetric operator has the required spin commutators, symmetric U-pair support, and D-pair exchange decomposition.',
 'l:alm': 'The positive m=6 vector satisfies the regenerated one-step inequality with 0<q<1; the maximum over finite bases is included, giving the uniform all-length H2 conclusion.',
 'l:boundaryconn': 'At the use, U is finite, nonempty, and star-connected, and U-complement is star-connected by l:cutgeom; hence its raw outer boundary is nonempty and star-connected.',
 'l:boxlift': 'Every actual square has integer M>=1 and L,N>=2M+3. Halo reduction is injective, bonds correspond exactly, and the local antipodal sign map transports conditional laws, updates, variances, and Hamming costs.',
 'l:colour': 'The periods satisfy L,N>=3; the supplied cycle coloring, including period three and odd periods, gives the proper torus three-coloring actually used.',
 'l:comparison': 'The translated squares are a nonempty labelled family of nonempty blocks. Every exterior fiber has gap g_M, the block gap is c>0, and the label multiplicity is T_M.',
 'l:contraction': 'P is the average over A=LN block labels; the constructed coupling has expected distance <=1-c/A, with 0<c=T_M-S_M*K<=A. The conclusion uses unnormalized block rates.',
 'l:density': 'The reference law is a positive product probability, with every boundary factor absorbed into its site weights. The density bounds give m/M=r_b^|E(Q)|; the frame reference measure of mass 5^|Lambda| is not substituted for this probability.',
 'l:exact': 'Only summed-out partition polynomials are transferred. Each integrated variable has at most four factors; fixed window letters and their actual frame weights remain in the reference window law.',
 'l:exposure': 'The stopped trails have admissible starts, and x_type>=1 bounds each covered U ratio. The given fixed ordering is restricted to actual U departures before comparison with all lattice first visits.',
 'l:finitecoupling': 'The maximal overlap construction includes zero and full overlap, and marginalization/completion has the asserted direction. The stopped construction retains both full marginals.',
 'l:finitefacts': 'The networks have at most four incident factors. Inserted observables are included in the degree-four budget; free positivity is used only without pins, and conditional independence only on positive fibers at nonneighbors.',
 'l:gram-residual': 'The matrices are regenerated symmetric integer forms and g,d,S are positive. Every residual row is checked; strict dominance implies positive diagonal. L=0 is allowed, and no invertibility is assumed.',
 'l:integercheck': 'The thresholds lie in (0,1), D0 is justified and positive, and sector bases are the unnormalized integer-coordinate bases. The scale is 15*D0*q. Bareiss is invoked only with exact divisions and positive pivots, including the proved positive-common-scalar reduction.',
 'l:inversion': 'One checked groupwise inversion has a positive semidefinite Pauli operator; the product density trace identity then gives polynomial positivity on closed unit balls and hence all unit slots.',
 'l:leaf': 'The retained leaf data satisfy the covered-template hypotheses: bonded-tip radius 3/5, reduced one-bond corner radius 1/2 or 1/3, and positive common factors for isolated leaves.',
 'l:local': 'Closure provides the covered non-tip template at each invoked U departure. The lemma explicitly allows arbitrary original pins, outside fields of norm <=1, missing factors, both corner slots, and the actual ordinary tip data.',
 'l:log-mean-bounds': 'The same rational type table is used, including turning a_t=150000/10^6 and bprime_type<=b_type. Appendix C ceilings reconstruct these exact fractions with the exact dyadic h_C.',
 'l:moments': 'Every use is a polynomial calculation of separate degree at most four, including observables. Tight-frame products have degree four, and the Pauli/local formulas use the same U second/fourth and diluted D moments.',
 'l:onepoint': 'When the estimate is applied, H1/H2 hold, the incoming bond is absent, starts are admissible, and there are at most twelve uncovered U departures anywhere along the trail. The maximum over the two pin ratios is taken before summation.',
 'l:planeenergy': 'Only admissible frame letters are used. Proper colorings give alpha=(1/12)*r_b^4 in (0,1], consistency, and conditional block gap r_b^internal-edge-count; no claim about arbitrary unit pins is imported.',
 'l:response': 'The untyped response identity uses the same positive logarithmic-mean coefficients, zero D response, free ratio <=1, and pinned ratio <=12/5. The refined coefficient choice is explicitly derived in Section 7.',
 'l:sector': 'The supported tensor-sector operators are Hermitian, preserve the sectors, and commute with all three spin generators. The central weight uses the parity of the singles, so positivity extends to exactly those full supported sectors.',
 'l:shellgeom': 'The stopped-coupling scale satisfies u>=M_g(l0), and all surgery indices lie in 2..i1. Cap estimates are used only outside I0. The parallel-side clause is used in l:cutgeom only after checking its corrected nonexceptional range.',
 'l:star': 'L,N>=3 gives five distinct star sites. The same finite positive g_star is used, and sum_x H_x=2H yields precisely the later quantum factor 1/2.',
 'l:stationary-assembly': 'Its exact five prefix ceilings give the stated B/C row bounds with the same dyadic h_C and rho0=993015/10^6, uniformly in the true-trail cutoff; this is exactly H3_h.',
 'l:surgery': 'Each selected joint resampling has, for every fixed input pair, the correct two conditional marginals on F_i; complements stay fixed. Thus each deterministic-index step preserves both full laws.',
 'l:thicken': 'X0 is finite, nonempty, and star-connected, so its nearest-neighbor crosses form a connected cut. The ambient-distance weighted comparison has factor 5/theta for 0<theta<1.',
 'l:threeframes': 'The three rotations are antipodal unit-vector fourth-moment frames with weights 1/12 and exact bond bounds b..2-b for both signs; b=(5-sqrt(5))/505 and r_b=b/(2-b).',
 'p:H2-test': 'The integer vector is on the same memory-six automaton and thresholds. Its positive row test has common denominator 2695605 and exactly the rational q_* consumed by H2 and the recursion.',
 'p:automaton10': 'The imported raw/quotient reconstruction has 60092 windows and 3741 classes, absolute direction labels, and the required final-direction condition for non-revisit transitions; no spatial symmetry or class-size factor is assumed.',
 'p:pairwalk': 'Both starts meet the U<=3/D<=1 bounds. The first target has the required degree, and the second protected target e has already lost its first arrival bond. The second stopping set is S union {e}=S; target constants and degree-four insertions match.',
 'p:stationary-check': 'The same five cases, memory 10, prefix 12>=10+2, radius 70, value scale 2^16, coefficient scale 2^48, and exact prefix upper bounds are used. All rows, caps, terminal values, and array indices remain required.',
 'p:toruskernel': 'Every invocation has L,N>=3. The owner proves B nonzero and the one-dimensional kernel at every parity, independently of frames or numerical inputs; no assertion for a plane or open box is imported.',
 's:topology': 'Locator: Appendix B contains the exact star-boundary and cross-thickening lemmas invoked by the connected-cut proof.',
 't:QD': 'The periods are at least three, the torus coloring is proper, and the specified frame law is used. The imported lower bound is exactly (g_star/2)*lambda(mu_af), with both local orientation signs retained by its proof.',
 't:cutMOS': 'P(A,theta) supplies A>=2 and 0<theta<1 on arbitrary original unit pins. The conclusion is W(64,p0,Mstar) with common positive constants for every proper plane coloring and translate, as needed by t:mainW.',
 't:inputs': 'The import supplies H1 at the prescribed thresholds, H2 with C_V=10 and the exact 0<q<1, and H3_h for the same type-dependent kernel/orderings. Consumers use these conclusions, without assuming a complete family of nonzero Gram factors.',
 't:main': 'The final Section 4 assembly proves exactly the two unconditional conclusions stated in Section 1: uniqueness for all L,N>=3 and one positive gap for all L,N>=L0, without parity restrictions.',
 't:mainW': 'The premise is exactly the uniform W estimate for the plane frame family. Its conclusion is already a quantum torus gap and uniqueness for all sufficiently large integer periods of either parity.',
 't:rec': 'H1 thresholds, arbitrary C_V>=1 and 0<q<1, and the same type-dependent H3_h/orderings are supplied by t:inputs. Its conclusion P has arbitrary original unit pins and all removed-site pairs required by Section 5.',
}

grouped = defaultdict(list)
for ref in audit['cross_references']:
    key = (ref['file'], ref['label'], ref['owner'][0]['file'])
    grouped[key].append(ref['line'])
assert set(NOTES) == {label for _, label, _ in grouped}
OVERRIDES = {
 ('app-input-contracts.tex', 'd:kernel'): 'True kernel weights, pair types, shifts, and departure-based dead-site counts match. The stationary suffix operator explicitly relaxes forgotten revisits and dead non-outgoing neighbors, using bprime_type<=b_type for domination; equality of relaxed and true trail classes is never assumed. Exact short and prefix sums retain the actual counts.',
 ('app-local-operator.tex', 'l:35'): 'A covering U tip has exactly three unit slot fields and one optional internal bond. The degree-four numerator and degree-three denominator give a normalized mean of norm <=3/5, exactly the radius required by the leaf reduction.',
 ('sec5-window.tex', 'l:35'): 'After x_j is removed, its distinct surviving neighbors are unpinned, conditionally independent, and have at most three present bonds. Their conditional means therefore have norm <=3/5 on positive fibers, as used in the removal lower bound.',
}
reviews = []
for (filename, label, owner), lines in sorted(grouped.items()):
    reviews.append({'file': filename, 'use_lines': lines, 'label': label,
                    'owner': owner, 'owner_line': audit['labels'][label][0]['line'],
                    'match': True, 'assessment': OVERRIDES.get((filename, label), NOTES[label])})
(OUT / 'cross-file-reviews.json').write_text(json.dumps(reviews, indent=2) + '\n')

def filelink(filename, line=None):
    return f'[{filename}' + (f':{line}' if line else '') + f']({DEST / filename}' + (f':{line}' if line else '') + ')'

sections = []
sections.append('''STATUS: COMPLETE

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
git --git-dir=/home/ubuntu/aklt/manuscript-v2/.git-metadata \\
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
''')
for r in reviews:
    lines = ', '.join(map(str, r['use_lines']))
    use = filelink(r['file'], r['use_lines'][0]) + f" (`{r['label']}`; lines {lines})"
    owner = filelink(r['owner'], r['owner_line'])
    assessment = r['assessment'].replace('|', '\\|')
    sections.append(f"| {use} | {owner} | Yes. {assessment} |\n")

sections.append('''
## Every edit to a section file

Locations below are the final assembled file's starting line and the corresponding source starting line. Before/after blocks are exact differing lines. Comments were replaced with blank lines, preserving their source line positions before other edits. All eight source comment lines were removed; none remain in main.tex or any section. The new first paragraph is expressly authorized by the task. All other prose edits remove history of prior methods or certificate preparation and leave the present mathematical conditions intact.

''')
for n, edit in enumerate(audit['section_edits'], 1):
    sections.append(f"### E{n}: {filelink(edit['file'], edit['assembled_line'])}\n\n")
    sections.append(f"Source: `{edit['file']}:{edit['source_line']}`. Before:\n\n```tex\n{edit['before']}\n```\n\n")
    if not edit['after'].strip():
        sections.append(f"After: {edit['assembled_line_count']} blank line(s).\n\n")
    else:
        sections.append(f"After:\n\n```tex\n{edit['after']}\n```\n\n")
sections.append('''The unchanged section files are sec2-moments.tex, sec3-quantum-frames.tex, sec5-window.tex, sec6-walks.tex, app-finite.tex, and app-topology.tex. The retained source repairs M1--M3 are already present in those inputs and are not assembly edits. A full reproducible patch is provided in [section-edits.patch](section-edits.patch).

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
''')

report = ''.join(sections)
(OUT / 'report.md').write_text(report)
patch = []
for source in json.loads((OUT / 'sources.json').read_text()):
    before = Path(source['source']).read_text().splitlines(keepends=True)
    after = (DEST / source['file']).read_text().splitlines(keepends=True)
    patch.extend(difflib.unified_diff(before, after, fromfile=source['source'],
                 tofile=str(DEST / source['file'])))
(OUT / 'section-edits.patch').write_text(''.join(patch))
print(f"Wrote report: {len(reviews)} review rows, {len(audit['section_edits'])} edit blocks.")
