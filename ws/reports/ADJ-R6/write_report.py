"""Assemble the adjudication with the exact, executable replacement fragments."""
import json
import re
from pathlib import Path

E = json.loads(Path('edits.json').read_text())
by_id = {e['id']: e for e in E}
parts = []


def put(s):
    # Use dollar delimiters in Markdown prose, keeping code/LaTeX fences exact.
    math = [
        'y', 'd', '-d', r'E[(n\cdot d)^{2j}]=1/(2j+1)', '3/5', '1/2',
        r'\mu_E=-rd,\mu_W=rd,\mu_N=d/5', r'E_U[n_i n_j]=\delta_{ij}/3',
        r'E_D[n_i n_j]=\delta_{ij}/5', r'4+4\cdot2=12', r'3+2\cdot4=11',
        '4+8', r'k\le11', 'k=11', r'c(\pi)', 't=1', '10^{-12}',
        r'a=\rho_f\rho_g', r'L(\pm1)\ge0', r'Q(\pm1)\ge0',
        r'Q(-q_1/(2q_2))\ge0', 'q_2>0', 'a=0', r'\ct\le416114/444675',
        r'3\cdot7962+7', r'Z_{\rm cur}/Z_{\rm next}', r'Xs^+=(s^-)^{\mathsf T}X',
        '+1', '10^{-7}', r'2.4\cdot10^{-15}', r'2.5\cdot10^{-15}',
        r'2\cdot10^{-5}', '10^{-5}', r'(\mathrm{leafred},\mathcal I)',
        r'1.4\cdot10^{-8}', r'4\cdot4=16', 'u=2^{-53}',
        r'\gamma_{32}=32u/(1-32u)', r'\widehat s\ge\eta s', 's',
        r'\widehat s<2^{61}', r's<2^{61}/\eta', 's<2^{61}', 'C_{ab}',
        r'C_{ab}<3\cdot2^{61}/\eta<2^{63}', 'Z,C', '2^{58}',
        r'2^{58}/\eta<2^{59}', "5qA-3pA'", r'\mu_x=\rho_xd_x', 'd_x',
        't', r'\mu_f+\mu_g=0', '4/5', '1,1,4/3,2', '1,4/3,3/2',
        'L_T', r'(1-t)^2\ge0', '1-(169/385)^2/3=416114/444675',
        '1,-1', '2,0,-2', 'p', r'z^{s\bmod2}', '131+48+48+18=245',
    ]
    display = re.escape(chr(92)+'[') + '.*?' + re.escape(chr(92)+']')
    chunks = re.split(r'(```.*?```|`[^`\n]*`|'+display+')', s, flags=re.S)
    for i in range(0, len(chunks), 2):
        t = re.sub(r'(?<!\\)mu_', lambda _: r'\mu_', chunks[i])
        for m in sorted(math, key=len, reverse=True):
            t = t.replace('('+m+')', '$'+m+'$')
        t = t.replace(r'\ct\le416114/444675', r'c_{\mathrm t}\le416114/444675')
        t = t.replace('equation (D.17)', 'equation (D.16)')
        chunks[i] = t
    s = ''.join(chunks)
    parts.append(s.strip()+'\n')


def correction(ids):
    for eid in ids:
        e = by_id[eid]
        put(f"**{eid} — target `manuscript/{e['file']}:{e['start']}–{e['end']}` (frozen-source lines).** {e['description']}\n\n```latex\n{e['new']}\n```")


put(r'''
STATUS: COMPLETE

This adjudication covers findings 1–7 in §1 of `/home/ubuntu/aklt/referee/REF-R6/report.md`. I independently reconstructed the pattern family, pruned the actual graphs with rational arithmetic, recomputed the counterexample and the three named exact values, and counted the current matrix blocks. I inspected the archived validation programs and outputs rather than treating the referee's unsuccessful bundle search as evidence that the validations did not exist.

The main theorem and its constants can be retained. Finding 1 requires an explicit restriction of the pattern definition to the convention actually used by the 7,962 records. Finding 4 is substantially modified: most disputed validations do exist in the full project archive. The global optimality claims in finding 3 remain unproved by those validations.

All input files remained unchanged. No sub-agents were used. The supplemental scripts and logs are in this working directory; they use the standard library and exact `Fraction` arithmetic. `audit_math.py` imports no production or referee code. `audit_archives.py` checks archival existence, coverage and consistency; reading archived success records is distinguished below from independently replaying the matrix computations. I did not rerun the entire NumPy/FLINT operator-verification suite. That replay is not needed to decide these seven findings. I did replay both small Bareiss tests, extracting the production function unchanged to avoid its unrelated NumPy import.

Paths beginning `manuscript/` below are relative to `/home/ubuntu/aklt/manuscript/bundle/`. Archive-table paths are relative to `/home/ubuntu/aklt/source-full/agents/`. All replacement line ranges refer to the frozen sources. Each LaTeX block replaces the identified fragment, retaining its surrounding statement, label and numbering. `edits.json` contains the exact original and replacement strings; `prepare_edits.py` applies them only to the local `proposed-manuscript/` preview.

The audited data file is `/home/ubuntu/aklt/manuscript/bundle/programs/data/pext/pext7962.json`. Unqualified primary-checker filenames refer to `bundle/programs/h1-local/code/`.
''')

put(r'''
## FINDING 1: CONFIRMED

**Evidence and mathematical decision.** Definition 6.1 (`sec6-walks.tex:10,14–16`) allows a general U site to have a chosen kept set; the requirement to keep every bond belongs specifically to `\Dcons(G)`. Definition 6.6 (`:104,108`) refers to the general definition and explicitly specifies D kept sets, but omits the corresponding U restriction and the other three kept bonds of (y). Thus the stated definition admits the referee's broader reading. The omitted restrictions are used in the first sentence of Lemma D.1's proof (`app-local.tex:26`).

The JSON records contain effective kinds and present bonds, not complete kept sets. I therefore tested the exact claim appropriate to that encoding: are their keys precisely the effective images of assignments with every U site other than (y) keeping all four lattice bonds, (y) keeping exactly its three non-arrival bonds, the specified two-bond D sets, and (C)? My independent enumeration distinguishes actual outside-corner leg choices before taking the effective quotient. It gives exactly the supplied set, with neither missing nor extra keys. This confirms the convention on **all 7,962 records**, rather than inferring it from a comment or a few examples. Absent isolated-site data do not determine unique original kept sets.

Command, from this working directory:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 audit_math.py > audit_math.log
```

Relevant output:

```text
ENUM raw configurations: 106101
ENUM effective: 7962 straight: 2696 turn: 5266
ENUM records: 7962 distinct: 7962 missing: 0 extra: 0
WITNESS direct moment messages: tip 3/5 corner 1/2 E/W 169/385 N 1/5
WITNESS ratio: 1040285/1131207 decimal 0.9196239061462668 187/200 minus ratio 3478709/226241400
WITNESS broad-reading consistency (C): PASS; key in frozen records: False
```

The independent enumeration follows directly from the local rules. Each of E,N,W has five options (U; X; D retaining (y) and one of its other three neighbours), S has four, and each corner has eight (U; X; six actual two-element D kept sets). Filtering the corner options by (C), then reflecting and deleting isolated factors, produces the counts above. The raw count precedes choosing an out-neighbour; it includes assignments with no eligible out-neighbour. The tip exception is implemented exactly as in the definition. All outside corner legs become slots even if omitted from the original kept set.

For completeness, the counterexample can be checked without the radius lemma or an optimizer. Remove S; all other relevant sites are U and the out-neighbour is E. Keep (y)'s E,N,W bonds. Give N only its bonds to (y) and its tip; delete the N–(1,1) and N–(-1,1) bonds at both ends. All other U sites keep every other bond. This is consistent under the broad reading. In particular, the upper corners have three kept bonds, so the example is excluded by the corrected U rule.

For a unit (d), assign all E-branch slots (-d), and all W- and N-branch slots (d). Other slots are immaterial. Direct spherical moments (E[(n\cdot d)^{2j}]=1/(2j+1)) give tip message (3/5), leaf-corner message (1/2), and

\[
r=\frac{(3/5+1/2+1/2)/3+(3/5)(1/2)(1/2)/5}
        {1+((3/5)(1/2)+(3/5)(1/2)+(1/2)(1/2))/3}=\frac{169}{385}.
\]

Thus (mu_E=-rd,mu_W=rd,mu_N=d/5). Integrating (y), using (E_U[n_i n_j]=\delta_{ij}/3) and (E_D[n_i n_j]=\delta_{ij}/5), gives

\[
\frac{Z_{\rm cur}}{Z_{\rm next}}
=\frac{1-r^2/3}{1+r/25}
=\frac{1040285}{1131207}<\frac{187}{200}.
\]

This proves an actual failure of (H1) under the broader definition. Replacing the definition is sufficient; lowering the theorem's constants is unnecessary.

**Correction.**
''')
correction(['E01'])
put(r'''
**Consequences elsewhere.** With this correction, `app-local.tex:26` becomes literally justified. Lemma 6.8, (H1), Theorems 8.1 and 8.3, and the proof at `app-local.tex:302–304` use the corrected class without any changed constants or proof steps. Lemma 7.1 already states and proves precisely the needed kept-set rule (`sec7-recursion.tex:21,28,30`), including the exception at the current endpoint, so no recursion repair is needed. Do not replace Definition 6.1 by a global U-all-bonds rule: its general domains deliberately include the endpoint exception.
''')

put(r'''
## FINDING 2: CONFIRMED

**Evidence and decision.** The two representations are defined at `app-local.tex:62`. Counting their vectors from the present graph, rather than trusting the certificate's stored `n`, gives:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 audit_math.py > audit_math.log
```

```text
DIM all records: max unreduced 12 max reduced 11 unreduced=12 records 36
DIM pid 113: unreduced 12 reduced 9
CERT certificates_covered_operator_only.jsonl coverage/threshold/model/tipradius/inversion groups: PASS; operator 7962 closed 0 unreduced [(3596, 11), (7725, 11)] max selected n 11
CERT certificates_covered.jsonl coverage/threshold/model/tipradius/inversion groups: PASS; operator 3227 closed 4735 unreduced [(3596, 11)] max selected n 11
```

The full group list in `audit_math.log` exhibits four tip singles and four corner pairs for ID 113: (4+4\cdot2=12). This is a counterexample to the universal assertion at `app-local.tex:282`, not to the definition of the representation.

There is also a direct reason for the correct reduced bound. With at most three tip bonds there are at most (3+2\cdot4=11) vectors. If all four tip bonds are present, S is D and spends one of its two kept bonds on its tip. It can keep at most one of its two corner bonds. At least one lower corner therefore has at most one present bond; deleting it or replacing it by a single vector lowers the upper bound (4+8) by at least one. Hence the reduced bound (k\le11) is uniform. `run_prod.py:76–80` excludes unreduced choices with more than eleven vectors, consistently with the actual selected records.

**Correction.**
''')
correction(['E13'])
put(r'''
**Consequences elsewhere.** The reduced-representation statement in `sec8-computer-assisted.tex:59` remains true, as do the bounds for every selected certificate and the examples with (k=11). No matrix, threshold, lemma, or certificate file needs to change.
''')

put(r'''
## FINDING 3: CONFIRMED

**Evidence and mathematical decision.** An exact value of (c(\pi)) for one graph proves an upper bound on the class minimum, not a matching lower bound for all other graphs. The supplied two covered certificate files store only `target = "961/1000"` or `"187/200"`. `verify_all.py:22–30` takes those targets into the exact test; it does not raise them to the proposed class minima. The independent archived verifier also derives only those H1 thresholds (`73-reimplement-H1/code/run_opall.py:18,36–40`; `code/run_k1.py:15,42`). Its existence therefore does not fill this gap.

I independently integrated actual tips, pruned all pendant vertices and checked the scalar quadratic criterion in exact fractions. For the three named graphs, the inequality at the stated fraction holds and is attained at (t=1), choosing the out-root mean opposite to the sum of the other means. This proves equality, without using the merely finite observation that the test fails after adding (10^{-12}).

```bash
PYTHONDONTWRITEBYTECODE=1 python3 audit_math.py > audit_math.log
```

```text
CLOSED exact H1 tests/radii: 4735 {'turn': 3182, 'straight': 1553} all PASS
VALUE pid 7645 radii {'(1, 0)': '740/2193', '(-1, 0)': '3/25', '(0, 1)': '7/24'} exact 3825127/3979368 attained at t=1; test at value PASS; value+1e-12 FAIL
VALUE pid 1382 radii {'(1, 0)': '112/275', '(-1, 0)': '112/275', '(0, 1)': '3/25'} exact 1071655/1145463 attained at t=1; test at value PASS; value+1e-12 FAIL
VALUE pid 5469 radii {'(1, 0)': '169/385', '(-1, 0)': '169/385'} exact 416114/444675 attained at t=1; test at value PASS; value+1e-12 FAIL
```

For example, for (a=\rho_f\rho_g), the exact value attained at (t=1) is

\[
\frac{1+a/3-\rho_o(\rho_f+\rho_g)/3}{1+a/5}.
\]

The lower-bound test is (L(\pm1)\ge0), (Q(\pm1)\ge0), and (Q(-q_1/(2q_2))\ge0) when (q_2>0) and the vertex is inside the interval. This handles (a=0) and all zero-radius cases. The numbers printed above are exact; the manuscript's six-place numbers are numerical roundings.

After finding 1's correction, the certified information is a class lower bound of (961/1000) or (187/200), together with the corresponding individual-pattern upper bounds. No archive-wide exact comparison at the two larger fractions is supplied. The word “tightest,” the class-minimum row, and the introduction's **“smallest margins”** therefore need qualification. The missing introductory occurrence is a consequence beyond the locations listed by the referee.

**Corrections.** These identify the displayed patterns and describe their numerical ranking without changing their exact individual values.
''')
correction(['E00', 'E02', 'E03', 'E04', 'E06', 'E07', 'E09', 'E10', 'E11', 'E19', 'E24'])
put(r'''
E19 also specifies the actual rounded threshold used by the archived negative-control program, relevant to finding 4.

**Consequences elsewhere.** Theorem 8.3 and the main theorem use the smaller certified constants and are unchanged. Remark 8.4's explicit upper bound (\ct\le416114/444675), and the corresponding statement at `sec8-computer-assisted.tex:9`, remain justified by a single exact pattern; they do not require any global ranking. Proposition D.9 and equation (D.17), label `e:5469`, retain their statements and numbering. No stronger global optimum is asserted by these corrections.
''')

put(r'''
## FINDING 4: CONFIRMED-MODIFIED

**Decision.** The frozen bundle omits the additional validation files, but the full archive supplies the disputed independent enumeration, the three-point untied-slot comparison, the exact total-spin check, the second exchange-operator implementation and its complete results, and the 600-case LDL test. It would be incorrect to conclude from the smaller bundle that these programs or results do not exist. What remains incomplete is their provenance in the manuscript/bundle and the missing driver for the specific 30-trial exact structural mutation test. There are also small differences between literal prose claims and what the programs compare or print.

I searched the complete `source-full/agents/` tree, not just the four suggested directories. Folder 63 supplies the original pattern data; 70 supplies the primary checker; 72 and 73 supply most of the questioned independent validations. The data in `63-certify-N/out/pext7962.json` are identical to the frozen data, and the 70 copies of `cert.py`, `ring.py`, `closed_exact.py` and both covered certificate files are byte-identical to the frozen copies. The 57 data used by the independent programs agree with all 7,962 frozen graph structures and their order. Thus these are validations of the same effective family and certificate choices.

**Precise archival inventory.** Agent-folder paths in the next table are relative to `/home/ubuntu/aklt/source-full/agents/`. Within each row, abbreviated `code/`, `out/`, `NOTES.md` and `LOG.md` paths are relative to the agent folder named in that row.

| Manuscript claim | Archived programs and outputs | What is supported; limits |
|---|---|---|
| Second enumeration: 106,101 and 7,962, class by class (`app-local.tex:282`) | `72-audit-H1-certificates/code/enum_pext.py:29–34,40–101,104–122`; `72-audit-H1-certificates/out/enum_pext.txt` | Source enumerates actual kept sets including outside corner legs and imposes (C). Output says `106101`, `7962`, `2696`, `5266`, missing `0`, extra `0`. **Supported**, and independently reproduced by my own enumerator. The raw count is before choosing an out-neighbour; it is not a count of complete patterns with an out-neighbour already chosen. |
| Three random full-slot points per pattern (`:292`) | `72-audit-H1-certificates/code/brute.py:38–92`; `72-audit-H1-certificates/code/xcheck_brute.py:15,35–84`; `72-audit-H1-certificates/out/xcheck_brute_all.json` | **Supported for ratios.** `npts` is an argument; 23,893 comparisons equal (3\cdot7962+7), with an extra evaluation of each slotless case. The vectors are independent before the reduction map, including all three tip slots. The observed maximum relative ratio discrepancy is `2.3418360722435107e-15`. `Certificate.evaluate` and `Brute.ratio` compare (Z_{\rm cur}/Z_{\rm next}); they do **not** compare the two unnormalized partition functions separately, nor certify each individual integer coefficient by this floating test. |
| Exact total-spin commutation for all 7,962 (`:293`) | `72-audit-H1-certificates/code/su2check.py:24–71,83–93`; `72-audit-H1-certificates/out/su2check_all_summary.json` | **Supported.** Two summaries each record 3,981 exact checks, with no failures. In the nonorthonormal congruence basis the tested identity is (Xs^+=(s^-)^{\mathsf T}X), for each of the current/next matrices, rather than an incorrectly interpreted ordinary matrix commutator. The source also compares all-sector and central-sector floating eigenvalues. The summary is aggregate output, not 7,962 archived per-pattern rows. |
| Detecting a (+1) nonconstant-coefficient mutation in 30/30 trials (`:293`) | `72-audit-H1-certificates/out/unitpert.txt`; descriptions in `72-audit-H1-certificates/NOTES.md`, Entry 8.4, and `LOG.md` | **Output exists, generating driver not located in the archive.** The log contains 30 specified coefficient perturbations, all `False` for passing the exact structure checks, and `undetected: 0 of 30`. `code/negctl.py:48–57` does contain a different (+1) mutation comparison of floating ratios; it does not generate this exact structural-check log. The archived `su2check.py` has no 30-trial mutation loop. The result is reported archival evidence, not a fully reproducible archived program/output pair. |
| Exact positivity on all spin-component sectors for 63 patterns (`:294`) | `72-audit-H1-certificates/code/su2check.py:97–100`; `72-audit-H1-certificates/out/su2_allexact.json`; also `code/negctl.py:41–43`, `out/negctl_hard.json`, `out/negctl_random.json` | **Supported as an “at least 63” statement.** The first JSON has 50 successful exact all-sector rows. The union with successful target all-sector rows in the two negative-control files has **77 distinct IDs**, all accepted. The archive also contains the stronger independent all-sector check of every pattern in folder 73. One need not reconstruct the notes' historical choice of 63 to establish the stated weaker claim. |
| Closed-form/operator numerical comparison on 4,735, 4,250 agreeing within (10^{-7}) (`:295`) | `72-audit-H1-certificates/code/two_proofs.py`; `72-audit-H1-certificates/out/two_proofs.txt` | **Supported**, except the literal upper bound needs upward rounding: the maximum displayed excess is `2.4424906541753444e-15`, which is larger than (2.4\cdot10^{-15}). Use (2.5\cdot10^{-15}). This remains a numerical comparison, not stronger exact optimality certification. |
| Negative controls above the numerical minima (`:296`) | `72-audit-H1-certificates/code/negctl.py:29–43,58–63`; `72-audit-H1-certificates/out/negctl_hard.json`, including IDs 7645, 1382, 5469 | **Supported with the actual threshold convention.** The program adds (2\cdot10^{-5}), then rounds upward to a multiple of (10^{-5}); it does not generally test the unrounded sum. E19 gives the precise wording. |
| Independent symbolic integration, exchange operators, integer congruence and diagonal dominance (`:298`) | `73-reimplement-H1/code/wick.py:42–91,224–226`; `code/opcert.py:32–71,165–212,253–303`; `code/run_opall.py`; `73-reimplement-H1/out/operator_only_results.jsonl`; `out/summary.txt` | **Supported.** The 7,962 unique result records cover exactly IDs 0–7961, use the frozen ((\mathrm{leafred},\mathcal I)) choices and type-derived H1 thresholds, and report every block successful and no cross-sector entry. The 48,672 recorded spin-component blocks cover all sectors, not only the central sector. The full-space/complement split is exactly **4,992 / 2,970**. `opcert.py` chooses an integer triangular congruence from floating Cholesky data, checks nonzero diagonal, multiplies with FLINT integers, and checks positive strict diagonal dominance exactly. Large-entry fallback constructs the operator sector by sector; zero cross-sector entries then follow from the permutation construction (`:286–291`). The conceptual whole operator and all of its sectors are covered. |
| Same second implementation verifies the mixed file's closed certificates and numerical attainability (`:298`) | `73-reimplement-H1/code/closed.py`, `code/run_k1.py`, `code/numeval.py`, `code/run_k1b.py`; `73-reimplement-H1/out/k1_exact.jsonl`, `out/k1_summary.txt`, `out/k1b_numerics.jsonl` | **Supported.** There are 4,735 unique exact-success records, with matching classification and exact rational radii, and 4,735 numerical records. Maximum reported minimization gap is `1.3660174214003007e-08`; no reported random/minimized value goes below the closed form. The other 3,227 mixed-file operator choices agree with the operator-only choices (also checked by my scripts); `out/k2_results.jsonl` separately records 3,227 exact successes. |
| Bareiss versus exact LDLᵀ on 600 matrices (`:300`) | `72-audit-H1-certificates/code/test_bareiss72.py:10–39`; `72-audit-H1-certificates/NOTES.md:169–171`; `72-audit-H1-certificates/LOG.md:21` | **Program and recorded result exist.** The program really uses 600 cases and exact fractions, including large, singular and perturbed examples. The archived `NOTES.md`/`LOG.md` record 600/600 agreements; I found no dedicated saved stdout file for this test. My fresh execution below gives 600 agreements, 0 disagreements, 346 PD cases. The bundle's different 400-case test neither refutes nor substitutes for this archived 600-case test. |

**Commands and independently checked outputs.**

```bash
PYTHONDONTWRITEBYTECODE=1 python3 audit_archives.py > audit_archives.log
PYTHONDONTWRITEBYTECODE=1 python3 replay_bareiss.py > replay_bareiss.log
rg -n 'unitpert|perturbed coefficient|undetected' \
  /home/ubuntu/aklt/source-full \
  -g '*.py' -g '*.c' -g '*.sh' -g '*.ipynb' --stats
```

Selected output (the last search covered 741 source/notebook files and found no match):

```text
DATA frozen records = 63 records; structures = 57 merged: 7962/7962
CODE frozen cert.py, ring.py, closed_exact.py = archived 70 copies: byte-identical
CERT frozen two covered certificate files = archived 70 copies: byte-identical
ALL-SECTOR 72 sample 50 union negative-control target checks: 77
MUTATION archived output: 30 detected; final: undetected: 0 of 30
SECOND OPERATOR archived coverage/choices/type-threshold/all-sector results: 7962 PASS
SECOND OPERATOR fullspace: 4992 U-pair complement: 2970 all Sz blocks: 48672
SECOND CLOSED archived coverage/radii/exact threshold results: 4735 PASS
SECOND NUMERICS decoupled: 4735 max gap: 1.3660174214003007e-08 min(opt_min - closed): 0.0
bareiss_pd agrees with Sylvester (exact Fractions) on 400 random matrices: 235 PD, 165 not PD
{'agree': 600, 'disagree': 0, 'pd': 346}
```

The obsolete absolute `/home/user/otis-claude/research/aklt-gap/agents/...` paths in these programs must be relocated to the supplied tree, with outputs directed to a writable directory, to replay them here. NumPy is needed by folder 72; the full folder-73 verifier also uses SciPy and python-flint. These observations concern invocation, not absence of the programs. `replay_bareiss.py` avoids relocation and those dependencies by loading only the unchanged `bareiss_pd` AST into an in-memory `cert` module and executing both test sources unchanged.

**Corrections.** Retain the supported validations, identify the full-archive locations, state exactly what was compared, and disclose the missing mutation driver. The 600-case sentence can remain substantively intact with its actual provenance. The primary mathematical certificate proof remains separate from these checks.
''')
correction(['E12', 'E16', 'E17', 'E18', 'E20', 'E21', 'E22'])
put(r'''
Apply E19 under finding 3 as well; it gives the archived negative-control threshold convention. These replacements document the existing full archive and require no write to the frozen bundle.

**Consequences elsewhere.** No theorem, constant or mathematical lemma changes because these additional validations were performed in other archived programs. The assertions in checks (3), the second implementation's coverage counts, and its (1.4\cdot10^{-8}) numerical gap can remain. The mutation result must no longer be presented as a program/output pair that a reader can reproduce from the supplied archive. A future repackaging can include these identified files, but the present adjudication does not depend on such an external action.
''')

put(r'''
## FINDING 5: CONFIRMED

**Evidence and arithmetic decision.** `cert.py:45–65` creates binary64 arrays of small integer moment numerators, later converted exactly to `int64` (`:123–133`). `itensordot` (`:76–82`) converts its nonnegative integer inputs to binary64, contracts the shadows and tests a floating maximum before the integer contraction. `cur_next_int` (`:162–175`) uses further shadows in its coefficient guards. Thus “Floating-point arithmetic is used only for this choice” (`app-local.tex:286`) is false as a description of the checker. The header at `cert.py:4–7` also describes an obsolete floating-integer implementation; it is not evidence of what the current body executes.

The mathematical exactness claim can nevertheless be retained with an explicit guard argument. Each half-ring contraction sums at most four products; the closing contraction sums at most (4\cdot4=16). All inputs are nonnegative. Let (u=2^{-53}), (\gamma_{32}=32u/(1-32u)), and

\[
\eta=(1-u)^2(1-\gamma_{32})>1-10^{-12}>3/4.
\]

Two integer-to-binary64 conversions and a dot product of at most sixteen products give (\widehat s\ge\eta s) for the exact nonnegative contraction entry (s). There is no underflow or binary64 overflow in these operations on `int64` inputs. A passing shadow test (\widehat s<2^{61}) therefore implies (s<2^{61}/\eta), well below the signed-64-bit limit, though it does not literally prove (s<2^{61}). Nonnegativity bounds every integer product and partial sum by the final contraction entry.

One must also cover the later coefficient formation, rather than checking the contraction in isolation. Each (C_{ab}) is a sum of three such contraction tensors, so (C_{ab}<3\cdot2^{61}/\eta<2^{63}) even before the final guard. The final shadows are computed from these exact nonnegative (Z,C) arrays, independently of the already formed `cur` and `nxt` arrays. Their accepted (2^{58}) limits bound the true coefficient sums by (2^{58}/\eta<2^{59}). Thus on every accepted run those integer multiplications and sums also fit. A rejected run might already have formed a wrapped candidate array, but it cannot thereby falsify the independently reconstructed shadow test.

The later signed Pauli steps have pre-operation magnitude guards (`cert.py:256–264,309–322`) and an unbounded-integer fallback (`:269–276`); the final matrices (5qA-3pA') and Bareiss divisions are formed with Python integers (`:445`, `:361–384`). The correction concerns the trust explanation, not a discovered false positivity verdict.

```bash
PYTHONDONTWRITEBYTECODE=1 python3 audit_math.py > audit_math.log
```

```text
GUARD exact lower factor > 1/2: True and > 1-1/10^12: True
```

Those comparisons are themselves rational computations; they are not floating estimates of the error factor. The explanation assumes ordinary binary64 round-to-nearest arithmetic for the shadow operations, and retains the existing prohibition on disabling assertions.

**Corrections.**
''')
correction(['E14', 'E15', 'E23'])
put(r'''
**Consequences elsewhere.** Claims that the polynomial coefficients and the positive-definiteness verdicts are exact remain valid with this arithmetic justification. The introduction, abstract, Section 8 and Theorem 8.3 do not say that every operation is integer-only; their exact-certificate descriptions need no further change. The frozen code need not be altered for these manuscript repairs. If its introductory docstring is later maintained, its obsolete floating-integer description should be synchronized with the body; changing that documentation is not needed to make the manuscript proof correct.
''')

put(r'''
## FINDING 6: CONFIRMED

**Evidence and mathematical decision.** The proof of Proposition D.9 (`app-local.tex:263`) defines the cosine of an angle between vectors which can be zero. This is already unavoidable in ID 5469: N is removed and its mean and radius are zero. The radius bounds, attainable-boundary argument and quotient formula remain valid.

For (mu_x=\rho_xd_x) with unit (d_x), choosing (d_x) freely at a zero radius, both identities

\[
\mu_f\cdot\mu_g=\rho_f\rho_g(d_f\cdot d_g),\qquad
|\mu_f+\mu_g|^2=\rho_f^2+\rho_g^2+2\rho_f\rho_g(d_f\cdot d_g)
\]

hold without division by a radius. If either radius vanishes, (a=0) and the scalar expression is constant in (t). If (mu_f+mu_g=0), minimization over the out-root direction still gives zero for that dot product. The denominator is always at least (4/5), so no new degeneracy enters the ratio or its quadratic test.

As a check on the underlying argument, I rederived the single-site numerator and denominator from second/fourth moments. The subset proof uses positive rank factors (1,1,4/3,2), whose successive ratios (1,4/3,3/2) are increasing; the asserted decreasing (L_T) condition reduces to ((1-t)^2\ge0). Thus the FKG step in the radius bound introduces no zero-radius division; its endpoints follow by continuity as written. The flaw is the later angle notation.

```bash
PYTHONDONTWRITEBYTECODE=1 python3 audit_math.py > audit_math.log
```

```text
VALUE pid 5469 radii {'(1, 0)': '169/385', '(-1, 0)': '169/385'} exact 416114/444675 attained at t=1; test at value PASS; value+1e-12 FAIL
```

The omitted N entry in this root-radius dictionary means N is removed and its radius is zero. The direct evaluation is (1-(169/385)^2/3=416114/444675), exactly as claimed.

**Correction.**
''')
correction(['E08'])
put(r'''
**Consequences elsewhere.** No change to Proposition D.9's statement, its scalar criterion, `closed_exact.py`, the three exact fractions, or Remark 8.4 is needed. The normalization convention at zero is all that changes.
''')

put(r'''
## FINDING 7: CONFIRMED

**Evidence and independent count.** The stored `sectors` diagnostics and the matrices actually tested are different things. `cert.py:333–348` encodes diluted-corner exchange signs in the sector label and chooses a central spin-component sector for each sign assignment. `:434–447` tests those separately. `verify_all.py` does not use the saved `sectors` diagnostics to assemble or select blocks.

I reconstructed the groups from the graph and the selected representation and counted the weights directly. A single vector has doubled spin weights (1,-1); a symmetric pair has (2,0,-2); an antisymmetric pair has weight 0. For (s) singles and (p) symmetric pairs, the central dimension is the coefficient of (z^{s\bmod2}) in

\[
(z+z^{-1})^s(z^2+1+z^{-2})^p.
\]

Looping over all D-pair exchange signs and all 7,962 selected certificates gives the following exact integer counts, independently of operator entries or floating eigenvalues:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 audit_math.py > audit_math.log
```

```text
BLOCK pid 711 split dimensions [179, 66, 66, 25, 66, 25, 25, 10] stored [10, 25, 25, 25, 66, 66, 66, 179]
BLOCK pid 3596 split dimensions [131, 48, 48, 18] stored [245]
BLOCK pid 7725 split dimensions [131, 48, 48, 18] stored [18, 48, 48, 131]
BLOCK max selected: 179 central exchange blocks: 12173 combined diagnostics: 141
```

For ID 3596, (131+48+48+18=245); the stored dimension combines the four exchange blocks. There are 141 records whose historical diagnostics use this combined convention, and my script verifies that every such dimension is the sum of the current split dimensions. The current largest individual block is **179**, attained, for example, at ID 711. This finding concerns the asserted maximum and stale diagnostics, not invalid positivity tests.

**Minimal correction.** Only the exact-largest-size clause needs to change; the already true upper bounds need not be tightened.
''')
correction(['E05'])
put(r'''
**Consequences elsewhere.** The bounds “at most 245” at `sec8-computer-assisted.tex:59,71` and `app-local.tex:290` remain true and are retained to minimize edits. The basis construction at `app-local.tex:188–192` is already the split construction and needs no amendment. No replacement of certificate choices, proofs or stored data is required; the obsolete diagnostic fields are not proof inputs.
''')

put(r'''
All mathematical labels, theorem numbers and constants are retained. No edit to the main theorem, (H1)'s thresholds, (H2), or (H3′) is required.

Validation of the proposed replacements:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 prepare_edits.py
cd proposed-manuscript
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The 25 exact replacements apply without overlap or missing targets; the local preview compiles successfully with resolved references. The frozen inputs are unchanged.

## Consolidated manuscript edits in file order

The following order follows the `\input` order in `main.tex`, and then increasing frozen-source line number. Fragments sharing an original line are disjoint and are applied cumulatively. The exact LaTeX replacements appear in the finding sections above and, with their exact original fragments, in `edits.json`.
''')
file_order = ['sec1-intro-statement.tex', 'sec6-walks.tex', 'sec8-computer-assisted.tex', 'app-constants.tex', 'app-local.tex']
for file in file_order:
    put(f"**`manuscript/{file}`**")
    for e in sorted((e for e in E if e['file'] == file), key=lambda e: (e['start'], e['id'])):
        put(f"- **{e['id']}**, lines {e['start']}–{e['end']}, finding {e['finding']}: {e['description']}")

Path('report.md').write_text('\n'.join(parts))
print('Wrote report.md:', len(E), 'edits,', len(Path('report.md').read_text().splitlines()), 'lines')
