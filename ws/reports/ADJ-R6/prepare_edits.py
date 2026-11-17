"""Produce reviewable minimal LaTeX replacements and a local compile preview.

The frozen inputs are read only. Original line numbers in edits.json refer to
the frozen sources. Each replacement operates on the exact quoted fragment.
"""
import json
import re
from pathlib import Path

ROOT = Path('/home/ubuntu/aklt/manuscript/bundle/manuscript')
edits = []


def add(eid, finding, file, start, end, old, new, description):
    source = (ROOT/file).read_text()
    assert source.count(old) == 1, (eid, source.count(old))
    line = source[:source.index(old)].count('\n')+1
    assert start <= line <= end, (eid, line)
    new = re.sub(r'\\texttt\{([^{}]+)\}',
                 lambda m: r'\texttt{' + m[1].replace('/', r'/\allowbreak ').replace(r'\_', r'\_\allowbreak ') + '}', new)
    edits.append(dict(id=eid, finding=finding, file=file, start=start, end=end,
                      description=description, old=old, new=new))


add('E00', 3, 'sec1-intro-statement.tex', 18, 18,
    'the smallest margins are',
    r'the margins on the first two patterns of Table~\ref{tab:H1}, which have the smallest values found numerically, are',
    'Qualify the global smallest-margin claim in the introduction.')

file = 'sec6-walks.tex'
line108 = (ROOT/file).read_text().splitlines()[107]
new108 = line108.replace(
    r'The class $\Pext$ consists of the patterns in which:',
    r'The class $\Pext$ consists of the patterns in which: $y$ keeps exactly its three bonds other than $\{y,\mathsf s\}$; every other site of status $\mathrm U$ keeps all four of its lattice bonds;')
new108 = new108.replace(
    r'A pattern is straight or a turn according to $o$.',
    r'The two outside legs of each non-removed corner are filled with slots, whether or not they belong to its kept set. A pattern is straight or a turn according to $o$.')
add('E01', 1, file, 108, 108, line108, new108, 'Replace the paragraph defining the class, including the existing tip exception.')

file = 'sec8-computer-assisted.tex'
add('E02', 3, file, 66, 66, 'tightest straight &', 'straight (ID 7645) &', 'Replace only the first table-cell text; retain the remainder of the row.')
add('E03', 3, file, 67, 67, 'tightest turn &', 'turn (ID 1382) &', 'Replace only the first table-cell text; retain the remainder of the row.')
add('E04', 3, file, 73, 73,
    r'The hardest patterns of $\Pext$, which has $2{,}696$ straight patterns and $5{,}266$ turns.',
    r'Selected patterns of $\Pext$, which has $2{,}696$ straight patterns and $5{,}266$ turns. The first two rows give the smallest values found numerically in the straight and turning classes; global optimality is not certified.',
    'Replace the opening caption sentence with these two sentences; keep the caption label and the rest.')
add('E05', 7, file, 73, 73,
    r'The largest of these matrices has size $245 \times 245$,',
    r'With the exchange signs split as in \eqref{e:Meps}, the largest tested matrix has size $179 \times 179$,',
    'Replace this caption clause; retain its following clause about production time.')
add('E06', 3, file, 77, 77,
    r'The margins of Theorem~\ref{t:H1} on the two tightest patterns are',
    r'The margins of Theorem~\ref{t:H1} on the first two patterns of Table~\ref{tab:H1} are',
    'Replace this phrase in Remark 8.4; retain its numerical margins and upper-bound argument.')

file = 'app-local.tex'
add('E07', 3, file, 196, 196,
    r'and the exact values of $c(\pi)$ for the tightest patterns.',
    r'and the exact values of $c(\pi)$ for the first three patterns of Table~\ref{tab:H1}.',
    'Replace the final phrase of the second sentence.')
old263 = (ROOT/file).read_text().splitlines()[262]
new263 = r'''For fixed $\mu_f, \mu_g$, the minimum over $|\mu_o| = \rho_o$ of $\mu_o \cdot (\mu_f + \mu_g)$ is $-\rho_o |\mu_f + \mu_g|$. Write $\mu_x = \rho_x d_x$ for $x \in \{f,g\}$, with $d_x$ a unit vector chosen arbitrarily when $\rho_x = 0$, and put $t = d_f \cdot d_g$. Then $\mu_f \cdot \mu_g = at$ and $|\mu_f + \mu_g|^2 = \rho_f^2 + \rho_g^2 + 2at$; every $t \in [-1,1]$ occurs in this parametrization. Minimizing over $t$, we obtain \eqref{e:closed}.'''
add('E08', 6, file, 263, 263, old263, new263, 'Replace the angle-parametrization paragraph of the proof of Proposition D.9.')
add('E09', 3, file, 270, 270,
    'among them the three tightest patterns of the class.',
    'including the three examples below.',
    'Replace the concluding phrase of the first sentence.')
add('E10', 3, file, 272, 272,
    r'\item The tightest straight pattern:',
    r'\item The straight pattern in the first row of Table~\ref{tab:H1}:',
    'Replace the item introduction; retain its statuses, radii, and value.')
add('E11', 3, file, 273, 273,
    r'\item The tightest turn ($o = \mathsf e$):',
    r'\item The turn in the second row of Table~\ref{tab:H1} ($o = \mathsf e$):',
    'Replace the item introduction; retain its statuses, radii, and value.')
add('E12', 4, file, 282, 282,
    r'A second enumeration, written independently from Definition~\ref{d:pattern}, finds $106{,}101$ configurations that satisfy the rules and the same $7{,}962$ classes, $2{,}696$ straight and $5{,}266$ turns, class by class.',
    r'''A second enumeration, written independently from Definition~\ref{d:pattern}, counts $106{,}101$ consistent site assignments before choosing an out-neighbour, distinguishing the choices of outside corner legs, and obtains the same $7{,}962$ classes, $2{,}696$ straight and $5{,}266$ turns, class by class. Its program and output are \texttt{72-audit-H1-certificates/code/enum\_pext.py} and \texttt{72-audit-H1-certificates/out/enum\_pext.txt}, relative to \texttt{agents/} in the full project archive. The additional validation files identified below are also in that archive and are absent from the frozen program bundle.''',
    'Replace the second-enumeration sentence and add the archive location and bundle-scope statement.')
add('E13', 2, file, 282, 282,
    r'In the representations of \S\ref{s:localred}, the number of vectors is $k \le 11$.',
    r'The reduced representation of \S\ref{s:localred} always has $k \le 11$. The unreduced representation can have $k = 12$, but every representation selected in the two certificate files has $k \le 11$.',
    'Replace the last sentence of the paragraph.')
add('E14', 5, file, 284, 284,
    r'The contraction is carried out in $64$-bit integer arithmetic, with run-time assertions that every entry stays below $2^{61}$.',
    r'''The contraction is carried out in $64$-bit integer arithmetic, with binary64 shadow computations used for conservative overflow guards. The small integer moment tensors are first stored exactly in binary64 arrays and then converted to integers. Assume binary64 round-to-nearest arithmetic, let $u=2^{-53}$, $\gamma_{32}=32u/(1-32u)$, and $\eta=(1-u)^2(1-\gamma_{32})>1-10^{-12}>3/4$. Each contracted entry is a sum of at most sixteen nonnegative products, so its shadow $\widehat s$ and exact value $s$ satisfy $\widehat s\ge\eta s$ (two input conversions and at most thirty-two arithmetic roundings suffice). Thus a passing shadow guard $\widehat s<2^{61}$ implies $s<2^{61}/\eta$, and a sum of three such contraction entries is smaller than $2^{63}$. The subsequent shadow bounds for the current and next coefficient sums are computed from these nonnegative integer arrays; their passing threshold $2^{58}$ implies exact sums smaller than $2^{58}/\eta<2^{59}$. Consequently every accepted coefficient computation is free of integer overflow, including its intermediate sums.''',
    'Replace the contraction/overflow sentence by the arithmetic justification.')
add('E15', 5, file, 286, 286,
    'Floating-point arithmetic is used only for this choice.',
    'Floating-point arithmetic is used for this choice, for the conservative overflow guards just described, and for diagnostics. Positivity is decided in unbounded integer arithmetic, and the closed-form tests use exact rational arithmetic.',
    'Replace the restriction on floating-point use.')
old292 = (ROOT/file).read_text().splitlines()[291]
add('E16', 4, file, 292, 292, old292,
    r'''\item An independent evaluator keeps the passage site, tips and corners as spins and compares the ratio $Z_{\mathrm{cur}}/Z_{\mathrm{next}}$ with the ratio obtained from the integer coefficients, at three random points with untied slot vectors for every pattern. There are $23{,}893$ comparisons, including seven additional zero-slot cases, and the largest observed relative discrepancy is less than $2.4\cdot10^{-15}$. The programs are \texttt{72-audit-H1-certificates/code/brute.py} and \texttt{xcheck\_brute.py} in the same directory; the output is \texttt{72-audit-H1-certificates/out/xcheck\_brute\_all.json}.''',
    'Replace check (1), stating that the archived comparison concerns ratios.')
old293 = (ROOT/file).read_text().splitlines()[292]
add('E17', 4, file, 293, 293, old293,
    r'''\item For all $7{,}962$ certificates, the integer matrices commute exactly with the total spin operators in the basis of \S\ref{s:inversion}; see \texttt{72-audit-H1-certificates/code/su2check.py} and \texttt{72-audit-H1-certificates/out/su2check\_all\_summary.json}. The archived output \texttt{72-audit-H1-certificates/out/unitpert.txt} records detection of a change by $1$ to a single non-constant coefficient of $3D\hat Z_{\mathrm{cur}}$ in all $30$ trials; its generating driver is not archived.''',
    'Replace check (2), distinguishing the commutator program from the mutation output without a driver.')
add('E18', 4, file, 295, 295,
    r'exceeds the closed form \eqref{e:closed} by at most $2.4 \cdot 10^{-15}$',
    r'exceeds the closed form \eqref{e:closed} by at most $2.5 \cdot 10^{-15}$',
    'Round the archived maximum 2.4424906541753444e-15 upward in check (4).')
old296 = (ROOT/file).read_text().splitlines()[295]
add('E19', 3, file, 296, 296, old296,
    r'''\item The stored certificates of the three closed-form examples above are rejected at thresholds obtained by adding $2\cdot10^{-5}$ to the numerical minimum and rounding upward to a multiple of $10^{-5}$; see \texttt{72-audit-H1-certificates/code/negctl.py} and \texttt{72-audit-H1-certificates/out/negctl\_hard.json}.''',
    'Replace check (5), removing the global ranking and specifying the archived threshold convention (also Finding 4).')
add('E20', 4, file, 298, 298,
    'A second implementation, written independently of the programs above, re-verifies the certificates of both files.',
    r'A second implementation, in \texttt{73-reimplement-H1/code/wick.py}, \texttt{opcert.py}, \texttt{run\_opall.py}, \texttt{closed.py}, \texttt{run\_k1.py}, \texttt{numeval.py} and \texttt{run\_k1b.py} in the same directory, re-verifies the certificates of both files independently of the programs above.',
    'Replace the introductory sentence identifying the independent implementation.')
add('E21', 4, file, 298, 298,
    'and never goes below it.',
    r'and never goes below it. The corresponding outputs are \texttt{operator\_only\_results.jsonl}, \texttt{k1\_exact.jsonl}, \texttt{k1b\_numerics.jsonl} and \texttt{summary.txt} under \texttt{73-reimplement-H1/out/}.',
    'Append the archived output locations to the independent-implementation paragraph.')
add('E22', 4, file, 300, 300,
    r'The fraction-free elimination (about $20$ lines) agrees with an exact $LDL^{\mathsf T}$ decomposition on $600$ random symmetric test matrices.',
    r'The fraction-free elimination (about $20$ lines) agrees with an exact $LDL^{\mathsf T}$ decomposition on $600$ random symmetric test matrices; the test is \texttt{72-audit-H1-certificates/code/test\_bareiss72.py}, and its result is recorded in \texttt{72-audit-H1-certificates/NOTES.md} and \texttt{LOG.md} in that directory.',
    'Add the location of the actual 600-case LDL test and its recorded result.')
add('E23', 5, file, 300, 300,
    'Since overflow is excluded by run-time assertions,',
    'The binary64 error bounds above and the run-time assertions exclude overflow for accepted certificates; therefore',
    'Replace this trust-statement clause; retain the requirements on assertions and the tip radius.')

file = 'app-constants.tex'
old17 = (ROOT/file).read_text().splitlines()[16]
new17 = old17.replace(r'$\min_\pi c(\pi)$', r'two displayed $c(\pi)$').replace(
    r'straight, turn; closed forms (\S\ref{s:closed})',
    r'straight, turn; exact values for the first two rows of Table~\ref{tab:H1} (\S\ref{s:closed})')
add('E24', 3, file, 17, 17, old17, new17, 'Replace the constants-table row without asserting minima over the classes.')

Path('edits.json').write_text(json.dumps(edits, indent=2)+'\n')
preview = Path('proposed-manuscript')
preview.mkdir(exist_ok=True)
for p in ROOT.glob('*.tex'):
    text = p.read_text()
    for e in edits:
        if e['file'] == p.name:
            assert text.count(e['old']) == 1, e['id']
            text = text.replace(e['old'], e['new'])
    (preview/p.name).write_text(text)
print('Prepared', len(edits), 'non-overlapping exact replacements in edits.json; frozen inputs unchanged.')
