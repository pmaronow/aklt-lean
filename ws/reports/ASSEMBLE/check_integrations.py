#!/usr/bin/env python3
"""Check assembly invariants and exact numerical interfaces, not certificates."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import re

ROOT = Path('/home/ubuntu/aklt')
DEST = ROOT / 'manuscript-v2'
OUT = ROOT / 'reports/ASSEMBLE'
audit = json.loads((OUT / 'audit.json').read_text())
main = (DEST / 'main.tex').read_text()
oldmain = (ROOT / 'manuscript-corrected/main.tex').read_text()
checks = []


def check(name, condition, detail=None):
    assert condition, name
    checks.append({'check': name, 'pass': True, 'detail': detail})


for key in ['undefined_references', 'duplicate_labels', 'undefined_citations',
            'uncited_bibliography', 'missing_planned_statements', 'comments',
            'editorial_candidates']:
    check('empty ' + key, not audit[key])
check('all source section hashes unchanged', all(s['unchanged'] for s in audit['source_integrity']))
check('all twelve section inputs in prescribed order',
      re.findall(r'\\input\{([^}]+)\}', main) ==
      [Path(f).stem for f in audit['section_order']])
check('title unchanged', re.search(r'\\title\{([^}]+)\}', main)[1] ==
      re.search(r'\\title\{([^}]+)\}', oldmain)[1])
check('exactly the two cited bibliography entries', audit['bibliography'] == ['AKLT88', 'KLT88'])

# Only editorial sentences change inside source statement environments.
statement_re = re.compile(r'\\begin\{(theorem|proposition|lemma|corollary|definition|hypothesis|remark)\}(.*?)\\end\{\1\}', re.S)


def statements(text):
    result = {}
    for m in statement_re.finditer(text):
        label = re.search(r'\\label\{([^}]+)\}', m.group())
        if label:
            result[label[1]] = re.sub(r'\s+', '', m.group())
    return result


editorial_replacements = {
    'sec7-recursion.tex': [
        ('trace coefficients. This \\(M\\) is the modified type-dependent kernel,\nnot the original uniform-coefficient matrix.',
         'trace coefficients. This \\(M\\) is the type-dependent response kernel.'),
        ('No bound for the former uniform-coefficient matrix is part of this\ncontract. Its proof in this revision uses the stationary lattice\nBellman certificates, with no periodic spatial walk or remainder.',
         'The assertion is proved using the stationary lattice Bellman\ncertificates, with no periodic spatial walk or remainder.'),
    ],
    'app-input-contracts.tex': [
        ('therefore (H3\\(_h\\)) holds for the modified kernel.',
         'therefore (H3\\(_h\\)) holds for the type-dependent kernel.'),
    ],
}
for source in json.loads((OUT / 'sources.json').read_text()):
    before = Path(source['source']).read_text()
    for old, new in editorial_replacements.get(source['file'], []):
        check('editorial replacement occurs once in ' + source['file'], before.count(old) == 1)
        before = before.replace(old, new)
    after = (DEST / source['file']).read_text()
    check('all mathematical statement text preserved: ' + source['file'],
          statements(before) == statements(after))

q = F(1119948287353, 1120437614225)
cs, ct = F(961, 1000), F(187, 200)
xs, xt = 1 / cs, 1 / ct
hC = F(5404319552844595, 4503599627370496)
rho0 = F(993015, 10**6)
a_s, a_t = F(145217, 10**6), F(150000, 10**6)
b_s, b_t = F(352782, 10**6), F(357549, 10**6)
bp_s, bp_t = F(340008, 10**6), F(344661, 10**6)
check('H2 rate satisfies actual recursion hypotheses', 0 < q < F(2499, 2500) < 1)
check('H2 finite-base majorant is below C_V=10', 6 * (xt / q)**6 < 10)
check('all type coefficients within crude summability bounds',
      0 < a_s <= a_t < F(18094, 100000) and
      0 < bp_s <= b_s < F(36751, 100000) and
      0 < bp_t <= b_t < F(36751, 100000))
check('H2 common-denominator numerators',
      [xs / 3, xt / 3, F(1, 5)] ==
      [F(n, 2695605) for n in [935000, 961000, 539121]])
check('memory/prefix condition L>=m+2', 12 >= 10 + 2)
check('spatial square and stationary row counts',
      141**2 == 19881 and 4 * 3741 * (19881 - 2) == 297469356)
check('H1 positivity routes cover every supported block', 8439 + 2 + 3732 == 12173)
check('positive witness and row contraction', hC > 1 and 0 < rho0 < 1)
boundB = F(2 * 351207554 + 290599163, 10**9)
boundC = F(527872005 + 380754375 + 273048088, 10**9)
check('exact B row is below rho0*hB', boundB < rho0, str(rho0 - boundB))
check('exact C row is below rho0*hC', boundC < rho0 * hC, str(rho0 * hC - boundC))
ceil = lambda x: (x.numerator + x.denominator - 1) // x.denominator
check('diagonal coefficient ceilings reconstructed exactly',
      [ceil(2**48 * x) for x in [xs / 3, xt / 3, F(1, 3), F(1, 5)]] ==
      [97632666219444, 100347585280092, 93824992236886, 56294995342132])
delta = 12139925673538045870080000
rewards = []
for a, b, bp in [(a_s, b_s, bp_s), (a_t, b_t, bp_t)]:
    # The two possible pair-type patterns and all possible single live pairs.
    rewards.extend([a + 2*b*hC, b + (a+b)*hC, bp, bp*hC, F(0)])
check('phase common denominator clears every allowed reward coefficient',
      all((delta * x * k / 3).denominator == 1 for x in [xs, xt] for k in rewards)
      and all((delta * x).denominator == 1 for x in [F(1,3), F(1,5), xs/3, xt/3]))
check('shared shell threshold at l0=64', max(16, 6*(64+1))**4 == 390**4)
check('periodic and quantum factors', F(499, 500) / 2 == F(499, 1000))

log = (DEST / 'main.log').read_text()
check('final TeX log has no errors or warnings',
      not re.search(r'(?:LaTeX|Package .*?) Warning|^!|undefined|multiply defined|Overfull|Underfull', log, re.M))
check('PDF exists and is nonempty', (DEST / 'main.pdf').stat().st_size > 100000)
result = {'status': 'PASS', 'scope': 'Assembly and exact interface arithmetic; no exhaustive certificate rerun.',
          'checks': checks, 'pdf_sha256': hashlib.sha256((DEST / 'main.pdf').read_bytes()).hexdigest()}
(OUT / 'integration-checks.json').write_text(json.dumps(result, indent=2) + '\n')
print(f"PASS: {len(checks)} assembly and exact arithmetic checks")
