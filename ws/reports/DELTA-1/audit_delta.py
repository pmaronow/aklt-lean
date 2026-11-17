"""Delta-specific structural and exact-arithmetic checks; all writes are local."""
from collections import Counter
from difflib import SequenceMatcher
from fractions import Fraction as F
from pathlib import Path
import csv
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = Path('/home/ubuntu/aklt/manuscript-corrected')
REPORTS = HERE.parent
ARCHIVE = Path('/home/ubuntu/aklt/source-full/agents')


def git(*args):
    return subprocess.check_output(['git', '-C', str(REPO), *args], text=True)


def structural():
    allowed = {}
    for report in ('ADJ-R4', 'ADJ-R6', 'ADJ-MINOR'):
        for edit in json.loads((REPORTS / report / 'edits.json').read_text()):
            start = edit.get('start', edit.get('first_line'))
            end = edit.get('end', edit.get('last_line'))
            allowed.setdefault(edit['file'], set()).update(range(start, end + 1))
    # ADJ-R5 gives the replacements in its report rather than edits.json.
    for filename, lines in {
        'sec6-walks.tex': [135, 138, 142, 149],
        'sec8-computer-assisted.tex': [3, 16, 33],
        # The trust paragraph at 125 must refer to the support-aware audit
        # implementations once the original sources are distinguished at 121.
        'app-tail.tex': [76, 90, 114, 119, 121, 123, 125, 128],
    }.items():
        allowed.setdefault(filename, set()).update(lines)
    names = git('diff', '--name-only', '32487a2', '9222abe').splitlines()
    unexpected = []
    for filename in names:
        assert filename in allowed, filename
        old = git('show', '32487a2:' + filename).splitlines()
        new = git('show', '9222abe:' + filename).splitlines()
        assert '\n'.join(new) + '\n' == (HERE / 'build' / filename).read_text()
        for tag, i, j, a, b in SequenceMatcher(None, old, new, autojunk=False).get_opcodes():
            if tag in ('replace', 'delete'):
                unexpected.extend((filename, n) for n in range(i + 1, j + 1)
                                  if n not in allowed[filename])
    assert not unexpected, unexpected
    print('SCOPE: all changed frozen source lines lie in adjudicated correction ranges;', len(names), 'files')

    # Check the exact first checkpoint before the later shared wording merges.
    r4 = {}
    for e in json.loads((REPORTS / 'ADJ-R4/edits.json').read_text()):
        r4.setdefault(e['file'], []).append(e)
    for filename, edits in r4.items():
        lines = git('show', '32487a2:' + filename).splitlines(keepends=True)
        for e in sorted(edits, key=lambda x: x['start'], reverse=True):
            lines[e['start'] - 1:e['end']] = e['replacement'].splitlines(keepends=True)
        assert ''.join(lines) == git('show', 'ade1a62:' + filename)
    print('ADJ-R4 checkpoint: byte-for-byte implementation of all 16 prescribed edits')

    def source_snapshot(folder):
        text = '\n'.join(p.read_text() for p in sorted(folder.glob('*.tex')))
        labels = re.findall(r'\\label\{([^}]+)\}', text)
        env = Counter(re.findall(r'\\begin\{(theorem|lemma|proposition|corollary|definition|hypothesis|remark|equation)\}', text))
        theorems = re.findall(r'\\begin\{theorem\}.*?\\end\{theorem\}', text, re.S)
        return text, labels, env, theorems
    old, oldlabels, oldenv, oldtheorems = source_snapshot(HERE / 'frozen')
    new, newlabels, newenv, newtheorems = source_snapshot(HERE / 'build')
    assert oldlabels == newlabels and len(set(newlabels)) == len(newlabels)
    assert oldenv == newenv
    assert oldtheorems == newtheorems
    assert not (set(re.findall(r'\\(?:eq)?ref\{([^}]+)\}', new)) - set(newlabels))
    for label in ('e:kernel', 'e:recineq', 'e:FX', 'e:P', 'e:H'):
        pattern = r'\\begin\{equation\}\\label\{' + re.escape(label) + r'\}.*?\\end\{equation\}'
        assert re.search(pattern, old, re.S)[0] == re.search(pattern, new, re.S)[0]
    def compiled_labels(folder):
        return dict(re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}', (folder / 'main.aux').read_text()))
    oldcompiled = compiled_labels(HERE / 'frozen')
    newcompiled = compiled_labels(HERE / 'build')
    assert oldcompiled == newcompiled
    print('LABELS:', len(newlabels), 'source labels and', len(newcompiled), 'compiled numbers preserved')
    print('NUMBERED ENVIRONMENTS:', dict(newenv))
    print('THEOREMS:', len(newtheorems), 'theorem environments unchanged byte-for-byte')
    print('UNCHANGED DISPLAYS: Hamiltonian, response envelopes, (P), kernel and recursion including C_T')
    log = (HERE / 'build/main.log').read_text()
    assert not re.search(r'undefined|Rerun to get|LaTeX Error|Emergency stop', log, re.I)
    for directory in ('frozen', 'build'):
        log = (HERE / directory / 'main.log').read_text()
        warnings = re.findall(r'Overfull \\hbox \(([^)]+)\)', log)
        pages = re.search(r'Output written on main.pdf \((\d+) pages', log)[1]
        print('BUILD:', directory, 'pages=', pages, 'overfull widths=', warnings)


def h2():
    data = (HERE / 'evidence/audit/h2_integer_certificate.tsv').read_bytes()
    assert data == (REPORTS / 'ADJ-R5/audit/h2_integer_certificate.tsv').read_bytes()
    h, terms = {}, {}
    for line in data.decode().splitlines():
        cells = line.split()
        if cells[0] == 'h':
            code, val = map(int, cells[1:])
            h[code] = val
            terms.setdefault(code, [])
        elif cells[0] == 'S':
            code, s, t, r, val = map(int, cells[1:])
            assert s + t + r == 8
            terms.setdefault(code, []).append((s, t, r, val))
    assert len(h) == len(terms) == 938 and min(h.values()) > 0
    rate = F(3923, 4000)
    lam = max(sum((val * F(1000, 2883)**s * F(200, 561)**t / 4**r
                   for s, t, r, val in terms[code]), F(0)) / value for code, value in h.items())
    assert F(max(h.values()), min(h.values())) == 100
    assert lam <= F('.8559487104') < F('.85594872') < rate**8
    totals = [F(0) for _ in range(16)]
    for row in csv.DictReader((HERE / 'evidence/audit/trails_integer.csv').open()):
        n, s, t = (int(row[k]) for k in ('n', 's', 't'))
        totals[n] += int(row['forbid']) * F(1000, 2883)**s * F(200, 561)**t / 5**(n-s-t)
    initial = max(totals[n] / rate**n for n in range(8))
    base = max(totals[n] / rate**n for n in range(8, 16))
    assert initial < F('1.473') and base < F('1.506') and max(initial, 100*base) < 153
    print('H2: fresh sanitizer run regenerates archived certificate exactly')
    print('H2 exact lambda =', lam)
    print('H2: q=.98075, positive vector ratio=100, both stated base bounds, and C_V<=153: PASS')


def tail():
    hc = F(2769713770832855, 2251799813685248)
    def read(path):
        records = {}
        content = path.read_text()
        for tag, n, x in re.findall(r'^([EDF]) (\d+) (\S+)$', content, re.M):
            assert (tag, int(n)) not in records
            records[tag, int(n)] = F(x)
        match = re.search(r'remainder<=([\d.eE+-]+)', content)
        return records, F(match[1]) if match else F(0)
    def assemble(folder, prefix_a, prefix_b, divisor):
        out = {}
        for row in ('B', 'C'):
            components = [F(0)] * 5
            for direction, mult in ((1, 2), (2, 1)) if row == 'B' else ((1, 1), (2, 1), (3, 1)):
                values, _ = read(folder / f'{prefix_a}_{row}_{direction}.txt')
                assert {n for tag, n in values if tag == 'D'} == set(range(22, 109, 2))
                components[0] += mult * sum(v for (tag, n), v in values.items() if tag == 'E' and n <= 20)
                components[1] += mult * values['D', 22]
                components[2] += mult * sum(values['D', n] for n in range(24, 107, 2))
            values, remainder = read(folder / f'{prefix_b}_{row}.txt')
            assert {n for tag, n in values if tag == 'F'} == set(range(54, 261, 2))
            components[3] = sum(values['F', n] for n in range(108, 261, 2))
            components[4] = remainder
            total = sum(components)
            out[row] = components + [total, total / (1 if row == 'B' else divisor)]
        return out
    new = assemble(ARCHIVE / '75-audit-tail/out/rerun', 'r961A', 'r961B', hc)
    old = assemble(ARCHIVE / '62-kernel-tail/out', 's961A', 's961B', hc)
    typed = assemble(ARCHIVE / '62-kernel-tail/out', 'c961_935_A', 'c961_935_B', F.from_float(1.2))
    table = {'B': ['.594580', '.026669', '.302932', '.057384', '.006199', '.987763', '.987763'],
             'C': ['.841681', '.022644', '.268029', '.053319', '.005737', '1.191407', '.968624']}
    for row in ('B', 'C'):
        assert all(v <= F(upper) and v > F(upper)-F(1, 10**6) for v, upper in zip(new[row], table[row]))
    assert new['B'][-2] == F('.987762443170525')
    assert new['C'][-2] == F('1.1914067844431')
    assert old['B'][-1] <= F('.987731') and old['C'][-1] <= F('.968592')
    assert F('.987731') * F('.18094') / F('.18093') < F('.98779')
    assert typed['B'][-2] == F('.913009554182608') and typed['C'][-1] < F('.918245584')
    ratios = []
    for row in ('B', 'C'):
        for suffix in [f'A_{row}_{d}' for d in ((1, 2) if row == 'B' else (1, 2, 3))] + [f'B_{row}']:
            a, _ = read(ARCHIVE / f'75-audit-tail/out/rerun/r961{suffix}.txt')
            b, _ = read(ARCHIVE / f'62-kernel-tail/out/s961{suffix}.txt')
            assert a.keys() == b.keys()
            ratios.extend(a[key] / b[key] for key in a)
    assert min(ratios) >= F('1.0000322') and max(ratios) <= F('1.0000333')
    print('TAIL: independent exact assembly verifies all 14 table entries and all amended comparison/optional bounds')
    print('TAIL corrected totals:', new['B'][-2], new['C'][-2])
    print('TAIL comparison interval [1.0000322,1.0000333]: PASS')


def elementary():
    # Positive-degree D moments are 3/5 of uniform moments.  The two-bond
    # denominator is >=4/5; its trace removes the site and adds mass 3/5.
    assert F(3, 5) / F(4, 5) == F(3, 4)
    assert F(3, 4) / 3 == F(1, 4) <= F(1, 3)
    assert sum(abs(x)+abs(y) in (1, 2) for x in range(-2, 3) for y in range(-2, 3)) == 12
    u = F(1, 2**53)
    eta = (1-u)**2 * (1 - 32*u/(1-32*u))
    assert eta > 1 - F(1, 10**12) > F(3, 4)
    assert 3 * 2**61 / eta < 2**63 and 2**58 / eta < 2**59
    assert F(1, 1) / F('.82') < F('1.22')
    assert F(2, 1) / F('.734') < F('2.73')
    assert F('.7776') / (15 * F('.734')) < F('.0707')
    # The signed-depth near-side comparison at the worst allowed j is s/6>l0/2.
    assert F(1, 3) - 2*F(1, 12) == F(1, 6)
    print('ELEMENTARY: initial D bound, twelve exceptions, shadow margins, removal constants, signed-depth margin: PASS')


if __name__ == '__main__':
    structural()
    h2()
    tail()
    elementary()
    print('ALL DELTA-SPECIFIC CHECKS PASSED')
