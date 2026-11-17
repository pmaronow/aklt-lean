"""Validate exact checks and compile isolated before/after review copies."""
from collections import Counter
from pathlib import Path
import difflib
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
SOURCE = Path('/home/ubuntu/aklt/manuscript/bundle/manuscript')


def run():
    subprocess.run([sys.executable, '-B', 'build_report.py'], cwd=HERE, check=True)
    edits = json.loads((HERE / 'edits.json').read_text())
    originals = {p.name: p.read_text() for p in SOURCE.glob('*.tex')}
    hashes = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in SOURCE.glob('*.tex')}
    patched = dict(originals)
    diff = []
    for name in sorted({e['file'] for e in edits}):
        relevant = sorted((e for e in edits if e['file'] == name), key=lambda e: e['start'])
        lines = originals[name].splitlines(keepends=True)
        pieces = []
        position = 0
        for e in relevant:
            assert e['start'] - 1 >= position, f"Overlapping edit: {e['id']}"
            assert e['end'] <= len(lines)
            pieces.extend(lines[position:e['start']-1])
            pieces.append(e['replacement'])
            position = e['end']
        pieces.extend(lines[position:])
        patched[name] = ''.join(pieces)
        assert Counter(re.findall(r'\\label\{([^}]+)\}', originals[name])) == Counter(
            re.findall(r'\\label\{([^}]+)\}', patched[name]))
        numbered = ('theorem', 'proposition', 'lemma', 'definition', 'hypothesis', 'remark',
                    'corollary', 'equation')
        for env in numbered:
            assert originals[name].count('\\begin{' + env + '}') == patched[name].count('\\begin{' + env + '}')
        diff.extend(difflib.unified_diff(originals[name].splitlines(keepends=True),
                                        patched[name].splitlines(keepends=True),
                                        fromfile='frozen/' + name, tofile='review/' + name))
    (HERE / 'manuscript-edits.diff').write_text(''.join(diff))
    print(f"{len(edits)} disjoint edits; source labels and numbered environments preserved.", flush=True)

    for name, content in (('baseline', originals), ('review', patched)):
        destination = HERE / name
        destination.mkdir(exist_ok=True)
        for filename, text in content.items():
            (destination / filename).write_text(text)
        for pass_no in (1, 2, 3):
            process = subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                                      '-file-line-error', 'main.tex'], cwd=destination,
                                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            (destination / f'pdflatex-pass{pass_no}.out').write_text(process.stdout)
            if process.returncode:
                print(process.stdout[-5000:], flush=True)
            assert process.returncode == 0, f"pdflatex failed: {name}, pass {pass_no}"
        assert 'Label(s) may have changed' not in process.stdout
        assert 'undefined references' not in process.stdout
        print(f"{name}: pdflatex passed three times; cross-references settled.", flush=True)
    label_pattern = r'\\newlabel\{([^}]+)\}\{\{([^}]*)\}'
    old_labels = dict(re.findall(label_pattern, (HERE / 'baseline/main.aux').read_text()))
    new_labels = dict(re.findall(label_pattern, (HERE / 'review/main.aux').read_text()))
    assert old_labels == new_labels
    print(f"All {len(old_labels)} compiled label numbers agree (page numbers may change).", flush=True)

    with (HERE / 'check_adj_r4.out').open('w') as output:
        subprocess.run([sys.executable, '-B', 'check_adj_r4.py'], cwd=HERE, stdout=output, check=True)
    print("Independent exact checker: PASS (including class-by-class pattern equality).", flush=True)
    with (HERE / 'check_r4.out').open('w') as output:
        subprocess.run([sys.executable, '-B', '/home/ubuntu/aklt/referee/REF-R4/check_r4.py'],
                       cwd=HERE, stdout=output, check=True)
    print("Supplied referee checker: PASS.", flush=True)
    after = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in SOURCE.glob('*.tex')}
    assert hashes == after
    print("Frozen LaTeX inputs unchanged (SHA-256 comparison).", flush=True)
    print("All validation checks passed.", flush=True)


if __name__ == '__main__':
    run()
