#!/usr/bin/env python3
"""Read-only evidence comparisons; all output stays in EDIT4_DELTA."""
from pathlib import Path
import ast
import collections
import difflib
import fractions
import gzip
import hashlib
import json
import re
import struct
import subprocess

OUT = Path(__file__).resolve().parent
PAPER = Path('/home/ubuntu/aklt/manuscript-v2')
REPO = Path('/home/ubuntu/aklt/repo')
REPORTS = Path('/home/ubuntu/aklt/reports')
ARCHIVE = Path('/home/ubuntu/aklt/compfeas')
H1 = Path('/home/ubuntu/aklt/data/h1')
CLOSE = Path('/home/ubuntu/aklt/wt/CLOSE_H3')


def sha(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def read_json(path):
    return json.loads(Path(path).read_text())


result = {}

# Replay the editor's literal replacements in memory, never execute edit4.py.
tree = ast.parse((REPORTS / 'EDIT_4/edit4.py').read_text())
edits = next(ast.literal_eval(n.value) for n in tree.body
             if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'EDITS' for t in n.targets))
pre = REPORTS / 'EDIT_4/pre-edit'
edit_info = {}
delta = []
math_re = re.compile(r'\\\(.*?\\\)|\\\[.*?\\\]|(?<!\\)\$(?:\\.|[^$])*?\$', re.S)
statement_re = re.compile(r'\\begin\{(theorem|proposition|lemma|corollary|hypothesis|definition)\}.*?\\end\{\1\}', re.S)
def normalize(text):
    text = re.sub(r'\\certpending\{[^}]*\}', '', text)
    text = re.sub(r'(?<!\\)%[^\n]*', '', text)
    return re.sub(r'\s+', ' ', text).strip()
for name, replacements in edits.items():
    before = (pre / name).read_text()
    actual = (PAPER / name).read_text()
    replay = before
    for old, new in replacements:
        assert replay.count(old) == 1, (name, old)
        replay = replay.replace(old, new)
    assert replay == actual, name
    without_status_paragraph = actual
    if name == 'sec8-inputs.tex':
        start = actual.index('Theorem~\\ref{t:main}, including the three inputs')
        end = actual.index('\n\nFor the local input', start)
        without_status_paragraph = actual[:start] + actual[end:]
    old_math = [normalize(m.group()) for m in math_re.finditer(before)]
    new_math = [normalize(m.group()) for m in math_re.finditer(without_status_paragraph)]
    assert old_math == new_math, ('math', name)
    old_stmts = [normalize(m.group()) for m in statement_re.finditer(before)]
    new_stmts = [normalize(m.group()) for m in statement_re.finditer(actual)]
    assert old_stmts == new_stmts, ('statements', name)
    edit_info[name] = dict(replacements=len(replacements), exact_editor_replay=True,
                           preexisting_math_segments_unchanged=len(old_math),
                           numbered_statements_unchanged=len(old_stmts))
    delta.extend(difflib.unified_diff(before.splitlines(True), actual.splitlines(True),
                 fromfile='pre-edit/' + name, tofile='current/' + name))
(OUT / 'edit4-only.diff').write_text(''.join(delta))
old_diff = (pre / 'working-tree.diff').read_text()
def diff_sections(text):
    return {m.group(1): m.group(0) for m in re.finditer(r'^diff --git a/(.*?) b/.*?\n.*?(?=^diff --git |\Z)', text, re.M | re.S)}
old_sections = diff_sections(old_diff)
new_diff = subprocess.check_output(['git', 'diff', '--', '*.tex'], cwd=PAPER, text=True)
new_sections = diff_sections(new_diff)
untouched = {}
for p in PAPER.glob('*.tex'):
    if p.name not in edits:
        assert old_sections.get(p.name, '') == new_sections.get(p.name, ''), p.name
        untouched[p.name] = 'same diff against HEAD as pre-edit snapshot'
result['edit_delta'] = dict(touched=edit_info, untouched=untouched,
                            pending_uses_removed=sum(len(re.findall(r'\\certpending\{', (pre / n).read_text())) for n in edits))

print('Edit-only comparison passed.', flush=True)

# Check all original pattern/choice values against the frozen H1 input chunks.
patterns_path = ARCHIVE / 'programs/data/pext/pext7962.json'
choices_path = ARCHIVE / 'programs/h1-local/out/certificates_covered_operator_only.jsonl'
patterns = read_json(patterns_path)
choices = {r['pid']: r for r in map(json.loads, choices_path.read_text().splitlines())}
small_hashes = {}
for name, source, copy in [('pext7962.json', patterns_path, H1 / 'inputs/pext7962.json'),
                           ('certificates_covered_operator_only.jsonl', choices_path, H1 / 'inputs/certificates_covered_operator_only.jsonl')]:
    assert source.read_bytes() == copy.read_bytes()
    bundle_copy = Path('/home/ubuntu/aklt/manuscript/bundle') / source.relative_to(ARCHIVE)
    assert source.read_bytes() == bundle_copy.read_bytes()
    small_hashes[name] = dict(sha256=sha(source), input_copy_equal=True, paper_bundle_copy_equal=True)
index = read_json(H1 / 'index.json')
receipt = {r['path']: r for r in read_json(REPORTS / 'CERT_H1/phase3/data-input-receipt.json')}
assert sha(H1 / 'index.json') == receipt[str(H1 / 'index.json')]['sha256']
counts = collections.Counter()
selected = {}
for chunk in index['chunks']:
    path = H1 / chunk['file']
    assert sha(path) == chunk['sha256'] == receipt[str(path)]['sha256']
    with gzip.open(path, 'rt') as stream:
        for line in stream:
            r = json.loads(line)
            pid = r['pid']; src = patterns[pid]; choice = choices[pid]
            assert src['pid'] == choice['pid'] == pid
            assert r['pattern']['out'] == src['out'] == choice['out']
            assert r['pattern']['present'] == sorted(sorted(b) for b in src['present'])
            for x, y, kind in r['pattern']['sites']:
                assert kind == src['kinds'].get(str((x, y)), 'x')
            assert r['threshold'] == list(map(int, choice['target'].split('/')))
            rep = r['representation']
            assert rep['inversion'] == choice['S'] and rep['leafred'] == choice['leafred'] and rep['nslots'] == choice['n']
            assert rep['model'] == choice['model'] == 'covered' and rep['tip_radius'] == [3, 5]
            counts['patterns'] += 1
            for block in r['blocks']:
                counts['blocks'] += 1
                counts['nonzero_Gram' if block['witness']['L_lt'] else 'zero_Gram'] += 1
                counts['max_dimension'] = max(counts['max_dimension'], block['n'])
            if pid in [5420, 7697]:
                selected[pid] = r
factors = {}
for pid in [5420, 7697]:
    path = ARCHIVE / f'data/h1_chol_{pid}_131.json'
    old = read_json(path)
    block = next(b for b in selected[pid]['blocks'] if b['n'] == 131)
    old_matrix_lt = [old['M'][i][j] for i in range(131) for j in range(i + 1)]
    old_factor_lt = [old['L'][i][j] for i in range(131) for j in range(i + 1)]
    assert all(old['M'][i][j] == old['M'][j][i] for i in range(131) for j in range(131))
    assert all(old['L'][i][j] == 0 for i in range(131) for j in range(i + 1, 131))
    assert block['M_lt'] == [old['gcd'] * v for v in old_matrix_lt]
    assert block['witness']['L_lt'] == old_factor_lt
    assert block['witness']['g'] == old['gcd'] == 1600
    assert block['witness']['d'] == old['shift_den'] == 1
    assert block['witness']['S'] == 2 ** old['precision'] == 1
    assert block['witness']['min_margin'] == 1600 * old['min_margin']
    factors[path.name] = dict(sha256=sha(path), matrix_entries_compared=131 * 131,
                             factor_entries_compared=len(old_factor_lt), factor_equal=True,
                             matrix_equal_after_scale_1600=True, witness_parameters_equal=True,
                             residual_minimum=block['witness']['min_margin'])
result['H1'] = dict(input_files=small_hashes, input_chunk_hashes_match_receipt=17,
                    archived_pattern_and_choice_values_compared=7962,
                    counts=dict(counts), archived_factors=factors)
print('All H1 inputs and both archived factors match.', flush=True)

# Recheck all 916 H2 integer literals against the 115 original orbit integers.
h2_path = ARCHIVE / 'data/h2_exact_m6k1_r5.json'
h2 = read_json(h2_path)
by_orbit = {r['code']: r['h'] for r in h2['rows']}
h2_source = REPO / 'AKLT/Cert/H2/Data.lean'
expanded = {int(c): int(v) for c, v in re.findall(r'if c == (\d+) then (\d+) else', h2_source.read_text())}
def raw_window(code):
    x, y = 0, 0; bonds = set()
    for i in range(6):
        dx, dy = [(1, 0), (0, 1), (-1, 0), (0, -1)][code // 4 ** i % 4]
        z = (x + dx, y + dy); edge = tuple(sorted(((x, y), z)))
        if edge in bonds:
            return False
        bonds.add(edge); x, y = z
    return True
def canonical(code):
    ds = [code // 4 ** i % 4 for i in range(6)]
    return min(sum(((eps * d + rot) % 4) * 4 ** i for i, d in enumerate(ds))
               for eps in [1, -1] for rot in range(4))
raw_codes = [c for c in range(4096) if raw_window(c)]
assert len(raw_codes) == len(expanded) == 916
assert {canonical(c) for c in raw_codes} == set(by_orbit) and len(by_orbit) == 115
assert all(expanded[c] == by_orbit[canonical(c)] for c in raw_codes)
result['H2'] = dict(archive_sha256=sha(h2_path), lean_source_sha256=sha(h2_source),
                    raw_codes=916, orbit_entries=115, all_values_equal=True,
                    minimum=min(expanded.values()), maximum=max(expanded.values()),
                    value_at_428=expanded[428])
print('All H2 witness values match.', flush=True)

# Compare H3's supplied graph in full and all cap entries; pin all five archives.
h3_receipts = read_json(REPORTS / 'CERT_H3/phase3/production-inputs.json')
h3_manifest = read_json(REPORTS / 'CERT_H3/phase3/build_manifest.json')
def pack_bytes(values, bits):
    out = bytearray(); acc = 0; count = 0
    for value in values:
        acc |= value << count; count += bits
        while count >= 8:
            out.append(acc & 255); acc >>= 8; count -= 8
    if count:
        out.append(acc)
    return bytes(out)
graph_path = ARCHIVE / 'data/windows_m10_min.txt'
lines = graph_path.read_text().splitlines(); nr, nq = map(int, lines[0].split())
mapping = dict(tuple(map(int, x.split())) for x in lines[1:1 + nr])
reps = [list(map(int, x.split())) for x in lines[1 + nr:]]
graph_source = CLOSE / 'CertData/H3/Graph.lean'
graph_text = graph_source.read_text()
fields = {n: s for n, s in re.findall(r'def (denseClass|representatives|destinations|kinds) : Nat := h3_hex% "([0-9a-f]+)"', graph_text)}
def hex_equal(name, values, bits):
    expected = pack_bytes(values, bits)
    actual = int(fields[name], 16).to_bytes(len(expected), 'little')
    assert actual == expected, name
hex_equal('denseClass', (mapping.get(c, 3741) for c in range(4 ** 10)), 12)
hex_equal('representatives', (r[0] for r in reps), 20)
hex_equal('destinations', (d + 1 for r in reps for d in r[1:5]), 12)
hex_equal('kinds', (k if k >= 0 else 3 for r in reps for k in r[5:9]), 2)
edge_counts = [sum(k == i for r in reps for k in r[5:9]) for i in range(3)]
h3 = dict(graph=dict(sha256=sha(graph_path), raw_states=nr, quotient_states=nq,
                     all_map_representative_destination_kind_values_equal=True,
                     edge_counts=edge_counts), potentials=[])
for item in h3_receipts:
    path = Path(item['path'])
    digest = sha(path)
    assert digest == item['sha256'] == item['expected_sha256'], path
    if item['case'] == 'graph':
        continue
    tag = item['case']; case = h3_manifest['cases'][tag]
    assert case['source_sha256'] == digest
    with gzip.open(path, 'rb') as f:
        header = list(struct.unpack('<9q', f.read(72)))
        caps_raw = f.read(4 * 4 * 3741)
    caps_source = CLOSE / f'CertData/H3/{tag}/Caps.lean'
    packed = re.search(r'def packedCaps : Nat := h3_hex% "([0-9a-f]+)"', caps_source.read_text()).group(1)
    assert int(packed, 16).to_bytes(len(caps_raw), 'little') == caps_raw
    prefix = read_json(ARCHIVE / f'logs/{case["name"]}_exact_prefix.json')
    assert fractions.Fraction(case['exact_bound']) == fractions.Fraction(prefix['exact_bound'])
    assert case['expected_total']['leaves'] == prefix['leaves']
    assert case['expected_total']['closed'] == prefix['closed']
    assert header == case['header']
    h3['potentials'].append(dict(case=tag, file=path.name, sha256=digest, bytes=path.stat().st_size,
                  header=header, all_14964_cap_values_equal=True,
                  prefix_fraction_matches_archived_record=True, prefix_ceiling=case['ceiling'],
                  prefix_counts=case['expected_total'], plane_count=case['planes'],
                  full_spatial_payload_comparison='production input hash plus exporter and accepted source/olean receipts; compacted literal sources not regenerated'))
result['H3'] = h3
print('H3 graph, caps, prefix records and archive hashes match.', flush=True)

# Tie the current closing sources and reusable certificate cores to the receipts.
closing = read_json(REPO / 'receipts/closing/final-receipt.json')
for row in closing['source_merge_set']:
    assert sha(REPO / row['path']) == row['sha256'], row['path']
olean = closing['output_olean']
assert sha(olean['path']) == olean['sha256']
h3_modules = read_json(REPORTS / 'CERT_H3/phase3/production-modules.json')
gen_names = {x['module'] for x in closing['generated_libraries']['H3']['modules']}
non_generated = [x['module'] for x in h3_modules if x['module'] not in gen_names]
assert len(h3_modules) == 5035 and len(gen_names) == 5032 and len(non_generated) == 3
source_matches = {}
for rel in ['AKLT/Cert/H1', 'AKLT/Cert/H2', 'AKLT/Cert/H3', 'CertData/H3/Kernel', 'CertData/H3/Bridge']:
    matches = []
    for p in (REPO / rel).rglob('*'):
        if not p.is_file() or p.suffix not in ['.lean', '.py']:
            continue
        other = CLOSE / p.relative_to(REPO)
        if other.is_file():
            assert p.read_bytes() == other.read_bytes(), str(p)
            matches.append(str(p.relative_to(REPO)))
    source_matches[rel] = len(matches)
result['closing'] = dict(current_sources_match_receipt=True, output_olean_hash_match=True,
                  source_merge_set_count=len(closing['source_merge_set']), theorem_types=closing['theorems'],
                  H3_generated_modules=5032, H3_production_manifest_modules=5035,
                  H3_handwritten_manifest_modules=non_generated, current_core_matches_closing=source_matches)
result['build'] = dict(command='latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex',
                output_pdf_sha256=sha(OUT / 'paper-copy/main.pdf'),
                source_pdf_sha256=sha(PAPER / 'main.pdf'),
                pdf_equal_to_paper=(sha(OUT / 'paper-copy/main.pdf') == sha(PAPER / 'main.pdf')))
log = (OUT / 'paper-copy/main.log').read_text()
result['build']['undefined_references_or_citations'] = bool(re.search(r'(undefined|multiply defined|LaTeX Error|Emergency stop)', log, re.I))
assert not result['build']['undefined_references_or_citations']
result['build']['pdflatex_passes'] = len(re.findall(r'Run number \d+ of rule .pdflatex.', (OUT / 'latexmk-output.log').read_text()))
result['build']['final_underfull_vboxes'] = len(re.findall(r'Underfull', log))
validation_base = '63d176add85a0eae6c862c54849a495434b7d438'
post_validation_changes = subprocess.check_output(['git', 'diff', '--name-status', validation_base, 'HEAD'], cwd=REPO, text=True).splitlines()
assert all(row.startswith('A\t') or row == 'M\tlakefile.toml' for row in post_validation_changes)
protected_diff = subprocess.check_output(['git', 'diff', '486b316', 'HEAD', '--', 'AKLT/Cert', 'CertData/Close', 'CertData/H1/Close', 'CertData/H3/Close', 'AKLT/Final/Conditional.lean', 'AKLT/Final/Skeleton.lean', 'AKLT/Challenge/MainV2.lean'], cwd=REPO, text=True)
assert not protected_diff
result['source_snapshot'] = dict(formalization_main=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip(),
    independent_recheck_base=validation_base, protected_closing_and_certificate_sources_unchanged_since_486b316=True,
    previously_validated_sources_unchanged=True, post_validation_changes=post_validation_changes)
assert read_json(OUT / 'source-snapshot.json') == {p.name: sha(p) for p in PAPER.glob('*.tex')}
(OUT / 'audit-results.json').write_text(json.dumps(result, indent=2) + '\n')
print('All comparisons passed; audit-results.json written.', flush=True)
