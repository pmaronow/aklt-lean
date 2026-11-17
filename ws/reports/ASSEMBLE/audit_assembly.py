#!/usr/bin/env python3
"""Static assembly checks and exact source-to-delivery edit inventory."""
from collections import Counter, defaultdict
import difflib
import hashlib
import json
from pathlib import Path
import re

ROOT = Path('/home/ubuntu/aklt')
DEST = ROOT / 'manuscript-v2'
OUT = ROOT / 'reports/ASSEMBLE'
SOURCES = json.loads((OUT / 'sources.json').read_text())
FILES = ['main.tex'] + [s['file'] for s in SOURCES]
TEXTS = {f: (DEST / f).read_text() for f in FILES}
ENV = r'(theorem|proposition|lemma|corollary|definition|hypothesis|remark)'
STATEMENT_RE = re.compile(r'\\begin\{' + ENV + r'\}(.*?)\\end\{\1\}', re.S)


def line_at(text, pos):
    return text.count('\n', 0, pos) + 1


def statements(text):
    result = {}
    for m in STATEMENT_RE.finditer(text):
        label = re.search(r'\\label\{([^}]+)\}', m.group())
        if label:
            result[label[1]] = {'text': m.group(), 'line': line_at(text, m.start())}
    return result


def normalized(text):
    return re.sub(r'\s+', '', text)


labels = defaultdict(list)
citations = []
bib = []
for filename, text in TEXTS.items():
    for m in re.finditer(r'\\label\{([^}]+)\}', text):
        labels[m[1]].append({'file': filename, 'line': line_at(text, m.start())})
    for m in re.finditer(r'\\cite\w*\*?(?:\[[^]]*\])*\{([^}]+)\}', text):
        citations.extend(k.strip() for k in m[1].split(','))
    bib.extend(re.findall(r'\\bibitem(?:\[[^]]*\])?\{([^}]+)\}', text))

refs, cross = [], []
for filename, text in TEXTS.items():
    for m in re.finditer(r'\\(ref|eqref|pageref|autoref|[Cc]ref)\*?\{([^}]+)\}', text):
        for label in m[2].split(','):
            label = label.strip()
            start = text.rfind('\n\n', 0, m.start()) + 2
            end = text.find('\n\n', m.end())
            if end < 0:
                end = len(text)
            item = {'file': filename, 'line': line_at(text, m.start()),
                    'kind': m[1], 'label': label, 'owner': labels.get(label, []),
                    'paragraph': text[start:end]}
            refs.append(item)
            if labels.get(label) and labels[label][0]['file'] != filename:
                cross.append(item)

plan = (ROOT / 'reports/REV-PLAN/PLAN.md').read_text()
planned = {}
for block in re.findall(r'```latex\s*\n(.*?)```', plan, re.S):
    planned.update(statements(block))
owned = {label: {'file': filename, **s} for filename, text in TEXTS.items()
         for label, s in statements(text).items()}
statement_diffs = []
for label, statement in owned.items():
    if label in planned and normalized(statement['text']) != normalized(planned[label]['text']):
        statement_diffs.append({'label': label, 'file': statement['file'],
            'line': statement['line'],
            'diff': '\n'.join(difflib.unified_diff(planned[label]['text'].splitlines(),
                statement['text'].splitlines(), fromfile='plan', tofile=statement['file'], lineterm=''))})

edits = []
source_integrity = []
for source in SOURCES:
    original_bytes = Path(source['source']).read_bytes()
    source_integrity.append({'file': source['file'],
        'unchanged': hashlib.sha256(original_bytes).hexdigest() == source['sha256']})
    before = original_bytes.decode().splitlines()
    after = TEXTS[source['file']].splitlines()
    for tag, i, j, k, l in difflib.SequenceMatcher(a=before, b=after, autojunk=False).get_opcodes():
        if tag != 'equal':
            edits.append({'file': source['file'], 'source_line': i + 1,
                'assembled_line': k + 1, 'source_line_count': j - i,
                'assembled_line_count': l - k, 'before': '\n'.join(before[i:j]),
                'after': '\n'.join(after[k:l])})

editorial = []
editorial_re = re.compile(r'\b(?:plans?|lanes?|reviews?|reviewer|referee|agents?|baseline|revision|revised|registry|supersedes)\b', re.I)
comments = []
for filename, text in TEXTS.items():
    for n, line in enumerate(text.splitlines(), 1):
        if editorial_re.search(line):
            editorial.append({'file': filename, 'line': n, 'text': line})
        if re.search(r'(?<!\\)%', line):
            comments.append({'file': filename, 'line': n, 'text': line})

result = {
    'section_order': [s['file'] for s in SOURCES],
    'labels': dict(labels), 'references': refs, 'cross_references': cross,
    'undefined_references': [r for r in refs if not r['owner']],
    'duplicate_labels': {k: v for k, v in labels.items() if len(v) != 1},
    'citations': sorted(set(citations)), 'bibliography': bib,
    'undefined_citations': sorted(set(citations) - set(bib)),
    'uncited_bibliography': sorted(set(bib) - set(citations)),
    'planned_statements': len(planned), 'assembled_statements': len(owned),
    'missing_planned_statements': sorted(set(planned) - set(owned)),
    'statement_differences': statement_diffs, 'section_edits': edits,
    'source_integrity': source_integrity, 'editorial_candidates': editorial,
    'comments': comments,
}
(OUT / 'audit.json').write_text(json.dumps(result, indent=2) + '\n')

by_pair = defaultdict(list)
for r in cross:
    by_pair[(r['file'], r['label'], r['owner'][0]['file'])].append(r['line'])
with (OUT / 'cross-file-contexts.txt').open('w') as f:
    for r in cross:
        f.write(f"{r['file']}:{r['line']} -> {r['label']} -> {r['owner'][0]['file']}:{r['owner'][0]['line']}\n")
        f.write(r['paragraph'] + '\n\n')
with (OUT / 'cross-file-index.tsv').open('w') as f:
    for (filename, label, owner), lines in sorted(by_pair.items()):
        f.write(f"{filename}\t{','.join(map(str, lines))}\t{label}\t{owner}\n")

for key in ['undefined_references', 'duplicate_labels', 'undefined_citations',
            'uncited_bibliography', 'missing_planned_statements', 'comments']:
    print(key + ': ' + str(result[key]))
print('labels:', len(labels), 'references:', len(refs), 'cross-file uses:', len(cross),
      'cross-file file/label pairs:', len(by_pair))
print('statements:', len(owned), '/', len(planned), 'statement deviations:', len(statement_diffs))
for diff in statement_diffs:
    print(diff['diff'])
print('editorial candidates:', json.dumps(editorial))
