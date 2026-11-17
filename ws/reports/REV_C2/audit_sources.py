#!/usr/bin/env python3
"""Check the inventory order, statement text and standalone references."""
import json
from pathlib import Path
import re

here = Path(__file__).resolve().parent
plan = Path('/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md').read_text()
registry = {m.group(1): m.group(2) for m in re.finditer(
    r'^### ([^ ]+) .*?\n```latex\n(.*?)\n```', plan, re.M | re.S)}
expected = {
    'sec8-inputs.tex': ['t:H1', 't:inputs'],
    'app-input-contracts.tex': [
        'd:memory-automaton', 'd:memorygrowth', 'l:alm', 'l:H2-dihedral',
        'p:H2-test', 'l:H2-CV', 'l:automaton-quotient', 'p:automaton10',
        'd:phaseweights', 'l:phase-expansion', 'd:stationary-walk',
        'l:stationary-domination', 'l:Bellman-soundness',
        'd:stationary-certificate', 'l:stationary-local-global',
        'd:prefix-bound', 'l:prefix-domination', 'l:kernel-reflection',
        'p:stationary-check', 'l:stationary-assembly'],
}
known_deviations = {'t:inputs'}
all_labels, all_refs = set(), set()
result = {}
for filename, labels in expected.items():
    source = (here/filename).read_text()
    actual = re.findall(r'\\label\{([^}]+)\}', source)
    assert actual == labels, (filename, actual)
    all_labels.update(actual)
    all_refs.update(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', source))
    matched, changed = [], []
    for label in labels:
        match = re.search(
            r'\\begin\{(theorem|lemma|definition|proposition)\}'
            r'\\label\{' + re.escape(label) + r'\}.*?\\end\{\1\}', source, re.S)
        assert match, label
        actual_statement = re.sub(r'\s+', ' ', match.group(0)).strip()
        planned_statement = re.sub(r'\s+', ' ', registry[label]).strip()
        if actual_statement == planned_statement:
            matched.append(label)
        else:
            assert label in known_deviations, label
            changed.append(label)
    assert '% PROOF_OR_NOTE' not in source
    assert source.count(r'\(') == source.count(r'\)')
    assert source.count(r'\[') == source.count(r'\]')
    result[filename] = dict(labels=labels, exact_planned_statements=matched,
                           explicitly_reported_changes=changed,
                           proof_environments=source.count(r'\begin{proof}'))
result['external_references'] = sorted(all_refs-all_labels)
assert result['external_references'] == sorted([
    'd:kernel', 'd:kernel-order', 'd:weights', 'h:H1', 'h:H2', 'h:H3',
    'l:gram-residual', 'l:integercheck', 'l:log-mean-bounds',
    'c:reduce', 'd:pattern', 'l:Iw', 'l:Ostruct', 'l:inversion',
    'l:leaf', 'l:moments', 'l:sector'])
(here/'checks/source_audit.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
