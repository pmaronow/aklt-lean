#!/usr/bin/env python3
"""Official source/configuration checks and release-specific invariants.

This is a local source check, not full preparation or protected verification.
Author metadata and license findings are reported separately from proof checks.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--verifier', type=Path, required=True)
ap.add_argument('--project', type=Path, default=Path(__file__).resolve().parents[1])
ap.add_argument('--report', type=Path, required=True)
args = ap.parse_args()
sys.dont_write_bytecode = True
sys.path.insert(0, str(args.verifier.resolve()))
from scripts import verify_submission as official
from scripts.source_requirements import physical_lines
from refresh_manifests import check as check_manifests
project = args.project.resolve()
summary, issues = official.inspect_lean_sources(project)
problems = [dict(code=e.code, path=e.path, message=str(e)) for e in issues]
manifests = check_manifests(project)
for issue in manifests['issues']:
    problems.append(dict(code='package.source_hash', **issue))
config = official.load_comparator_config(project/'comparator.json')
if config['theorem_names'] != ['AKLTPalomar.aklt_gap'] or set(config['permitted_axioms']) != {
        'propext', 'Classical.choice', 'Quot.sound'} or config.get('definition_names'):
    problems.append(dict(code='package.configuration', message='Unexpected comparison surface'))
inventory=json.loads((project/'verification/source-inventory.json').read_text())
expected=set(inventory['handwritten'])
generated=json.loads((project/'verification/generated-modules.json').read_text())
allowed_generated={m.replace('.','/')+'.lean' for fam in ['H1','H3'] for m in generated[fam]}
actual={str(p.relative_to(project)) for p in official.lean_source_files(project)}
if expected-actual or actual-expected-allowed_generated:
    problems.append(dict(code='package.source_inventory', missing=sorted(expected-actual), extra=sorted(actual-expected-allowed_generated)))
# A source-only check: render in memory, compare exact bytes, and never rewrite
# the Challenge during verification. This also validates the source hash record.
spec = importlib.util.spec_from_file_location('release_statement_generator', project/'scripts/make_challenge.py')
statement_generator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(statement_generator)
try:
    generated_challenge, generated_sources = statement_generator.render(project)
    stale = [name for name, data in [('Challenge.lean', generated_challenge),
                                   ('verification/statement-sources.json', generated_sources)]
             if not (project/name).is_file() or (project/name).read_bytes() != data]
    if stale:
        problems.append(dict(code='package.statement_generation', files=stale,
                             message='Statement files differ byte-for-byte from their generator output'))
except Exception as error:
    problems.append(dict(code='package.statement_generation', message=str(error)))
challenge = (project/'Challenge.lean').read_text()
if physical_lines(challenge) > 1000 or len(challenge.encode()) > 100*1024:
    problems.append(dict(code='package.challenge_size'))
for p in official.lean_source_files(project):
    code = official.strip_lean_comments(p.read_text())
    code = re.sub(r'"(?:\\.|[^"\\])*"', '""', code)
    holes = re.findall(r'(?<![\w.])(?:sorry|admit)(?![\w\'])', code)
    if holes != (['sorry'] if p == project/'Challenge.lean' else []):
        problems.append(dict(code='package.proof_hole', path=str(p.relative_to(project))))
    forbidden = re.findall(r'(?<![\w.])(?:axiom|native_decide|unsafe|implemented_by|extern|opaque)(?![\w\'])', code)
    if forbidden:
        problems.append(dict(code='package.forbidden_tokens', path=str(p.relative_to(project)), tokens=sorted(set(forbidden))))
    if re.search(r'set_option\s+debug\.skipKernelTC\s+true', code):
        problems.append(dict(code='package.kernel_bypass', path=str(p.relative_to(project))))
    if re.search(r'set_option\s+maxHeartbeats\s+0\b', code) and p!=project/'AKLT/Cert/H2/Check.lean' and str(p.relative_to(project)) not in allowed_generated:
        problems.append(dict(code='package.unlimited_heartbeats', path=str(p.relative_to(project))))
if 'TODO' in (project/'formalization.yaml').read_text():
    problems.append(dict(code='package.metadata_todo', message='Author metadata and public provenance remain TODO'))
if not (project/'LICENSE').is_file():
    problems.append(dict(code='package.license_missing', message='Choose a license and add its exact text at the release root'))
report = dict(scope='local source/config checks; not full preparation', summary=summary,
              configuration=config, passed=not problems, issues=problems,
              generated_present=sorted(actual & allowed_generated),
              generated_missing=sorted(allowed_generated-actual))
args.report.parent.mkdir(parents=True, exist_ok=True)
args.report.write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(dict(passed=not problems, summary=summary, issue_count=len(problems)), indent=2))
raise SystemExit(0 if not problems else 1)
