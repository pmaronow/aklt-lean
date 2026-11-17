#!/usr/bin/env python3
"""Build and audit both existing H1 closing modules after fresh production."""
import argparse, json, os, re, signal, subprocess, time
from pathlib import Path
from production_build import (ROOT, REPORT, ALLOWED, artifact_hashes, artifact_path,
                              group_rss, guard, metrics, sha)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--report-dir', type=Path, default=REPORT)
    args = ap.parse_args()
    production = json.loads((args.report_dir / 'verified-production.json').read_text())
    assert production['success'] and production['modules'] == 7964
    report = args.report_dir / 'closing'
    report.mkdir(exist_ok=True)
    env = os.environ.copy()
    env['PATH'] = str(Path.home() / '.elan/bin') + ':' + env['PATH']
    env['LEAN_NUM_THREADS'] = '1'
    records = []
    expected = {'CertData.H1.Close.finiteData', 'CertData.H1.Close.certificate'}
    for module in ['CertData.H1.Close.Main', 'CertData.H1.Close.Audit']:
        guard()
        source = ROOT / (module.replace('.', '/') + '.lean')
        obj = artifact_path(module)
        obj.parent.mkdir(parents=True, exist_ok=True)
        name = module.split('.')[-1]
        stdout, stderr, timing = [report / (name + suffix) for suffix in ['.stdout', '.stderr', '.time']]
        command = ['/usr/bin/time', '-v', '-o', str(timing), 'lake', 'env', 'lean',
                   '-DElab.async=false', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
                   '-DwarningAsError=true', '-o', str(obj), str(source)]
        started = time.monotonic()
        started_at = time.time()
        peak = 0
        with stdout.open('w') as out, stderr.open('w') as err:
            process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=out, stderr=err, start_new_session=True)
            try:
                while process.poll() is None:
                    guard()
                    peak = max(peak, group_rss(process.pid))
                    if peak > 64 * 2**30:
                        raise MemoryError('closing module exceeded 64 GiB')
                    time.sleep(.5)
            except BaseException:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                raise
        if process.returncode:
            raise RuntimeError(stdout.read_text() + stderr.read_text())
        text = stdout.read_text()
        audits = {}
        for theorem, values in re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", text, re.S):
            axioms = sorted(v.strip() for v in values.split(',') if v.strip())
            if not set(axioms) <= ALLOWED:
                raise RuntimeError('forbidden closing axiom: ' + theorem)
            audits[theorem] = axioms
        assert expected <= set(audits), 'missing closing theorem audit'
        if name == 'Main':
            for theorem, statement in [('finiteData', 'AKLT.Blueprint.Top.H1FiniteDataStatementV2'),
                                       ('certificate', 'AKLT.Blueprint.Top.CertificateStatement')]:
                pattern = r'theorem\s+' + re.escape('CertData.H1.Close.' + theorem) + r'\s*:\s*' + re.escape(statement) + r'\s*:='
                assert re.search(pattern, text), 'closing type is not exact and hypothesis-free'
        row = dict(module=module, exit=0, command=command, wall_seconds=time.monotonic()-started,
                   started_at=started_at, finished_at=time.time(),
                   source_sha256=sha(source), artifact_hashes=artifact_hashes(module),
                   axioms=audits, log=str(stdout), stderr=str(stderr), timing=str(timing), **metrics(timing))
        records.append(row)
        print(json.dumps({k: v for k, v in row.items() if k not in ['command', 'axioms']}), flush=True)
    receipt = dict(success=True, records=records,
                   statements={'CertData.H1.Close.finiteData': 'AKLT.Blueprint.Top.H1FiniteDataStatementV2',
                               'CertData.H1.Close.certificate': 'AKLT.Blueprint.Top.CertificateStatement'},
                   closed=True, exact_types_checked_by_examples=True)
    (report / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    (report / 'SOURCES.sha256').write_text(''.join(
        row['source_sha256'] + '  ' + row['module'].replace('.', '/') + '.lean\n'
        for row in records))
    objects = {path: digest for row in records for path, digest in row['artifact_hashes'].items()}
    (report / 'COMPILED.sha256').write_text(''.join(
        objects[path] + '  ' + path + '\n' for path in sorted(objects)))


if __name__ == '__main__':
    main()
