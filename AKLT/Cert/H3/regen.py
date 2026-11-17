#!/usr/bin/env python3
"""Regenerate H3 module sources and run fresh, bounded kernel checks.

No legacy compiled artifact or numerical answer is accepted as proof. Resume
requires matching source, dependency, compiler, and compiled artifact hashes.
"""
import argparse
import collections
import concurrent.futures
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import threading
import time

import production as gen

ROOT = gen.ROOT
REPORT = gen.REPORT
LIB = ROOT / '.lake/build/lib/lean'
INVENTORY = set(json.loads((ROOT / 'verification/generated-modules.json').read_text())['H3'])
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
FORBIDDEN = re.compile(r'\b(sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque|run_cmd)\b|debug\.skipKernelTC|macro_rules|#eval|\bmaxHeartbeats\s+0\b')
LOCK = threading.Lock()
ACTIVE = {}


def sha(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(value, indent=2) + '\n')
    tmp.replace(path)


def append(path, value):
    with LOCK:
        with path.open('a') as f:
            f.write(json.dumps(value) + '\n')


def progress(text):
    print(text, flush=True)
    path = REPORT / 'report.md'
    if path.exists():
        s = path.read_text()
        marker = '## ORCH-SUMMARY'
        before, sep, after = s.partition(marker)
        path.write_text(before + '- ' + text + '\n\n' + sep + after)


def pin_inputs():
    records = []
    for pin in json.loads((Path(__file__).with_name('inputs.json')).read_text()):
        p = gen.ARCHIVE / pin['name']
        actual = sha(p)
        if actual != pin['sha256'] or p.stat().st_size != pin['bytes']:
            raise RuntimeError('Input pin mismatch: ' + str(p))
        records.append(dict(pin, path=str(p)))
    p = Path(__file__).with_name('prefix-reference.json')
    records.append(dict(role='tracked independent exact-prefix comparison assertions', path=str(p), bytes=p.stat().st_size, sha256=sha(p)))
    save(REPORT / 'input-pins.json', records)
    return records


def generate(args):
    pin_inputs()
    if args.legacy_report:
        rows = json.loads((args.legacy_report / 'production-modules.json').read_text())
        gen.LEGACY_HASHES.update({r['module']: r['source_sha256'] for r in rows})
    m = gen.load_manifest()
    mapping, _ = gen.generate_graph(m)
    oracle = gen.Oracle()
    oracle.generate_exact(m)
    m['exact_denominator'] = str(oracle.K)
    for case in args.cases:
        gen.generate_case(case, m, mapping, oracle, args.group, args.depth, args.batch)
        gen.save_manifest(m)
        progress('Regenerated ' + case + ' from its pinned numeric archive.')
    gen.generate_assemblies(m)
    # The legacy manifest also scheduled three hand-written bridge modules.
    m['jobs'] = [j for j in m['jobs'] if j['module'] in INVENTORY]
    for j in m['jobs']:
        j['deps'] = imports(ROOT / j['source'])
    gen.save_manifest(m)
    save(REPORT / 'generator-equivalence.json', gen.EQUIVALENCE)
    info = {j['module']: source_info(j) for j in m['jobs']}
    save(REPORT / 'sources.json', info)
    missing = INVENTORY - set(info)
    if set(args.cases) == set(gen.CASES) and missing:
        raise RuntimeError('Missing generated modules: ' + str(sorted(missing)))
    progress(f'Generated {len(info)}/{len(INVENTORY)} module-system sources; all headers, line caps, and forbidden-token checks pass.')


def refresh():
    """Apply the pilot's import repair to an export already in progress."""
    m = gen.load_manifest()
    if {j['module'] for j in m['jobs']} != INVENTORY:
        raise RuntimeError('Wait for the complete generated inventory before refresh')
    repaired = []
    for j in m['jobs']:
        p = ROOT / j['source']
        if j['kind'] in {'early', 'prefix', 'prefix_assembly'}:
            s = p.read_text()
            if re.search(r'\b(earlyDFS|prefixBatch)\b', s) and 'import all Init.Data.List.Sort.Basic' not in s:
                p.write_text(s.replace('\n\n@[expose]', '\nimport all Init.Data.List.Sort.Basic\n\n@[expose]', 1))
                repaired.append(j['module'])
        j['deps'] = imports(p)
    gen.save_manifest(m)
    save(REPORT / 'sources.json', {j['module']: source_info(j) for j in m['jobs']})
    save(REPORT / 'pilot-import-repair.json', dict(modules=repaired, checker_definitions_changed=False))
    progress(f'Applied the pilot visibility repair to {len(repaired)} still-unrepaired generated modules; refreshed all 5,032 source hashes.')


def imports(path):
    result = []
    with path.open() as f:
        for line in f:
            m = re.match(r'^(?:public )?import (?:all )?(\S+)', line)
            if m:
                result.append(m[1])
            elif line.strip() and line.strip() != 'module':
                break
    return result


def source_info(j):
    p = ROOT / j['source']
    s = p.read_text()
    lines = s.splitlines()
    # Hex strings are data, and can occupy 25 MB in a single small module.
    # Scan code outside those strings, just as the official source audit does.
    code = []
    for line in lines:
        at = line.find('h3_hex% "')
        code.append(line if at < 0 else line[:at] + 'h3_hex% ""' + line[line.rfind('"')+1:])
    code = '\n'.join(code)
    if not s.startswith('module\n') or len(lines) > 10000 or FORBIDDEN.search(code):
        raise RuntimeError('Source policy failed: ' + str(p))
    ns = re.search(r'^namespace (\S+)', code, re.M)[1]
    declarations = {}
    for match in re.finditer(r'^theorem (\w+)', code, re.M):
        end = code.find(':=', match.end())
        if end < 0:
            raise RuntimeError('Missing theorem body: ' + str(p))
        declarations[ns + '.' + match[1]] = code[match.start():end].strip()
    theorems = list(declarations)
    return dict(source=j['source'], sha256=sha(p), bytes=p.stat().st_size,
                lines=len(lines), theorems=theorems, declarations=declarations, imports=imports(p))


def environment():
    env = dict(os.environ)
    env['PATH'] = str(Path.home() / '.elan/bin') + ':' + env.get('PATH', '')
    env['LEAN_NUM_THREADS'] = '1'
    raw = subprocess.check_output(['lake', 'env', 'env', '-0'], cwd=ROOT, env=env)
    env = dict(x.decode().split('=', 1) for x in raw.split(b'\0') if x)
    if any('/wt/' in p or '/scratch/CERT_' in p for p in env.get('LEAN_PATH', '').split(':')):
        raise RuntimeError('Legacy import root in LEAN_PATH')
    return env


def context(env):
    # Changes anywhere in the hand-written source surface invalidate resumes.
    tracked = subprocess.check_output(['git', 'ls-files', '*.lean'], cwd=ROOT, text=True).splitlines()
    sources = {p: sha(ROOT / p) for p in tracked if (ROOT / p).exists()}
    c = dict(toolchain=(ROOT / 'lean-toolchain').read_text().strip(),
             lean=subprocess.check_output(['lean', '--version'], env=env, text=True).strip(),
             lean_binary_sha256=sha(shutil.which('lean', path=env['PATH'])),
             handwritten_source_sha256=digest(sources), lean_path=env.get('LEAN_PATH'))
    save(REPORT / 'environment.json', c)
    return digest(c)


def artifacts(module):
    base = LIB / module.replace('.', '/')
    return [base.with_suffix('.olean'), Path(str(base) + '.olean.server'), Path(str(base) + '.olean.private')]


def artifact_records(module):
    return [dict(path=str(p.relative_to(ROOT)), bytes=p.stat().st_size, sha256=sha(p))
            for p in artifacts(module) if p.exists()]


def read_axioms(log):
    result = {}
    for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
        result[name] = [x.strip() for x in values.split(',') if x.strip()]
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        result[name] = []
    return result


def dep_hashes(j):
    result = {}
    for d in j['deps']:
        if not d.startswith(('AKLT.', 'CertData.', 'RegenSamples.')):
            # Standard-library and Mathlib artifacts are pinned by the toolchain
            # and package manifest; never rebuild or shadow them.
            continue
        p = artifacts(d)[0]
        if not p.exists():
            raise RuntimeError('Missing module-system dependency: ' + str(p))
        result[d] = sha(p)
    return result


def receipt_path(module):
    return REPORT / 'receipts' / (module + '.json')


def current(j, info, ctx):
    p = receipt_path(j['module'])
    if not p.exists():
        return False
    r = json.loads(p.read_text())
    if r['exit'] or r['context'] != ctx or r['source_sha256'] != info['sha256']:
        return False
    if r['dependencies'] != dep_hashes(j):
        return False
    return all((ROOT / a['path']).exists() and sha(ROOT / a['path']) == a['sha256'] for a in r['artifacts'])


def run_one(j, info, args, env, ctx):
    module = j['module']
    folder = REPORT / args.stage
    folder.mkdir(parents=True, exist_ok=True)
    log = folder / (module + '.log')
    stats = folder / (module + '.time')
    out = artifacts(module)[0]
    out.parent.mkdir(parents=True, exist_ok=True)
    src = ROOT / j['source']
    deps = dep_hashes(j)
    cap = args.process_gib * 1024**3
    command = ['prlimit', '--as=' + str(cap), '--core=0', '--', '/usr/bin/time', '-v', '-o', str(stats),
               'timeout', str(args.timeout), 'lean', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
               '-DElab.async=false', '-DwarningAsError=true', '-o', str(out), str(src)]
    if args.profile:
        command.insert(-1, '-Dprofiler=true')
    started = time.time()
    with log.open('w') as f:
        proc = subprocess.Popen(command, cwd=ROOT, env=env, stdout=f, stderr=subprocess.STDOUT, start_new_session=True)
        with LOCK:
            ACTIVE[proc.pid] = module
        proc.wait()
        with LOCK:
            ACTIVE.pop(proc.pid, None)
    output = log.read_text()
    axioms = read_axioms(output)
    missing = set(info['theorems']) - set(axioms)
    bad = {n: a for n, a in axioms.items() if set(a) - ALLOWED}
    exit_code = proc.returncode or (2 if missing or bad else 0)
    r = dict(module=module, kind=j['kind'], case=j.get('case'), stage=args.stage,
             exit=exit_code, lean_exit=proc.returncode, started_unix=started, ended_unix=time.time(),
             wall=time.time() - started, source=j['source'], source_sha256=info['sha256'],
             context=ctx, dependencies=deps, command=command, log=str(log), time_log=str(stats),
             axioms=axioms, exported_theorems=info['theorems'], missing_axioms=sorted(missing), forbidden_axioms=bad)
    if stats.exists():
        for line in stats.read_text().splitlines():
            if 'Maximum resident set size (kbytes):' in line:
                r['rss_kib'] = int(line.rsplit(':', 1)[1])
            if 'User time (seconds):' in line:
                r['user_s'] = float(line.rsplit(':', 1)[1])
            if 'System time (seconds):' in line:
                r['sys_s'] = float(line.rsplit(':', 1)[1])
    r['cpu'] = r.get('user_s', 0) + r.get('sys_s', 0)
    r['log_sha256'] = sha(log)
    r['time_log_sha256'] = sha(stats) if stats.exists() else None
    r['artifacts'] = artifact_records(module) if not exit_code else []
    save(folder / (module + '.json'), r)
    if not exit_code:
        save(receipt_path(module), r)
    append(REPORT / 'attempts.jsonl', r)
    if exit_code:
        print('FAILED ' + module + '\n' + output[-5000:], flush=True)
    return r


def memory():
    with LOCK:
        pending = list(ACTIVE)
    seen = set()
    rss = 0
    lean_count = 0
    while pending:
        pid = pending.pop()
        if pid in seen:
            continue
        seen.add(pid)
        try:
            s = Path(f'/proc/{pid}/status').read_text()
            match = re.search(r'^VmRSS:\s+(\d+)', s, re.M)
            rss += int(match[1]) * 1024 if match else 0
            lean_count += int(bool(re.search(r'^Name:\s+lean$', s, re.M)))
            pending += list(map(int, Path(f'/proc/{pid}/task/{pid}/children').read_text().split()))
        except (FileNotFoundError, ProcessLookupError):
            pass
    available = int(re.search(r'^MemAvailable:\s+(\d+)', Path('/proc/meminfo').read_text(), re.M)[1]) * 1024
    return rss, available, lean_count


def reserve(j):
    return {'all_case_assembly': 38, 'close': 38, 'prefix': 19, 'plane_catalog': 19,
            'rows': 16, 'tables': 16, 'row_assembly': 16, 'pilot': 16, 'case_assembly': 16,
            'plane_data': 8, 'endpoint_data': 8, 'caps': 8, 'exact': 8}.get(j['kind'], 11) * 10**9


def select_jobs(args, m):
    jobs = {j['module']: dict(j) for j in m['jobs']}
    # This also supports a pilot while another process is still exporting cases.
    for j in jobs.values():
        p = ROOT / j['source']
        if p.exists():
            j['deps'] = imports(p)
    if args.action == 'close':
        jobs = {}
        for name in ['Leaves', 'Main']:
            module = 'CertData.H3.Close.' + name
            p = ROOT / (module.replace('.', '/') + '.lean')
            jobs[module] = dict(module=module, source=str(p.relative_to(ROOT)), kind='close', deps=imports(p))
        return jobs
    selected = {n for n, j in jobs.items() if (not args.module or n in args.module)
                and (not args.kind or j['kind'] in args.kind)
                and (not j.get('case') or j['case'] in args.cases)}
    if args.module and set(args.module) - set(jobs):
        raise RuntimeError('Unknown selected modules: ' + str(set(args.module) - set(jobs)))
    pending = list(selected)
    while pending:
        for d in jobs[pending.pop()]['deps']:
            if d in jobs and d not in selected:
                selected.add(d)
                pending.append(d)
    return {n: jobs[n] for n in sorted(selected)}


def build(args):
    env = environment()
    ctx = context(env)
    m = gen.load_manifest()
    jobs = select_jobs(args, m)
    info = {n: source_info(j) for n, j in jobs.items()}
    pending = dict(jobs)
    done = set()
    running = {}
    failed = []
    reused = 0
    peak = 0
    peak_count = 0
    started = time.time()
    last_progress = 0
    progress(f'{args.stage}: checking {len(jobs)} modules, at most {args.jobs} Lean processes and {args.ram_gb} GB reserved RSS.')
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            rss, available, count = memory()
            peak = max(peak, rss)
            peak_count = max(peak_count, count)
            free_disk = shutil.disk_usage(ROOT).free
            sample = dict(time=time.time(), stage=args.stage, rss_bytes=rss, available_bytes=available,
                          lean_processes=count, disk_free_bytes=free_disk)
            append(REPORT / 'resources.jsonl', sample)
            if rss > 170 * 10**9 or count > 16 or available < 40 * 10**9 or free_disk <= 100 * 1024**3:
                with LOCK:
                    for pid in ACTIVE:
                        try:
                            os.killpg(pid, signal.SIGTERM)
                        except ProcessLookupError:
                            pass
                raise RuntimeError('Resource guard stopped the run: ' + str(sample))
            ready = [j for j in pending.values() if all(d not in jobs or d in done for d in j['deps'])]
            # Finish shared data and then one case, allowing its catalogs to run.
            ready.sort(key=lambda j: (list(gen.CASES).index(j['case']) + 1 if j.get('case') else 0,
                                      0 if 'catalog' in j['kind'] else 1, j['module']))
            reserved = sum(reserve(j) for j in running.values())
            for j in ready:
                n = j['module']
                force = args.force and (not args.module or n in args.module)
                if not force and current(j, info[n], ctx):
                    done.add(n)
                    pending.pop(n)
                    reused += 1
                    continue
                need = reserve(j)
                if len(running) >= args.jobs or reserved + need > args.ram_gb * 10**9 or available - need < 40 * 10**9:
                    break
                running[pool.submit(run_one, j, info[n], args, env, ctx)] = j
                pending.pop(n)
                reserved += need
            if not running:
                if pending and not ready:
                    raise RuntimeError('Blocked dependency graph: ' + str(list(pending)[:5]))
            else:
                completed, _ = concurrent.futures.wait(running, timeout=2, return_when=concurrent.futures.FIRST_COMPLETED)
                for f in completed:
                    j = running.pop(f)
                    r = f.result()
                    if r['exit']:
                        failed.append(r['module'])
                    else:
                        done.add(j['module'])
            if time.time() - last_progress >= 30 or (not pending and not running):
                progress(f'{args.stage}: {len(done)}/{len(jobs)} checked ({reused} resumed), {len(running)} running; peak sampled RSS {peak / 10**9:.2f} GB; elapsed {time.time()-started:.1f} s.')
                last_progress = time.time()
            if failed:
                # Let already running bounded checks finish and retain receipts.
                pending.clear()
                for f, j in list(running.items()):
                    r = f.result()
                    if r['exit']:
                        failed.append(j['module'])
                    else:
                        done.add(j['module'])
                running.clear()
                break
    result = dict(stage=args.stage, started_unix=started, ended_unix=time.time(), wall=time.time()-started,
                  total=len(jobs), done=len(done), resumed=reused, failed=failed, sampled_peak_rss_bytes=peak,
                  peak_lean_processes=peak_count, jobs=args.jobs, ram_gb=args.ram_gb)
    append(REPORT / 'runs.jsonl', result)
    save(REPORT / (args.stage + '-run.json'), result)
    if failed:
        raise SystemExit(1)


def verify(args):
    pin_inputs()
    env = environment()
    ctx = context(env)
    m = gen.load_manifest()
    byname = {j['module']: j for j in m['jobs']}
    if set(byname) != INVENTORY:
        raise RuntimeError('Generated inventory mismatch')
    records = []
    declarations = {}
    for n in sorted(byname):
        j = byname[n]
        info = source_info(j)
        j['deps'] = info['imports']
        declarations.update({name: dict(module=n, namespace=n, source=j['source'], lean_header=header)
                             for name, header in info['declarations'].items()})
        if not current(j, info, ctx):
            raise RuntimeError('Invalid or stale successful receipt: ' + n)
        r = json.loads(receipt_path(n).read_text())
        output = Path(r['log']).read_text()
        actual_axioms = read_axioms(output)
        if actual_axioms != r['axioms'] or set(info['theorems']) - set(actual_axioms) or any(set(a) - ALLOWED for a in actual_axioms.values()):
            raise RuntimeError('Axiom receipt mismatch: ' + n)
        r['log_sha256'] = sha(r['log'])
        r['time_log_sha256'] = sha(r['time_log'])
        records.append(dict(r, source_bytes=info['bytes'], source_lines=info['lines']))
    save(REPORT / 'manifest.json', records)
    save(REPORT / 'declarations.json', declarations)
    gen.save_manifest(m)
    axioms = {n: a for r in records for n, a in r['axioms'].items()}
    save(REPORT / 'axioms.json', axioms)
    runs = [json.loads(s) for s in (REPORT / 'runs.jsonl').read_text().splitlines()]
    attempts = [json.loads(s) for s in (REPORT / 'attempts.jsonl').read_text().splitlines()]
    result = dict(modules=len(records), exported_theorems=sum(len(r['exported_theorems']) for r in records),
                  source_bytes=sum(r['source_bytes'] for r in records),
                  compiled_bytes=sum(a['bytes'] for r in records for a in r['artifacts']),
                  cpu_seconds=sum(r['cpu'] for r in records), sum_module_wall_seconds=sum(r['wall'] for r in records),
                  all_attempt_cpu_seconds=sum(r['cpu'] for r in attempts), attempts=len(attempts),
                  peak_process_rss_kib=max(r['rss_kib'] for r in records),
                  peak_sampled_rss_bytes=max(r['sampled_peak_rss_bytes'] for r in runs),
                  peak_lean_processes=max(r['peak_lean_processes'] for r in runs),
                  modules_by_kind=dict(collections.Counter(r['kind'] for r in records)),
                  manifest_sha256=sha(REPORT / 'manifest.json'), axioms_sha256=sha(REPORT / 'axioms.json'),
                  declarations_sha256=sha(REPORT / 'declarations.json'))
    save(REPORT / 'summary.json', result)
    print(json.dumps(result, indent=2), flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('action', choices=['generate', 'refresh', 'build', 'verify', 'close'])
    p.add_argument('--cases', nargs='+', choices=list(gen.CASES), default=list(gen.CASES))
    p.add_argument('--group', type=int, default=64)
    p.add_argument('--depth', type=int, default=8)
    p.add_argument('--batch', type=int, default=256)
    p.add_argument('--legacy-report', type=Path)
    p.add_argument('--jobs', type=int, default=16)
    p.add_argument('--ram-gb', type=int, default=160)
    p.add_argument('--process-gib', type=int, default=64)
    p.add_argument('--timeout', type=int, default=3600)
    p.add_argument('--module', nargs='+')
    p.add_argument('--kind', nargs='+')
    p.add_argument('--force', action='store_true')
    p.add_argument('--profile', action='store_true')
    p.add_argument('--stage', default='production')
    args = p.parse_args()
    if not 1 <= args.jobs <= 16 or not 1 <= args.ram_gb <= 170:
        p.error('At most 16 processes and 170 GB RAM are authorized')
    if args.group <= 0 or args.batch <= 0 or not 1 <= args.depth <= 12:
        p.error('Invalid generation shard parameters')
    REPORT.mkdir(parents=True, exist_ok=True)
    gen.guard()
    if args.action == 'generate':
        generate(args)
    elif args.action == 'refresh':
        refresh()
    elif args.action == 'verify':
        verify(args)
    else:
        # A second runner must not double the authorized Lean process pool.
        with (REPORT / 'runner.lock').open('a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            build(args)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
