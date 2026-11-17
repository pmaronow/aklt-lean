#!/usr/bin/env python3
"""Fresh-process module-system H1 builds with hash-checked resumable receipts.

Only artifacts in this release's normal Lake directory are used. Each accepted
module has separate stdout, stderr, GNU-time, source, artifact, and axiom receipts.
"""
from __future__ import annotations
import argparse, concurrent.futures, fcntl, gzip, hashlib, json, os, re
import shutil, signal, subprocess, threading, time
from pathlib import Path
from locations import REPORT_DIR

ROOT = Path(__file__).resolve().parents[4]
REPORT = REPORT_DIR
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
MEMORY_LIMIT = 270_000_000_000
MAX_JOBS = 36
lock = threading.Lock()
abort = threading.Event()
live_rss = {}
_files = {}
_closures = {}
_pins = None


def resource_limits():
    return MAX_JOBS, MEMORY_LIMIT


def source_bytes(path):
    if path.exists():
        return path.read_bytes()
    return gzip.decompress(Path(str(path) + '.gz').read_bytes())


def source_digest(path):
    return hashlib.sha256(source_bytes(path)).hexdigest()


def compact_source(path):
    if not path.is_relative_to(ROOT / 'CertData/H1/Generated') or not path.exists():
        return
    payload = path.read_bytes()
    target = Path(str(path) + '.gz')
    temp = target.with_suffix('.gz.tmp')
    temp.write_bytes(gzip.compress(payload, compresslevel=9, mtime=0))
    temp.replace(target)
    path.unlink()


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda: f.read(2**20), b''):
            h.update(chunk)
    return h.hexdigest()


def file_digest(path):
    st = path.stat()
    stamp = (st.st_mtime_ns, st.st_size)
    cached = _files.get(str(path))
    if cached and cached[0] == stamp:
        return cached[1]
    result = sha(path)
    _files[str(path)] = (stamp, result)
    return result


def artifact_path(module):
    return ROOT / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')


def artifact_hashes(module):
    obj = artifact_path(module)
    if not obj.is_file() or obj.is_symlink():
        raise FileNotFoundError('missing local module artifact: ' + str(obj))
    paths = [obj] + [Path(str(obj) + suffix) for suffix in ['.private', '.server']]
    return {str(p.relative_to(ROOT)): file_digest(p) for p in paths if p.is_file()}


def imports(text):
    return re.findall(r'^(?:public )?import (?:all )?([\w.]+)', text, re.M)


def library_fingerprint(module, seen=None):
    if module in _closures:
        return _closures[module]
    source = ROOT / (module.replace('.', '/') + '.lean')
    if not source.is_file():
        # External Lean/Mathlib dependencies are pinned, prebuilt, and read-only.
        if module.startswith(('AKLT.', 'CertData.')):
            raise FileNotFoundError('missing first-party dependency: ' + module)
        return ''
    if module.startswith('CertData.H1.Generated.'):
        raise ValueError('generated dependency omitted from manifest: ' + module)
    parts = [module, file_digest(source), json.dumps(artifact_hashes(module), sort_keys=True)]
    for dep in imports(source.read_text()):
        parts.append(library_fingerprint(dep))
    result = hashlib.sha256(''.join(parts).encode()).hexdigest()
    _closures[module] = result
    return result


def build_key(source, dependencies):
    global _pins
    payload = source_bytes(source)
    generated = {d['module'] for d in dependencies}
    core = ''.join(library_fingerprint(m) for m in imports(payload.decode()) if m not in generated)
    if _pins is None:
        _pins = ''.join(file_digest(ROOT / name) for name in ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml'])
    material = 'h1-module-key-v3' + hashlib.sha256(payload).hexdigest() + _pins + core
    material += ''.join(d['key'] + json.dumps(d['artifact_hashes'], sort_keys=True) for d in dependencies)
    return hashlib.sha256(material.encode()).hexdigest(), core


def group_rss(pid):
    try:
        status = Path(f'/proc/{pid}/status').read_text()
        match = re.search(r'^VmRSS:\s*(\d+) kB', status, re.M)
        own = int(match[1]) * 1024 if match else 0
        children = Path(f'/proc/{pid}/task/{pid}/children').read_text().split()
        return own + sum(group_rss(int(child)) for child in children)
    except (FileNotFoundError, ProcessLookupError):
        return 0


def available_memory():
    return int(re.search(r'^MemAvailable:\s*(\d+)', Path('/proc/meminfo').read_text(), re.M)[1]) * 1024


def guard():
    if shutil.disk_usage(ROOT).free < 100 * 2**30:
        abort.set()
        raise RuntimeError('ABORT: free disk below 100 GiB')
    if available_memory() < 40_000_000_000:
        abort.set()
        raise MemoryError('ABORT: available physical memory below 40 GB')


def metrics(path):
    text = path.read_text()
    def number(pattern):
        match = re.search(pattern, text)
        return float(match[1]) if match else None
    return dict(user_seconds=number(r'User time \(seconds\): ([0-9.]+)'),
                system_seconds=number(r'System time \(seconds\): ([0-9.]+)'),
                max_rss_kib=number(r'Maximum resident set size \(kbytes\): (\d+)'))


def axiom_audit(text, source):
    records = {}
    pattern = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    for name, values in re.findall(pattern, text, re.S):
        axioms = sorted(v.strip() for v in values.split(',') if v.strip())
        if not set(axioms) <= ALLOWED:
            raise RuntimeError('forbidden axiom: ' + name + ': ' + repr(axioms))
        if name in records:
            raise RuntimeError('duplicate theorem audit: ' + name)
        records[name] = axioms
    expected = set()
    namespaces = []
    for line in source.splitlines():
        namespace = re.match(r'^namespace\s+([\w.]+)\s*$', line)
        end = re.match(r'^end\s+([\w.]+)\s*$', line)
        theorem = re.match(r'^(?:public )?theorem\s+(\w+)', line)
        if namespace:
            namespaces.append(namespace[1])
        elif end:
            if not namespaces or namespaces.pop() != end[1]:
                raise RuntimeError('unexpected generated namespace boundary')
        elif theorem:
            expected.add('.'.join([*namespaces, theorem[1]]))
    exports = len(expected)
    prints = len(re.findall(r'^#print axioms\s+', source, re.M))
    if exports != prints or len(records) != prints:
        raise RuntimeError(f'incomplete axiom audit: {exports} theorems, {prints} requests, {len(records)} results')
    if set(records) != expected:
        raise RuntimeError('axiom transcript does not cover the exact exported theorem names')
    return records


def main():
    global REPORT, MEMORY_LIMIT
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('manifest', type=Path)
    ap.add_argument('--jobs', type=int, default=32)
    ap.add_argument('--cap-gib', type=float, default=8)
    ap.add_argument('--ram-gb', type=float, default=270, help='Aggregate memory reservation/RSS limit in decimal GB, at most 270')
    ap.add_argument('--seconds', type=int, default=14400)
    ap.add_argument('--kinds', nargs='+')
    ap.add_argument('--force', action='store_true')
    ap.add_argument('--force-kinds', nargs='+', default=[])
    ap.add_argument('--jobs-file', type=Path)
    ap.add_argument('--compact-sources', action='store_true')
    ap.add_argument('--report-dir', type=Path)
    ap.add_argument('--progress-file', type=Path, help='separate progress snapshot for a concurrent pilot frontier')
    ap.add_argument('--profile', action='store_true', help='Lean profiling for isolated performance diagnostics')
    args = ap.parse_args()
    if not 1 <= args.jobs <= MAX_JOBS:
        ap.error('at most 36 Lean processes')
    if args.cap_gib <= 0:
        ap.error('the memory cap must be positive')
    if not 0 < args.ram_gb <= 270:
        ap.error('the aggregate memory limit must be positive and at most 270 GB')
    MEMORY_LIMIT = int(args.ram_gb * 1_000_000_000)
    signal.signal(signal.SIGINT, lambda *_: abort.set())
    signal.signal(signal.SIGTERM, lambda *_: abort.set())
    REPORT = args.report_dir or REPORT
    REPORT.mkdir(parents=True, exist_ok=True)
    logs = REPORT / 'logs'
    logs.mkdir(exist_ok=True)
    locks = REPORT / 'module-locks'
    locks.mkdir(exist_ok=True)
    receipts = REPORT / 'receipts'
    receipts.mkdir(exist_ok=True)
    plan = json.loads(args.manifest.read_text())
    alljobs = {job['module']: job for job in plan['jobs']}
    wanted = set(alljobs)
    if args.kinds:
        wanted = {m for m, j in alljobs.items() if j['kind'] in args.kinds}
        def add_deps(m):
            for d in alljobs[m]['deps']:
                if d not in wanted:
                    wanted.add(d)
                    add_deps(d)
        for m in list(wanted):
            add_deps(m)
    jobs = {m: alljobs[m] for m in wanted}
    if args.ram_gb < 270:
        oversized = [m for m, j in jobs.items() if j.get('cap_gib', args.cap_gib) * 2**30 > MEMORY_LIMIT]
        if oversized:
            ap.error('a module reservation exceeds --ram-gb: ' + oversized[0])
    statepath = REPORT / ('state-' + args.manifest.stem + '.json')
    state = {}
    events = REPORT / 'events.jsonl'
    if events.exists():
        for line in events.read_text().splitlines():
            try:
                record = json.loads(line)
            except json.JSONDecodeError:
                continue  # A terminated process may have left an incomplete last line.
            if record.get('exit') == 0:
                state[record['module']] = record
    env = os.environ.copy()
    env['PATH'] = str(Path.home() / '.elan/bin') + ':' + env['PATH']
    env['LEAN_NUM_THREADS'] = '1'
    env['LEAN_PATH'] = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, env=env, text=True).strip()
    prefix = subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'], cwd=ROOT, env=env, text=True).strip()
    lean = str(Path(prefix) / 'bin/lean')
    peak_rss = 0
    minimum_available = available_memory()
    minimum_disk = shutil.disk_usage(ROOT).free
    begin = time.monotonic()

    def run(module):
        nonlocal peak_rss, minimum_available, minimum_disk
        guard()
        job = jobs[module]
        source = ROOT / (module.replace('.', '/') + '.lean')
        obj = artifact_path(module)
        obj.parent.mkdir(parents=True, exist_ok=True)
        cap = job.get('cap_gib', args.cap_gib)
        with (locks / (module + '.lock')).open('a') as module_lock:
            fcntl.flock(module_lock, fcntl.LOCK_EX)
            key, core = build_key(source, [state[d] for d in job['deps']])
            old = state.get(module)
            receiptpath = receipts / (module + '.json')
            if receiptpath.exists():
                old = json.loads(receiptpath.read_text())
            elif obj.exists() and (not old or old.get('key') != key) and events.exists():
                for line in reversed(events.read_text().splitlines()):
                    try:
                        candidate = json.loads(line)
                    except json.JSONDecodeError:
                        continue
                    if candidate.get('module') == module and candidate.get('exit') == 0:
                        old = candidate
                        break
            if not args.force and job['kind'] not in args.force_kinds and old and old.get('key') == key and obj.exists() and artifact_hashes(module) == old.get('artifact_hashes'):
                if args.compact_sources:
                    compact_source(source)
                return module, dict(old, replayed=True)
            if not source.exists():
                source.write_bytes(source_bytes(source))
            payload = source.read_text()
            stamp = str(time.time_ns())
            stem = logs / (module.replace('.', '__') + '-' + stamp)
            stdout = Path(str(stem) + '.stdout')
            stderr = Path(str(stem) + '.stderr')
            timing = Path(str(stem) + '.time')
            cmd = ['/usr/bin/time', '-v', '-o', str(timing), '/usr/bin/prlimit',
                   f'--as={max(128, int(2 * cap)) * 2**30}', '--', lean,
                   *(['--profile'] if args.profile else []),
                   '-DElab.async=false', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
                   '-o', str(obj), str(source)]
            started = time.monotonic()
            with stdout.open('w') as out, stderr.open('w') as err:
                process = subprocess.Popen(cmd, cwd=ROOT, env=env, stdout=out, stderr=err, start_new_session=True)
                try:
                    while process.poll() is None:
                        guard()
                        rss = group_rss(process.pid)
                        with lock:
                            live_rss[module] = rss
                            aggregate = sum(live_rss.values())
                            peak_rss = max(peak_rss, aggregate)
                            minimum_available = min(minimum_available, available_memory())
                            minimum_disk = min(minimum_disk, shutil.disk_usage(ROOT).free)
                        if rss > cap * 2**30 or aggregate > MEMORY_LIMIT:
                            raise MemoryError('RSS limit exceeded: ' + module)
                        if abort.is_set() or time.monotonic() - started > args.seconds:
                            raise TimeoutError(module)
                        time.sleep(.5)
                except BaseException:
                    abort.set()
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                    raise
                finally:
                    with lock:
                        live_rss.pop(module, None)
            record = dict(module=module, kind=job['kind'], exit=process.returncode,
                          started_at=int(stamp) / 1e9, finished_at=time.time(),
                          wall_seconds=round(time.monotonic() - started, 4),
                          command=cmd, log=str(stdout), stderr=str(stderr), timing=str(timing),
                          key=key, key_version=3, source_sha256=source_digest(source),
                          library_closure=core, replayed=False, manifest=str(args.manifest),
                          cap_gib=cap, **metrics(timing))
            if process.returncode:
                with lock:
                    with (REPORT / 'failures.jsonl').open('a') as f:
                        f.write(json.dumps(record, sort_keys=True) + '\n')
                abort.set()
                raise RuntimeError('Lean failed ' + module + '\n' + stdout.read_text()[-5000:] + stderr.read_text()[-5000:])
            if record['max_rss_kib'] > cap * 2**20:
                abort.set()
                raise MemoryError('GNU-time RSS exceeded cap: ' + module)
            audits = axiom_audit(stdout.read_text(), payload)
            auditpath = Path(str(stem) + '.axioms.json')
            auditpath.write_text(json.dumps(audits, sort_keys=True) + '\n')
            record.update(axioms=sorted({a for values in audits.values() for a in values}),
                          theorem_count=len(audits), axiom_audit=str(auditpath),
                          axiom_audit_sha256=sha(auditpath), artifact_hashes=artifact_hashes(module),
                          artifact_sha256=sha(obj))
            with lock:
                with events.open('a') as f:
                    fcntl.flock(f, fcntl.LOCK_EX)
                    f.write(json.dumps(record, sort_keys=True) + '\n')
                    f.flush()
                temp = receiptpath.with_suffix('.json.tmp')
                temp.write_text(json.dumps(record, sort_keys=True) + '\n')
                temp.replace(receiptpath)
            if args.compact_sources:
                compact_source(source)
            return module, record

    done = set()
    pending = set(jobs)
    running = {}
    replayed = 0
    max_running = 0
    last_progress = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_JOBS) as pool:
        while pending or running:
            if abort.is_set():
                raise RuntimeError('another module failed; pending work canceled')
            concurrency = int(args.jobs_file.read_text().strip()) if args.jobs_file and args.jobs_file.exists() else args.jobs
            if not 1 <= concurrency <= MAX_JOBS:
                raise ValueError('jobs setting must be between 1 and 36')
            ready = [m for m in pending if all(d in done for d in jobs[m]['deps'])]
            ready.sort(key=lambda m: (jobs[m]['kind'] not in ['constructor_rows', 'gram_rows'], -jobs[m].get('n', 0), m))
            reserved = sum(jobs[m].get('cap_gib', args.cap_gib) * 2**30 for m in running.values())
            with lock:
                outstanding = sum(max(0, jobs[m].get('cap_gib', args.cap_gib) * 2**30 - live_rss.get(m, 0)) for m in running.values())
            for module in ready:
                if len(running) >= concurrency:
                    break
                reservation = jobs[module].get('cap_gib', args.cap_gib) * 2**30
                if reserved + reservation > MEMORY_LIMIT or available_memory() - outstanding - reservation < 40_000_000_000:
                    continue
                pending.remove(module)
                running[pool.submit(run, module)] = module
                reserved += reservation
                outstanding += reservation
            max_running = max(max_running, len(running))
            if not running:
                if not ready:
                    raise RuntimeError('cycle or missing dependency')
                guard()
                time.sleep(2)
                continue
            finished, _ = concurrent.futures.wait(running, timeout=2, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in finished:
                try:
                    module, result = future.result()
                except BaseException:
                    abort.set()
                    raise
                del running[future]
                state[module] = result
                done.add(module)
                replayed += int(result['replayed'])
            if len(done) % 100 == 0 and finished or time.monotonic() - last_progress > 30 or not pending and not running:
                progress = dict(completed=len(done), total=len(jobs), replayed=replayed,
                                running=len(running), wall_seconds=round(time.monotonic() - begin, 1),
                                peak_sampled_aggregate_rss_bytes=peak_rss)
                print(json.dumps(progress), flush=True)
                (args.progress_file or REPORT / 'progress.json').write_text(json.dumps(progress, indent=2) + '\n')
                temp = statepath.with_suffix('.tmp')
                temp.write_text(json.dumps(state, sort_keys=True))
                temp.replace(statepath)
                last_progress = time.monotonic()
    summary = dict(manifest=str(args.manifest), modules=len(jobs), replayed=replayed,
                   wall_seconds=time.monotonic() - begin, jobs=args.jobs, max_concurrent_jobs=max_running,
                   cap_gib=args.cap_gib, peak_sampled_aggregate_rss_bytes=peak_rss,
                   minimum_available_bytes=minimum_available, minimum_free_disk_bytes=minimum_disk,
                   completed_at=time.time(), compact_sources=args.compact_sources,
                   resource_limits=dict(processes=MAX_JOBS, memory_bytes=MEMORY_LIMIT))
    (REPORT / ('run-' + args.manifest.stem + '.json')).write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary), flush=True)


if __name__ == '__main__':
    main()
