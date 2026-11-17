#!/usr/bin/env python3
"""Conservative hard memory reservations + inherited 16-CPU affinity.

No cgroup privileges are available. Each leaf gets a hard RLIMIT_AS; simultaneous
reservations plus this supervisor's 512 MiB hard limit sum to <=32 GiB.
Only direct, non-forking tool processes are admitted. A descendant is terminated
and invalidates the run. This is not Palomar's authenticated cgroup supervisor.
"""
import argparse
import ctypes
import fcntl
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import time

GIB = 1024**3
REPORT = Path('/home/ubuntu/aklt/reports/PAL_FIT')
CPUS = set(range(16))


def procstats(pid):
    p = Path('/proc') / str(pid)
    status = {}
    try:
        for line in (p / 'status').read_text().splitlines():
            key, _, val = line.partition(':')
            status[key] = val.strip()
        raw = (p / 'stat').read_text()
        fields = raw[raw.rfind(')') + 2:].split()
        childset = set()
        for task in (p / 'task').iterdir():
            try:
                childset.update((task / 'children').read_text().split())
            except FileNotFoundError:
                pass
        childlist = sorted(childset, key=int)
        return {'rss': int(status.get('VmRSS', '0 kB').split()[0]) * 1024,
                'hwm': int(status.get('VmHWM', '0 kB').split()[0]) * 1024,
                'vms': int(status.get('VmSize', '0 kB').split()[0]) * 1024,
                'threads': int(status.get('Threads', '0')),
                'cpu_ticks': int(fields[11]) + int(fields[12]),
                'cpus': status.get('Cpus_allowed_list'), 'children': childlist}
    except (FileNotFoundError, ProcessLookupError):
        return None


def killgroup(pid):
    # A nested sandbox may create a new process group. Kill its descendants
    # explicitly rather than relying on the original process group alone.
    descendants = []
    pending = [pid]
    seen = set()
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        stat = procstats(current)
        if stat:
            children = [int(x) for x in stat['children']]
            descendants.extend(children)
            pending.extend(children)
    for current in reversed(descendants):
        try:
            os.kill(current, signal.SIGKILL)
        except ProcessLookupError:
            pass
    try:
        os.killpg(pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def prepare():
    os.sched_setaffinity(0, CPUS)
    assert os.sched_getaffinity(0) == CPUS
    resource.setrlimit(resource.RLIMIT_AS, (64 * 1024**2, 32 * GIB))


def run_one(name, argv, cwd, seconds=1800, worker_gib=31, env=None, stdout=None, shared_small=False):
    assert 0 < worker_gib <= 31.5
    # This campaign runs one harness at a time; lock makes that verifiable.
    lock = (REPORT / 'measurements' / 'active.lock').open('w')
    if shared_small:
        assert worker_gib <= .5
        # 30 GiB build workers + .5 GiB build supervisor + .125 GiB queue
        # + .5 GiB this supervisor + .5 GiB this worker = 31.625 GiB.
    else:
        fcntl.flock(lock, fcntl.LOCK_EX)
    resource.setrlimit(resource.RLIMIT_AS, (512 * 1024**2, 32 * GIB))
    limit = int(worker_gib * GIB)
    dest = REPORT / 'measurements' / name
    dest.mkdir(parents=True, exist_ok=True)
    def setup():
        os.setsid()
        os.sched_setaffinity(0, CPUS)
        resource.setrlimit(resource.RLIMIT_AS, (limit,) * 2)
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        if ctypes.CDLL(None, use_errno=True).prctl(4, 0, 0, 0, 0) != 0:
            raise OSError('PR_SET_DUMPABLE failed')
    environment = os.environ.copy()
    environment.update({'LEAN_NUM_THREADS': '1', 'LEAN_ABORT_ON_PANIC': '1',
                        'OMP_NUM_THREADS': '1', 'OPENBLAS_NUM_THREADS': '1'})
    environment['PATH'] = '/home/ubuntu/.elan/bin:' + environment.get('PATH', '')
    if env:
        environment.update(env)
    out = open(stdout or dest / 'stdout.log', 'wb')
    err = open(dest / 'stderr.log', 'wb')
    started = time.monotonic()
    usage0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    child = subprocess.Popen(argv, cwd=cwd, env=environment, stdout=out, stderr=err,
                             preexec_fn=setup)
    resource.setrlimit(resource.RLIMIT_AS, (512 * 1024**2,) * 2)
    record = {'name': name, 'argv': argv, 'cwd': str(cwd),
              'started_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
              'hard_limit_worker_as_bytes': limit,
              'hard_limit_supervisor_as_bytes': 512 * 1024**2,
              'total_hard_reservation_bytes': limit + 512 * 1024**2,
              'affinity_cpus': sorted(CPUS), 'timeout_s': seconds,
              'cgroup_enforced': False, 'swap_limit_enforced': False,
              'core_dumps_disabled': True,
              'shared_small_reservation': shared_small,
              'unexpected_descendants': [], 'timeout': False,
              'peak_rss_bytes_sampled': 0, 'peak_vms_bytes_sampled': 0,
              'max_threads': 0, 'max_cpu_ticks': 0}
    trace = (dest / 'samples.jsonl').open('w')
    check_at = started
    final_usage = None
    while True:
        waited, status, usage = os.wait4(child.pid, os.WNOHANG)
        if waited:
            child.returncode = os.waitstatus_to_exitcode(status)
            final_usage = usage
            break
        now = time.monotonic()
        stat = procstats(child.pid)
        if stat:
            stat['elapsed_s'] = round(now - started, 4)
            record['peak_rss_bytes_sampled'] = max(record['peak_rss_bytes_sampled'], stat['rss'], stat['hwm'])
            record['peak_vms_bytes_sampled'] = max(record['peak_vms_bytes_sampled'], stat['vms'])
            record['max_threads'] = max(record['max_threads'], stat['threads'])
            record['max_cpu_ticks'] = max(record['max_cpu_ticks'], stat['cpu_ticks'])
            if now >= check_at:
                trace.write(json.dumps(stat) + '\n')
                trace.flush()
                check_at = now + 1
            if stat['children']:
                record['unexpected_descendants'] = stat['children']
                killgroup(child.pid)
            if stat['cpus'] != '0-15':
                record['affinity_violation'] = stat['cpus']
                killgroup(child.pid)
        if now - started > seconds:
            record['timeout'] = True
            killgroup(child.pid)
        time.sleep(.05)
    trace.close()
    out.close()
    err.close()
    usage1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    record.update(exit_code=child.returncode, wall_s=time.monotonic() - started,
                  user_s=usage1.ru_utime - usage0.ru_utime,
                  system_s=usage1.ru_stime - usage0.ru_stime,
                  supervisor_max_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    record['peak_rss_bytes'] = max(record['peak_rss_bytes_sampled'], final_usage.ru_maxrss * 1024)
    record['wait4_user_s'] = final_usage.ru_utime
    record['wait4_system_s'] = final_usage.ru_stime
    record['cpu_s'] = record['user_s'] + record['system_s']
    record['accepted_envelope'] = not (record['unexpected_descendants'] or record.get('affinity_violation'))
    (dest / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
    with (REPORT / 'measurements' / 'ledger.jsonl').open('a') as ledger:
        ledger.write(json.dumps(record) + '\n')
    with (REPORT / 'report.md').open('a') as report:
        report.write(f"\nMeasurement `{name}`: wall {record['wall_s']:.3f} s; CPU {record['cpu_s']:.3f} s; "
                     f"sampled peak RSS {record['peak_rss_bytes_sampled']/GIB:.3f} GiB; "
                     f"exit {child.returncode}; timeout {record['timeout']}; "
                     f"envelope valid {record['accepted_envelope']}. "
                     f"Receipt: `measurements/{name}/result.json`.\n")
    fcntl.flock(lock, fcntl.LOCK_UN)
    lock.close()
    return record


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--name', required=True)
    parser.add_argument('--cwd', default=os.getcwd())
    parser.add_argument('--seconds', type=float, default=1800)
    parser.add_argument('--worker-gib', type=float, default=31)
    parser.add_argument('--env', action='append', default=[])
    parser.add_argument('--stdout')
    parser.add_argument('--shared-small', action='store_true')
    parser.add_argument('argv', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    prepare()
    argv = args.argv
    if argv and argv[0] == '--':
        argv = argv[1:]
    record = run_one(args.name, argv, args.cwd, args.seconds, args.worker_gib,
                     dict(x.split('=', 1) for x in args.env), args.stdout,args.shared_small)
    print(json.dumps(record, indent=2))
    return int(record['exit_code'] != 0 or not record['accepted_envelope'])

if __name__ == '__main__':
    sys.exit(main())
