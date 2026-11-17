import os, pathlib, subprocess, sys, time
out = pathlib.Path(sys.argv[1]); source = pathlib.Path(sys.argv[2]); cap = int(os.environ.get('CAP_GB', '8')) * 1024**2
out.mkdir(parents=True, exist_ok=True)
tc = pathlib.Path('/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin')
with (out/'con-ron.log').open('w') as stdout, (out/'progress.log').open('w') as stderr:
    start = time.monotonic(); peak = 0
    p = subprocess.Popen([str(tc/'con-ron'), '--verified', '--jobs=4', '--progress=1', str(source)], stdout=stdout, stderr=stderr)
    reason = ''
    while p.poll() is None:
        try:
            rss = next(int(s.split()[1]) for s in pathlib.Path(f'/proc/{p.pid}/status').read_text().splitlines() if s.startswith('VmRSS:'))
            peak = max(peak, rss)
        except (OSError, StopIteration): pass
        if peak > cap or time.monotonic() - start > 180:
            reason = 'memory cap' if peak > cap else 'time cap'
            p.terminate(); break
        time.sleep(.25)
    rc = p.wait()
    summary = f'con-ron exit={rc} peak_rss_kb={peak} time_s={time.monotonic()-start:.2f}' + (f' ({reason})' if reason else '')
    print(summary); (out/'result.txt').write_text(summary+'\n')
