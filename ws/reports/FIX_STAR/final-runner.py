import json, os, pathlib, subprocess, time
base = pathlib.Path('/home/ubuntu/aklt/reports/FIX_STAR')
wt = '/home/ubuntu/aklt/wt/FIX_STAR'
script = '/home/ubuntu/aklt/bin/conron-check.sh'
runs = {}
env = dict(os.environ, CAP_GB='7')
def launch(q):
    out = base/f'final_{q.lower()}'
    log = (base/f'final_{q.lower()}.out').open('w')
    p = subprocess.Popen([script, wt, str(out), f'AKLT.W.{q}.Main'], stdout=log, stderr=subprocess.STDOUT, env=env)
    runs[q] = dict(p=p, log=log, start=time.monotonic(), peak=0, done=False)
    print(f'Started supplied tool for {q}, pid={p.pid}', flush=True)
launch('Q038')
while True:
    if 'Q037' not in runs and (base/'q037-ready').exists(): launch('Q037')
    processes = {}
    for d in pathlib.Path('/proc').iterdir():
        if not d.name.isdigit(): continue
        try:
            info = dict(line.split(':',1) for line in (d/'status').read_text().splitlines() if ':' in line)
            processes[int(d.name)] = (int(info['PPid']), info['Name'].strip(), int(info.get('VmRSS','0 kB').split()[0]))
        except (OSError, ValueError, KeyError): pass
    for q,r in runs.items():
        for pid,(ppid,name,rss) in processes.items():
            if name != 'con-ron': continue
            ancestor = ppid
            while ancestor in processes and ancestor != r['p'].pid and ancestor != 0:
                ancestor = processes[ancestor][0]
            if ancestor == r['p'].pid: r['peak'] = max(r['peak'],rss)
        if not r['done'] and r['p'].poll() is not None:
            r['done'] = True; r['log'].close()
            data = dict(exit=r['p'].returncode, conron_peak_rss_kb=r['peak'], total_tool_time_s=round(time.monotonic()-r['start'],2))
            (base/f'final_{q.lower()}_measurements.json').write_text(json.dumps(data,indent=2)+'\n')
            print(q, json.dumps(data), flush=True)
            print((base/f'final_{q.lower()}.out').read_text(), flush=True)
    if len(runs)==2 and all(r['done'] for r in runs.values()): break
    time.sleep(.25)
