import json, os, pathlib, subprocess, time
base = pathlib.Path('/home/ubuntu/aklt/reports/FIX_STAR')
wt = '/home/ubuntu/aklt/wt/FIX_STAR'
script = '/home/ubuntu/aklt/bin/conron-check.sh'
runs = {}
def launch(key, modules, cap):
    out = base/key
    log = (base/f'{key}.out').open('w')
    p = subprocess.Popen([script, wt, str(out), *modules], stdout=log, stderr=subprocess.STDOUT, env=dict(os.environ, CAP_GB=str(cap)))
    runs[key] = dict(p=p, log=log, start=time.monotonic(), peak=0, done=False, modules=modules, cap=cap)
    print(f'Started {key}, pid={p.pid}, modules={modules}', flush=True)
launch('round2-q037', ['AKLT.W.Q037.Main'], 7)
launch('round2-q038', ['AKLT.W.Q038.Main'], 7)
launch('round2-survey', ['AKLT.W.Q016.Main','AKLT.W.Q020.Main'], 7)
while True:
    if 'q017' not in runs and (base/'round2-q017-ready').exists(): launch('q017', ['AKLT.W.Q017.Main'], 24)
    processes = {}
    for d in pathlib.Path('/proc').iterdir():
        if not d.name.isdigit(): continue
        try:
            info = dict(line.split(':',1) for line in (d/'status').read_text().splitlines() if ':' in line)
            processes[int(d.name)] = (int(info['PPid']), info['Name'].strip(), int(info.get('VmRSS','0 kB').split()[0]))
        except (OSError, ValueError, KeyError): pass
    for key,r in runs.items():
        for pid,(ppid,name,rss) in processes.items():
            if name != 'con-ron': continue
            ancestor = ppid
            while ancestor in processes and ancestor != r['p'].pid and ancestor != 0:
                ancestor = processes[ancestor][0]
            if ancestor == r['p'].pid: r['peak'] = max(r['peak'],rss)
        if not r['done'] and r['p'].poll() is not None:
            r['done'] = True; r['log'].close()
            data = dict(exit=r['p'].returncode, conron_peak_rss_kb=r['peak'], total_tool_time_s=round(time.monotonic()-r['start'],2), modules=r['modules'], cap_gb=r['cap'])
            (base/f'{key}-measurements.json').write_text(json.dumps(data,indent=2)+'\n')
            print(key, json.dumps(data), flush=True)
            print((base/f'{key}.out').read_text(), flush=True)
    if len(runs)==4 and all(r['done'] for r in runs.values()): break
    time.sleep(.25)
