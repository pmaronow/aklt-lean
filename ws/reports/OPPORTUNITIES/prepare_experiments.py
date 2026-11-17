from pathlib import Path

ROOT = Path(__file__).resolve().parent
BUNDLE = Path('/home/ubuntu/aklt/manuscript/bundle/programs')
(ROOT / 'experiments').mkdir(exist_ok=True)
src = (BUNDLE / 'h2-trails/alm8.c').read_text()
src = src.replace('m = atoi(argv[1]); k = atoi(argv[2]);', '''if (argc < 5) return 2;
  m = atoi(argv[1]); k = atoi(argv[2]);
  if(m < 1 || m > 10 || k < 1 || k > 14 || m+k > 24) return 2;''')
src = src.replace('i < 24', 'i <= m')
src = src.replace('wr = 0.25', 'wr = 0.2')
src = src.replace('    fesetround(FE_TONEAREST);\n    double rate', '    printf("quotient_up=%.17g\\n",best);\n    fesetround(FE_TONEAREST);\n    double rate')
(ROOT / 'experiments/alm.c').write_text(src)
src = (BUNDLE / 'h3-tail/code/tailmem6.c').read_text()
# Repair support-aware acceptance as in the referee/adjudication. Retain the
# stronger start deletion justified by the degree argument for true trails.
src = src.replace('if (l[p][w] / r > worst) worst = l[p][w] / r;',
  'if (!isfinite(l[p][w]) || !isfinite(r) || r < 0) ok=0; if (r > 0 && l[p][w] / r > worst) worst = l[p][w] / r;')
src = src.replace('double a = (double)V[p][(long)w * KK + s] / z[p][w]; if (a > alpha) alpha = a;',
  '''double vv=(double)V[p][(long)w * KK + s];
    if(!isfinite(vv) || !isfinite(z[p][w]) || z[p][w]<0) {ok=0; continue;}
    if(z[p][w]==0) {if(vv!=0) ok=0; continue;}
    double a = vv / z[p][w]; if (a > alpha) alpha = a;''')
(ROOT / 'experiments/tail.c').write_text(src)
