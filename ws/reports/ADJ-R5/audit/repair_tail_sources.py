"""Produce reviewable support-aware copies; the production inputs stay untouched."""
from pathlib import Path
folder=Path('/home/ubuntu/aklt/manuscript/bundle/programs/h3-tail/code')
for version in (4,5,6):
    s=(folder/f'tailmem{version}.c').read_text()
    s=s.replace('validity: mode A AT = T = 2P-3 (counts n <= 2P-3), mode B AT <= P-3, NEX >= 2P-3 (counts n > NEX, i.e. n >= 2P-2).',
                'validity: mode A trail bound only for n <= 2P-5; mode B AT <= P-3 dominates n > AT. The chosen T=AT=2P-3 also prints extra walk masses.')
    s=s.replace('mode A: AT = T = 2K-3 (counts NEX < n <= 2K-3);  mode B: AT <= K-3, NEX >= 2K-2, T > AT (counts n >= NEX).',
                'diagonal quotient P=2K; mode A valid only through 2P-5; mode B AT <= P-3. Use per-n outputs and a checked valid cutoff.')
    old='  for (int p = 0; p < 4; p++) for (int w = 0; w < nw; w++) { double r = lcheck * z[p][w]; if (l[p][w] > r) ok = 0; if (l[p][w] / r > worst) worst = l[p][w] / r; }'
    new='''  if (!isfinite(lcheck) || !(0 < lcheck && lcheck < 1)) { fprintf(stderr,"invalid lambda\\n"); return 2; }
  for (int p = 0; p < 4; p++) for (int w = 0; w < nw; w++) {
    if (!isfinite(z[p][w]) || z[p][w] < 0 || !isfinite(l[p][w]) || l[p][w] < 0) { ok=0; continue; }
    double r = lcheck*z[p][w];
    if (!isfinite(r) || l[p][w] > r) ok=0;
    if (r > 0 && l[p][w]/r > worst) worst=l[p][w]/r;
  }
  if (!ok) { fprintf(stderr,"sub-invariance check failed\\n"); return 2; }'''
    assert old in s
    s=s.replace(old,new)
    old='    double a = (double)V[p][(long)w * KK + s] / z[p][w]; if (a > alpha) alpha = a; }'
    new='''    double v=(double)V[p][(long)w*KK+s];
    if (!isfinite(v) || v<0) { fprintf(stderr,"invalid terminal value\\n"); return 2; }
    if (z[p][w]==0) { if (v!=0) { fprintf(stderr,"terminal support mismatch\\n"); return 2; } continue; }
    double a=v/z[p][w]; if (!isfinite(a)) return 2; if(a>alpha)alpha=a;
  }'''
    assert old in s;s=s.replace(old,new)
    if version==5:
        s=s.replace('if (k == 2) continue; /* third visit */', 'if (D0 >= 0 && k == 2) continue; /* third visit in a split class */')
    s=s.replace('(mode A, no remainder)', '(mode A WALK MASS, no remainder; trail bound only n<=4K-5)')
    Path(f'audit/tailmem{version}_checked.c').write_text(s)
