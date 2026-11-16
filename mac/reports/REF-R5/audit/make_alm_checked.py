from pathlib import Path

source = Path('/Users/paronow/aklt-lean/bundle/programs/h2-trails/alm8.c').read_text()
old = 'for (int i = 1; i < 24; i++) pw4[i] = pw4[i - 1] * 4;'
new = 'for (int i = 1; i <= m; i++) pw4[i] = pw4[i - 1] * 4;'
assert old in source
source = source.replace(old, new)
old = '/* rigorous Collatz-Wielandt bound with upward rounding */'
new = '''/* The clipped, quantized binary64 vector is an exact positive rational vector. */
    for (int i = 0; i < nst; i++) xv[i] = ceil(fmax(xv[i], 0.01) * 1e12) / 1e12;
    /* rigorous Collatz-Wielandt bound with upward rounding */'''
assert old in source
source = source.replace(old, new)
old = '    fesetround(FE_TONEAREST);\n    double rate = exp(log(best) / k) * (1 + 1e-12);'
new = '''    printf("AUDIT quotient_up=%.17g quotient_hex=%a\\n", best, best);
    double hmin = xv[0], hmax = xv[0];
    for (int i = 1; i < nst; ++i) { if (xv[i] < hmin) hmin=xv[i]; if (xv[i] > hmax) hmax=xv[i]; }
    printf("AUDIT hmin=%a hmax=%a ratio_up=%.17g\\n", hmin, hmax, hmax/hmin);
    fesetround(FE_TONEAREST);
    double rate = exp(log(best) / k) * (1 + 1e-12);'''
assert old in source
source = source.replace(old, new)
Path('audit/alm8_checked.c').write_text(source)
