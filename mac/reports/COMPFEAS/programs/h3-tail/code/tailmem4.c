/* tailmem4 = tailmem3 + (i) the start site u is known to be visited at time 0, so every DP passage at the site u
   (while t <= AT, when the quotient site of u is u itself) is a revisit (weight 1/5, no response); (ii) closed trails
   of length <= L found by the DFS are weighted with the per-trail OPTIMAL order of Lemma 3.2' for the h-weighted
   scalar (ascending (x_i - 1)/(x_i kappa_h(i)), exchange argument), instead of straights-first.
   tailmem3 = tailmem2 on the DIAGONAL quotient Z^2 / Lambda, Lambda = <(K,K),(K,-K)> (2K^2 sites, minimal L1 period
   P = 2K instead of K for a K x K torus); validity: mode A AT = T = 2P-3 (counts n <= 2P-3), mode B AT <= P-3, NEX >= 2P-3 (counts n > NEX, i.e. n >= 2P-2).
   RIGOROUS over-count of the tail n > NEX of the pair-response kernel (agent 59, Entries 2-5, 10) for the
   "straights first" exposure order of Lemma 3.2' (agent 62, NOTES Entry 5), contracted with h = (h_B, h_C).
   Per trail w and first-visit passage j the term is 3^{-n}(3/5)^{rev} kappa_h(j) times
     j straight:  x_s^{#straight FV passages i <= j}
     j turn:      x_s^{#straight FV passages in w} * x_t^{#turn FV passages i <= j}
   (the order "all straight FV passages in path order, then all turn FV passages in path order"; Lemma 3.2' holds
   for every order, and this is the exchange-optimal order when all pairs are alive).  Four phases:
     A: before a turn response, weights (straight x_s/3, turn x_t/3);   C: after it, (x_s/3, 1/3);
     B: before a straight response, (x_s/3, 1/3);                      D: after it, (1/3, 1/3);
   revisit 1/5 in all phases; A -> C at a turn passage with x_t kappa/3; B -> D at a straight passage with x_s kappa/3.
   Method as tailmem.c: exact DFS for the first L steps; memory-m walks on the K-torus; c killed / v absorbing while
   t <= AT; remainder after T by the L-infinity bound with left sub-eigenvectors (checked with directed rounding).
   Storage float (round-upward arithmetic: still upper bounds), DFS in double.
   Usage: tailmem2 X m L K T AT NEX cs ct a b hB hC
   mode A: AT = T = 2K-3 (counts NEX < n <= 2K-3);  mode B: AT <= K-3, NEX >= 2K-2, T > AT (counts n >= NEX). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <fenv.h>
#pragma STDC FENV_ACCESS ON

static int m, L, K, T, NEX, AT;
static double xs, xt, ca, cb, hB, hC, third, fifth;
static const int dx[4] = {1, 0, -1, 0}, dy[4] = {0, 1, 0, -1};
static int nw = 0, *wcode, *lut;
static int (*tgt)[4]; static unsigned char (*kind)[4];
static float *V[4], *Nv[4]; /* phases A, B, C, D */
static int ux, uy, vx, vy, cx, cy;

static void wpos(const int *dirs, int len, int *px, int *py) {
  px[0] = 0; py[0] = 0;
  for (int i = 0; i < len; i++) { px[i+1] = px[i] + dx[dirs[i]]; py[i+1] = py[i] + dy[dirs[i]]; }
}
static int is_trail(const int *dirs, int len) {
  int px[64], py[64]; wpos(dirs, len, px, py);
  for (int i = 0; i < len; i++) for (int j = i + 1; j < len; j++) {
    if (px[i] == px[j] && py[i] == py[j] && px[i+1] == px[j+1] && py[i+1] == py[j+1]) return 0;
    if (px[i] == px[j+1] && py[i] == py[j+1] && px[i+1] == px[j] && py[i+1] == py[j]) return 0;
  }
  return 1;
}
static int cap = 0;
static void gen(int *dirs, int len) {
  if (len == m) {
    if (nw == cap) { cap = cap ? 2 * cap : 1024; wcode = realloc(wcode, cap * sizeof(int)); }
    int c = 0; for (int i = 0; i < m; i++) c = c * 4 + dirs[i];
    wcode[nw++] = c; return;
  }
  for (int d = 0; d < 4; d++) {
    if (len > 0 && d == (dirs[len-1] + 2) % 4) continue;
    dirs[len] = d; if (!is_trail(dirs, len + 1)) continue;
    gen(dirs, len + 1);
  }
}
static void decode(int c, int *dirs) { for (int i = m - 1; i >= 0; i--) { dirs[i] = c & 3; c >>= 2; } }
static void build_windows(void) {
  int dirs[64]; gen(dirs, 0);
  lut = malloc(sizeof(int) << (2 * m)); for (long i = 0; i < (1L << (2 * m)); i++) lut[i] = -1;
  for (int i = 0; i < nw; i++) lut[wcode[i]] = i;
  tgt = malloc(nw * sizeof *tgt); kind = malloc(nw * sizeof *kind);
  for (int w = 0; w < nw; w++) {
    int px[64], py[64]; decode(wcode[w], dirs); wpos(dirs, m, px, py);
    int rev = 0; for (int i = 0; i < m; i++) if (px[i] == px[m] && py[i] == py[m]) rev = 1;
    for (int d = 0; d < 4; d++) {
      tgt[w][d] = -1; kind[w][d] = rev ? 2 : (d == dirs[m-1] ? 0 : 1);
      if (d == (dirs[m-1] + 2) % 4) continue;
      int nx = px[m] + dx[d], ny = py[m] + dy[d], bad = 0;
      for (int i = 0; i < m; i++) {
        if (px[i] == px[m] && py[i] == py[m] && px[i+1] == nx && py[i+1] == ny) bad = 1;
        if (px[i+1] == px[m] && py[i+1] == py[m] && px[i] == nx && py[i] == ny) bad = 1;
      }
      if (bad) continue;
      int nc = ((wcode[w] << 2) | d) & ((1 << (2 * m)) - 1);
      tgt[w][d] = lut[nc];
      if (tgt[w][d] < 0) { fprintf(stderr, "window lookup failed\n"); exit(1); }
    }
  }
}
static int modK(int z) { return ((z % K) + K) % K; }
static int NSITE, *nbr[4], *repx, *repy, ic, iu; static unsigned char *nearc;
static int sidx(int x, int y) { int P2 = 2 * K; int p = ((x + y) % P2 + P2) % P2, q = ((x - y) % P2 + P2) % P2; return p * K + (q - (p & 1)) / 2; }
static void build_sites(void) {
  NSITE = 2 * K * K; repx = malloc(NSITE * sizeof(int)); repy = malloc(NSITE * sizeof(int)); nearc = calloc(NSITE, 1);
  for (int d = 0; d < 4; d++) nbr[d] = malloc(NSITE * sizeof(int));
  for (int p = 0; p < 2 * K; p++) for (int r = 0; r < K; r++) {
    int q = 2 * r + (p & 1), x = (p + q) / 2, y = (p - q) / 2, s = p * K + r;
    if (sidx(x, y) != s) { fprintf(stderr, "site map error\n"); exit(1); }
    repx[s] = x; repy[s] = y;
  }
  ic = sidx(0, 0);
  for (int s = 0; s < NSITE; s++) {
    for (int d = 0; d < 4; d++) nbr[d][s] = sidx(repx[s] + dx[d], repy[s] + dy[d]);
    for (int a = -2; a <= 2; a++) for (int b = -2; b <= 2; b++) if (abs(a) + abs(b) <= 2 && sidx(repx[s] + a, repy[s] + b) == ic) nearc[s] = 1;
  }
}
/* h-weighted response of a first-visit passage at (x,y) with in-direction ain and out-direction out; with killc,
   pairs containing the torus site of c are dead */
static double kappa(int x, int y, int ain, int out, int killc) {
  int back = (ain + 2) % 4, fx[2], fy[2], nf = 0;
  for (int k = 0; k < 4; k++) if (k != back && k != out) { fx[nf] = x + dx[k]; fy[nf] = y + dy[k]; nf++; }
  int ox = x + dx[out], oy = y + dy[out];
  int Ax[3] = {fx[0], fx[0], fx[1]}, Ay[3] = {fy[0], fy[0], fy[1]}, Bx[3] = {fx[1], ox, ox}, By[3] = {fy[1], oy, oy};
  double s = 0;
  for (int q = 0; q < 3; q++) {
    if (killc && (sidx(Ax[q], Ay[q]) == ic || sidx(Bx[q], By[q]) == ic)) continue;
    int isB = (Ax[q] == Bx[q] || Ay[q] == By[q]);
    s += (q == 0 ? ca : cb) * (isB ? hB : hC);
  }
  return s;
}
/* ---------------- exact prefix by DFS ---------------- */
#define GG 112
#define OFF 56
static unsigned char hbd[GG][GG], vbd[GG][GG];
static int V1[GG][GG], V2[GG][GG];
static int pd_[128];
static int zvx, zvy, zcx = OFF, zcy = OFF;
static double closedK[256];
static int usedb(int x, int y, int k) { if (k == 0) return hbd[x][y]; if (k == 2) return hbd[x-1][y]; if (k == 1) return vbd[x][y]; return vbd[x][y-1]; }
static void setb(int x, int y, int k, int v) { if (k == 0) hbd[x][y] = v; else if (k == 2) hbd[x-1][y] = v; else if (k == 1) vbd[x][y] = v; else vbd[x][y-1] = v; }
static int pb(int x, int y, int j) { return (V1[x][y] < j) + (V2[x][y] < j); }

/* per-trail optimal-order value of a closed trail of length n (directions pd_[0..n-1] from u): Lemma 3.2' with the
   order ascending in (x_i - 1)/w_i, w_i = x_i kappa_h(i); exact dead pairs (c, or a site passed twice before i) */
static int cmpd(const void *a, const void *b) { double d = ((const double *)a)[0] - ((const double *)b)[0]; return d < 0 ? -1 : d > 0; }
static double sorted_value(int n) {
  int qx[130], qy[130]; qx[0] = OFF - 1; qy[0] = OFF;
  for (int i = 0; i < n; i++) { qx[i+1] = qx[i] + dx[pd_[i]]; qy[i+1] = qy[i] + dy[pd_[i]]; }
  double item[130][3]; int ni = 0, nrev = 0;
  for (int j = 0; j < n; j++) {
    int seen = 0; for (int i = 0; i < j; i++) if (qx[i] == qx[j] && qy[i] == qy[j]) seen++;
    if (seen) { nrev++; continue; }
    int ain = (j == 0) ? 2 : pd_[j-1], out = pd_[j];
    double xx = (out == ain) ? xs : xt;
    int back = (ain + 2) % 4, fx[2], fy[2], nf = 0;
    for (int k = 0; k < 4; k++) if (k != back && k != out) { fx[nf] = qx[j] + dx[k]; fy[nf] = qy[j] + dy[k]; nf++; }
    int ox = qx[j+1], oy = qy[j+1];
    int Ax[3] = {fx[0], fx[0], fx[1]}, Ay[3] = {fy[0], fy[0], fy[1]}, Bx[3] = {fx[1], ox, ox}, By[3] = {fy[1], oy, oy};
    double kap = 0;
    for (int q = 0; q < 3; q++) {
      int sx[2] = {Ax[q], Bx[q]}, sy[2] = {Ay[q], By[q]}, dead = 0;
      for (int t = 0; t < 2; t++) {
        if (sx[t] == zcx && sy[t] == zcy) dead = 1;
        int cnt = 0; for (int i = 0; i < j; i++) if (qx[i] == sx[t] && qy[i] == sy[t]) cnt++;
        if (cnt >= 2) dead = 1;
      }
      if (dead) continue;
      int isB = (Ax[q] == Bx[q] || Ay[q] == By[q]);
      kap += (q == 0 ? ca : cb) * (isB ? hB : hC);
    }
    double w = xx * kap;
    item[ni][0] = (w > 0) ? (xx - 1) / w : 1e300; item[ni][1] = xx; item[ni][2] = w; ni++;
  }
  qsort(item, ni, sizeof item[0], cmpd);
  double tot = 0, pre = 1;
  for (int k = 0; k < ni; k++) { tot += item[k][2] * pre; pre *= item[k][1]; }
  double base = 1; for (int i = 0; i < n; i++) base *= third; for (int i = 0; i < nrev; i++) base *= fifth * 3.0;
  return tot * base;
}
static void dfs(int x, int y, int n, double PA, double PB, double QC, double QD, int code) {
  if (x == zvx && y == zvy && n > 0) { closedK[n] += sorted_value(n); return; }
  if (n == L) {
    int w = lut[code & ((1 << (2 * m)) - 1)]; if (w < 0) { fprintf(stderr, "prefix window not found\n"); exit(1); }
    long s = (long)w * NSITE + sidx(x - OFF, y - OFF);
    V[0][s] += (float)PA; V[1][s] += (float)PB; V[2][s] += (float)QC; V[3][s] += (float)QD; return;
  }
  int *slot = (V1[x][y] == 100000) ? &V1[x][y] : &V2[x][y];
  int prior = pb(x, y, n);
  *slot = n;
  for (int k = 0; k < 4; k++) {
    int nx = x + dx[k], ny = y + dy[k];
    if (nx == zcx && ny == zcy) continue;
    if (usedb(x, y, k)) continue;
    double A2, B2, C2, D2;
    if (prior > 0) { A2 = PA * fifth; B2 = PB * fifth; C2 = QC * fifth; D2 = QD * fifth; }
    else {
      int ain = (n == 0) ? 2 : pd_[n-1];
      int back = (ain + 2) % 4, fx[2], fy[2], nf = 0;
      for (int kk = 0; kk < 4; kk++) if (kk != back && kk != k) { fx[nf] = x + dx[kk]; fy[nf] = y + dy[kk]; nf++; }
      int Ax[3] = {fx[0], fx[0], fx[1]}, Ay[3] = {fy[0], fy[0], fy[1]}, Bx[3] = {fx[1], nx, nx}, By[3] = {fy[1], ny, ny};
      double kap = 0;
      for (int q = 0; q < 3; q++) {
        if ((Ax[q] == zcx && Ay[q] == zcy) || (Bx[q] == zcx && By[q] == zcy)) continue;
        if (pb(Ax[q], Ay[q], n) >= 2 || pb(Bx[q], By[q], n) >= 2) continue;
        int isB = (Ax[q] == Bx[q] || Ay[q] == By[q]);
        kap += (q == 0 ? ca : cb) * (isB ? hB : hC);
      }
      if (k == ain) { /* straight */
        double ws = xs * third;
        A2 = PA * ws; B2 = PB * ws; C2 = QC * ws; D2 = QD * third + B2 * kap;
      } else {        /* turn */
        double wt = xt * third;
        A2 = PA * wt; B2 = PB * third; C2 = QC * third + A2 * kap; D2 = QD * third;
      }
    }
    pd_[n] = k; setb(x, y, k, 1); dfs(nx, ny, n + 1, A2, B2, C2, D2, (int)((((unsigned)code << 2) | (unsigned)k) & ((1u << (2 * m)) - 1))); setb(x, y, k, 0);
  }
  *slot = 100000;
}
/* ---------------- one DP step on the torus ---------------- */
static void step(int exact) {
  long KK = NSITE;
  for (int p = 0; p < 4; p++) memset(Nv[p], 0, nw * KK * sizeof(float));
  float f5 = (float)fifth, f3 = (float)third, fs = (float)(xs * third), ft = (float)(xt * third);
  for (int w = 0; w < nw; w++) {
    int ain = wcode[w] & 3;
    for (int d = 0; d < 4; d++) {
      int t = tgt[w][d]; if (t < 0) continue;
      float *sA = V[0] + (long)w * KK, *sB = V[1] + (long)w * KK, *sC = V[2] + (long)w * KK, *sD = V[3] + (long)w * KK;
      float *tA = Nv[0] + (long)t * KK, *tB = Nv[1] + (long)t * KK, *tC = Nv[2] + (long)t * KK, *tD = Nv[3] + (long)t * KK;
      int k = kind[w][d];
      float kg = (float)kappa(0, 0, ain, d, 0);
      const int *nb = nbr[d];
      {
        for (long s = 0; s < NSITE; s++) {
          long s2 = nb[s];
          if (k == 2) {
            tA[s2] += sA[s] * f5; tB[s2] += sB[s] * f5; tC[s2] += sC[s] * f5; tD[s2] += sD[s] * f5;
          } else {
            if (exact && s == iu) { tA[s2] += sA[s] * f5; tB[s2] += sB[s] * f5; tC[s2] += sC[s] * f5; tD[s2] += sD[s] * f5; continue; }
            float kk = kg;
            if (exact && nearc[s]) kk = (float)kappa(repx[s], repy[s], ain, d, 1);
            if (k == 0) {
              float b2 = sB[s] * fs;
              tA[s2] += sA[s] * fs; tB[s2] += b2; tC[s2] += sC[s] * fs; tD[s2] += sD[s] * f3 + b2 * kk;
            } else {
              float a2 = sA[s] * ft;
              tA[s2] += a2; tB[s2] += sB[s] * f3; tC[s2] += sC[s] * f3 + a2 * kk; tD[s2] += sD[s] * f3;
            }
          }
        }
      }
    }
  }
  for (int p = 0; p < 4; p++) { float *s = V[p]; V[p] = Nv[p]; Nv[p] = s; }
}
/* left Perron-type vector: z <- (z T_phase)/max, weights (ws, wt, 1/5) */
static double perron(double *z, double ws, double wt) {
  double *tmp = malloc(nw * sizeof(double)), lam = 0;
  for (int w = 0; w < nw; w++) z[w] = 1;
  for (int it = 0; it < 40000; it++) {
    memset(tmp, 0, nw * sizeof(double));
    for (int w = 0; w < nw; w++) for (int d = 0; d < 4; d++) { int t = tgt[w][d]; if (t < 0) continue;
      tmp[t] += z[w] * (kind[w][d] == 2 ? fifth : (kind[w][d] == 0 ? ws : wt)); }
    double mx = 0; for (int w = 0; w < nw; w++) if (tmp[w] > mx) mx = tmp[w];
    double dl = 0; for (int w = 0; w < nw; w++) { double nv = tmp[w] / mx; dl = fmax(dl, fabs(nv - z[w])); z[w] = nv; }
    lam = mx; if (dl < 1e-15 && it > 200) break;
  }
  free(tmp); return lam;
}
/* fixed point zq = (zsrc Ksrc + zq Tq)/lt; response passes of type 'resp' (0 straight, 1 turn) with source weights */
static void postvec(double *zq, const double *zsrc, int resp, double srcw, double qs, double qt, double lt) {
  double *tmp = malloc(nw * sizeof(double));
  for (int w = 0; w < nw; w++) zq[w] = 0;
  for (int it = 0; it < 40000; it++) {
    memset(tmp, 0, nw * sizeof(double));
    for (int w = 0; w < nw; w++) { int ain = wcode[w] & 3; for (int d = 0; d < 4; d++) { int t = tgt[w][d]; if (t < 0) continue;
      int k = kind[w][d];
      if (k == 2) { tmp[t] += zq[w] * fifth; continue; }
      tmp[t] += zq[w] * (k == 0 ? qs : qt);
      if (k == resp) tmp[t] += zsrc[w] * srcw * kappa(0, 0, ain, d, 0); } }
    double dl = 0; for (int w = 0; w < nw; w++) { double nv = tmp[w] / lt; dl = fmax(dl, fabs(nv - zq[w]) / (nv + 1e-300)); zq[w] = nv; }
    if (dl < 1e-14 && it > 200) break;
  }
  free(tmp);
}
int main(int argc, char **argv) {
  if (argc < 14) { fprintf(stderr, "usage\n"); return 1; }
  char X = argv[1][0]; m = atoi(argv[2]); L = atoi(argv[3]); K = atoi(argv[4]); T = atoi(argv[5]); AT = atoi(argv[6]); NEX = atoi(argv[7]);
  double cs = atof(argv[8]), ct = atof(argv[9]); ca = atof(argv[10]); cb = atof(argv[11]); hB = atof(argv[12]); hC = atof(argv[13]);
  /* the decimal constants are lower (c) / upper (a, b) bounds: move one ulp in the safe direction */
  cs = nextafter(cs, 0.0); ct = nextafter(ct, 0.0); ca = nextafter(ca, INFINITY); cb = nextafter(cb, INFINITY);
  if (!((AT == 4 * K - 3 && T == AT) || (AT <= 2 * K - 3 && NEX >= 4 * K - 3 && T > AT))) { fprintf(stderr, "invalid (AT,T,NEX)\n"); return 1; }
  if (L < m || K < m + 3 || L > AT) { fprintf(stderr, "need m <= L <= AT, K >= m+3\n"); return 1; }
  fesetround(FE_UPWARD);
  volatile double one = 1.0, three = 3.0, five = 5.0;
  xs = one / (cs < 1 ? cs : 1); xt = one / (ct < 1 ? ct : 1); third = one / three; fifth = one / five;
  build_windows(); build_sites();
  long KK = NSITE;
  fprintf(stderr, "m=%d windows=%d K=%d states/phase=%ld mem=%.2f GB\n", m, nw, K, nw * KK, 8.0 * nw * KK * 4 / 1e9);
  for (int p = 0; p < 4; p++) { V[p] = calloc(nw * KK, sizeof(float)); Nv[p] = calloc(nw * KK, sizeof(float));
    if (!V[p] || !Nv[p]) { fprintf(stderr, "alloc failed\n"); return 1; } }
  for (int i = 0; i < GG; i++) for (int j = 0; j < GG; j++) { V1[i][j] = 100000; V2[i][j] = 100000; }
  int zux = OFF - 1, zuy = OFF; if (X == 'B') { zvx = OFF + 1; zvy = OFF; } else { zvx = OFF; zvy = OFF + 1; }
  cx = 0; cy = 0; iu = sidx(zux - OFF, zuy - OFF);
  dfs(zux, zuy, 0, 1.0, 1.0, 0.0, 0.0, 0);
  printf("# tailmem4 (straights-first order, diagonal quotient, u-revisit, sorted closed DFS) X=%c m=%d L=%d K=%d T=%d AT=%d NEX=%d cs=%.6f ct=%.6f a=%.6f b=%.6f h=(%.6f,%.6f)\n",
         X, m, L, K, T, AT, NEX, cs, ct, ca, cb, hB, hC);
  printf("# E = exact (DFS), D = DP with c killed / v absorbing, F = free torus; values h-weighted upper bounds\n");
  double ex = 0;
  for (int n = 1; n <= L; n++) if (closedK[n] > 0) { printf("E %d %.12e\n", n, closedK[n]); if (n <= NEX) ex += closedK[n]; }
  printf("# EXACT(n<=min(L,NEX)) = %.12e\n", ex);
  double tail = 0; long sv = sidx(zvx - OFF, zvy - OFF), sc = ic;
  for (int n = L + 1; n <= L && n <= NEX; n++) ;
  for (int n = NEX + 1; n <= L; n++) tail += closedK[n];
  for (int t = L; t < T; t++) {
    int exact = (t + 1 <= AT);
    step(exact);
    double arr = 0;
    for (int w = 0; w < nw; w++) arr += (double)V[2][(long)w * KK + sv] + (double)V[3][(long)w * KK + sv];
    if (exact) for (int p = 0; p < 4; p++) for (int w = 0; w < nw; w++) { V[p][(long)w * KK + sv] = 0; V[p][(long)w * KK + sc] = 0; }
    if (t + 1 > NEX) tail += arr;
    if (arr > 0) printf("%c %d %.10e\n", exact ? 'D' : 'F', t + 1, arr);
    fflush(stdout);
  }
  if (T == AT) { printf("# TAIL(%d<n<=%d) <= %.9e   (mode A, no remainder)\n", NEX, T, tail); return 0; }
  /* remainder */
  fesetround(FE_TONEAREST);
  double *z[4]; for (int p = 0; p < 4; p++) z[p] = malloc(nw * sizeof(double));
  double lamA = perron(z[0], xs * third, xt * third);
  double lamB = perron(z[1], xs * third, third);
  double lt = lamA * (1 + 1e-9);
  postvec(z[2], z[0], 1, xt * third, xs * third, third, lt);
  postvec(z[3], z[1], 0, xs * third, third, third, lt);
  for (int w = 0; w < nw; w++) { z[2][w] *= 1 + 1e-7; z[3][w] *= 1 + 1e-7; }
  double lcheck = lamA * (1 + 2e-9);
  fesetround(FE_UPWARD);
  double *l[4]; for (int p = 0; p < 4; p++) l[p] = calloc(nw, sizeof(double));
  for (int w = 0; w < nw; w++) { int ain = wcode[w] & 3; for (int d = 0; d < 4; d++) { int t = tgt[w][d]; if (t < 0) continue;
    int k = kind[w][d];
    if (k == 2) { for (int p = 0; p < 4; p++) l[p][t] += z[p][w] * fifth; continue; }
    double kk = kappa(0, 0, ain, d, 0);
    if (k == 0) { double ws = xs * third; l[0][t] += z[0][w] * ws; l[1][t] += z[1][w] * ws; l[2][t] += z[2][w] * ws;
      l[3][t] += z[3][w] * third + z[1][w] * ws * kk; }
    else { double wt = xt * third; l[0][t] += z[0][w] * wt; l[1][t] += z[1][w] * third; l[2][t] += z[2][w] * third + z[0][w] * wt * kk;
      l[3][t] += z[3][w] * third; } } }
  fesetround(FE_DOWNWARD);
  int ok = 1; double worst = 0;
  for (int p = 0; p < 4; p++) for (int w = 0; w < nw; w++) { double r = lcheck * z[p][w]; if (l[p][w] > r) ok = 0; if (l[p][w] / r > worst) worst = l[p][w] / r; }
  fesetround(FE_UPWARD);
  double alpha = 0;
  for (int p = 0; p < 4; p++) for (int w = 0; w < nw; w++) for (long s = 0; s < KK; s++) {
    double a = (double)V[p][(long)w * KK + s] / z[p][w]; if (a > alpha) alpha = a; }
  double zsum = 0; for (int w = 0; w < nw; w++) zsum += z[2][w] + z[3][w];
  fesetround(FE_DOWNWARD); double den = 1.0 - lcheck; fesetround(FE_UPWARD);
  double rem = alpha * zsum * lcheck / den;
  printf("# remainder: lamA=%.9f lamB=%.9f lcheck=%.9f check=%s (max ratio %.12f) alpha=%.6e |zC+zD|=%.6e remainder<=%.6e\n",
         lamA, lamB, lcheck, ok ? "OK" : "FAILED", worst, alpha, zsum, rem);
  printf("# TAIL(n>%d) <= %.9e  (sum over t<=%d: %.9e + remainder %.6e)  %s\n", NEX, tail + rem, T, tail, rem, ok ? "" : "CHECK FAILED - NOT RIGOROUS");
  return 0;
}
