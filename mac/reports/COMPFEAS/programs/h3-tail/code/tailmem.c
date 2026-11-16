/* RIGOROUS over-count of the tail n > NEX of the forward-order pair-response kernel (agent 59, Entries 5, 10),
   contracted with a positive test vector h = (h_B, h_C):  out_X = sum_{trails w: u->v, |w| > NEX} sum_{first-visit
   passages j} 3^{-n} (3/5)^{rev} X_j(w) kappa_h(j, w),   kappa_h = sum over live pairs at j of coef * h_{type}.
   (agent 62).  Method:
   (1) exact trails for the first L steps (DFS; c avoided, v absorbing, exact revisit weights and dead pairs);
   (2) memory-m walks (no reuse of the last m bonds; revisit seen in the window -> 1/5 and no response; else
       first-visit weights) on the K x K torus, c killed and v absorbing while t <= K-3 (exactly the Z^2 dynamics),
       then no killing / absorption (projection of Z^2 walks = over-count); two phases: pre (pinned weights x/3,
       before the response passage) and post (free weights 1/3, after it; carries the h-weighted response);
   (3) remainder t > T by an L-infinity bound with left sub-eigenvectors z_pre, z_post (z T <= lam z), uniform in the
       position:  sum_{t > T} mass_post(v, t) <= alpha |z_post| lam/(1-lam),  alpha = max V_T / z.
   Arithmetic: all quantities are nonnegative; FE_UPWARD rounding throughout gives upper bounds; the sub-invariance
   of z is CHECKED with upward-rounded left sides against a downward-rounded right side.
   Killing at torus-c and absorption at torus-v are applied while t <= AT.  Valid choices (agent 62 NOTES Entry 3):
   mode A: AT = T = 2K-3, counting NEX < n <= 2K-3 (a closed trail of length <= 2K-3 never meets an image of c or v);
   mode B: AT = K-3 (no image reachable), counting n >= NEX = 2K-2 up to infinity (remainder bound at T).
   Usage: tailmem X m L K T AT NEX cs ct a b hB hC   (pair X in {B,C}; constants used for start and interior alike) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <fenv.h>
#pragma STDC FENV_ACCESS ON

static int m, L, K, T, NEX, AT;
static double xs, xt, ca, cb, hB, hC, third, fifth;
static const int dx[4] = {1, 0, -1, 0}, dy[4] = {0, 1, 0, -1};
/* windows */
static int nw = 0, *wcode, *lut; /* lut[code] = index or -1 */
static int (*tgt)[4]; static unsigned char (*kind)[4]; /* kind 0 straight, 1 turn, 2 revisit */
static double *Vpre, *Vpost, *Npre, *Npost;
static int ux, uy, vx, vy, cx, cy; /* torus coordinates */

static int wpos(const int *dirs, int len, int *px, int *py) {
  px[0] = 0; py[0] = 0;
  for (int i = 0; i < len; i++) { px[i+1] = px[i] + dx[dirs[i]]; py[i+1] = py[i] + dy[dirs[i]]; }
  return 0;
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
      tgt[w][d] = lut[nc]; /* the shifted window is a trail since the new bond is not in the window */
      if (tgt[w][d] < 0) { fprintf(stderr, "window lookup failed\n"); exit(1); }
    }
  }
}
/* h-weighted response of a first-visit passage at site (x,y) (torus coords) with in-direction ain, out-direction
   out; pairs containing the site (cx,cy) are dead when killc = 1 (exact regime).  Pairs: (f,g) coef a, (f,o), (g,o)
   coef b; type B (collinear) if they share a row/column, else C. */
static double kappa(int x, int y, int ain, int out, int killc) {
  int back = (ain + 2) % 4, fx[2], fy[2], nf = 0;
  for (int k = 0; k < 4; k++) if (k != back && k != out) { fx[nf] = x + dx[k]; fy[nf] = y + dy[k]; nf++; }
  int ox = x + dx[out], oy = y + dy[out];
  int Ax[3] = {fx[0], fx[0], fx[1]}, Ay[3] = {fy[0], fy[0], fy[1]}, Bx[3] = {fx[1], ox, ox}, By[3] = {fy[1], oy, oy};
  double s = 0;
  for (int q = 0; q < 3; q++) {
    if (killc) {
      if (((Ax[q] % K + K) % K) == cx && ((Ay[q] % K + K) % K) == cy) continue;
      if (((Bx[q] % K + K) % K) == cx && ((By[q] % K + K) % K) == cy) continue;
    }
    int isB = (Ax[q] == Bx[q] || Ay[q] == By[q]);
    s += (q == 0 ? ca : cb) * (isB ? hB : hC);
  }
  return s;
}
/* ---------------- exact prefix by DFS ---------------- */
#define GG 96
#define OFF 48
static unsigned char hbd[GG][GG], vbd[GG][GG];
static int V1[GG][GG], V2[GG][GG];
static int px_[128], py_[128], pd_[128];
static int zux, zuy, zvx, zvy, zcx = OFF, zcy = OFF;
static double closedK[256]; /* exact closed (h-weighted, forward order) by length, DFS part */
static int usedb(int x, int y, int k) { if (k == 0) return hbd[x][y]; if (k == 2) return hbd[x-1][y]; if (k == 1) return vbd[x][y]; return vbd[x][y-1]; }
static void setb(int x, int y, int k, int v) { if (k == 0) hbd[x][y] = v; else if (k == 2) hbd[x-1][y] = v; else if (k == 1) vbd[x][y] = v; else vbd[x][y-1] = v; }
static int pb(int x, int y, int j) { return (V1[x][y] < j) + (V2[x][y] < j); }
static int tor(int z, int off) { return ((z - off) % K + K) % K; }
static void dfs(int x, int y, int n, double P, double Q) {
  px_[n] = x; py_[n] = y;
  if (x == zvx && y == zvy && n > 0) { closedK[n] += Q; return; }
  if (n == L) {
    int c = 0; for (int i = n - m; i < n; i++) c = c * 4 + pd_[i];
    int w = lut[c]; if (w < 0) { fprintf(stderr, "prefix window not found\n"); exit(1); }
    long s = (long)w * K * K + tor(x, OFF) * K + tor(y, OFF);
    Vpre[s] += P; Vpost[s] += Q; return;
  }
  int *slot = (V1[x][y] == 100000) ? &V1[x][y] : &V2[x][y];
  int prior = pb(x, y, n);
  *slot = n;
  for (int k = 0; k < 4; k++) {
    int nx = x + dx[k], ny = y + dy[k];
    if (nx == zcx && ny == zcy) continue;
    if (usedb(x, y, k)) continue;
    double P2, Q2;
    if (prior > 0) { P2 = P * fifth; Q2 = Q * fifth; }
    else {
      int ain = (n == 0) ? 2 : pd_[n-1];
      double xx = (k == ain) ? xs : xt;
      /* dead pairs: c, or a site passed twice before passage n */
      int back = (ain + 2) % 4, fx[2], fy[2], nf = 0;
      for (int kk = 0; kk < 4; kk++) if (kk != back && kk != k) { fx[nf] = x + dx[kk]; fy[nf] = y + dy[kk]; nf++; }
      int ox = nx, oy = ny;
      int Ax[3] = {fx[0], fx[0], fx[1]}, Ay[3] = {fy[0], fy[0], fy[1]}, Bx[3] = {fx[1], ox, ox}, By[3] = {fy[1], oy, oy};
      double kap = 0;
      for (int q = 0; q < 3; q++) {
        int dead = 0;
        if ((Ax[q] == zcx && Ay[q] == zcy) || (Bx[q] == zcx && By[q] == zcy)) dead = 1;
        if (pb(Ax[q], Ay[q], n) >= 2 || pb(Bx[q], By[q], n) >= 2) dead = 1;
        if (dead) continue;
        int isB = (Ax[q] == Bx[q] || Ay[q] == By[q]);
        kap += (q == 0 ? ca : cb) * (isB ? hB : hC);
      }
      P2 = P * (xx * third);
      Q2 = Q * third + P2 * kap;
    }
    pd_[n] = k; setb(x, y, k, 1); dfs(nx, ny, n + 1, P2, Q2); setb(x, y, k, 0);
  }
  *slot = 100000;
}
/* ---------------- one DP step on the torus ---------------- */
static double kap_tab[4][4][2]; /* [ain][out][killc-at-generic] not position dependent except c-death */
static void step(int exact) {
  long KK = (long)K * K;
  memset(Npre, 0, nw * KK * sizeof(double)); memset(Npost, 0, nw * KK * sizeof(double));
  for (int w = 0; w < nw; w++) {
    int ain = wcode[w] & 3;
    for (int d = 0; d < 4; d++) {
      int t = tgt[w][d]; if (t < 0) continue;
      double *sp = Vpre + (long)w * KK, *sq = Vpost + (long)w * KK, *tp = Npre + (long)t * KK, *tq = Npost + (long)t * KK;
      int k = kind[w][d];
      if (k == 2) {
        for (int x = 0; x < K; x++) {
          int x2 = (x + dx[d] + K) % K;
          for (int y = 0; y < K; y++) {
            int y2 = (y + dy[d] + K) % K;
            tp[x2 * K + y2] += sp[x * K + y] * fifth;
            tq[x2 * K + y2] += sq[x * K + y] * fifth;
          }
        }
      } else {
        double wp = (k == 0 ? xs : xt) * third;
        double kg = kappa(0, 0, ain, d, 0); /* generic (no c) response */
        for (int x = 0; x < K; x++) {
          int x2 = (x + dx[d] + K) % K;
          for (int y = 0; y < K; y++) {
            int y2 = (y + dy[d] + K) % K;
            double a = sp[x * K + y];
            double kk = kg;
            if (exact) { int ddx = abs(x - cx), ddy = abs(y - cy); if (K - ddx < ddx) ddx = K - ddx; if (K - ddy < ddy) ddy = K - ddy; if (ddx + ddy <= 2) kk = kappa(x, y, ain, d, 1); }
            double pn = a * wp;
            tp[x2 * K + y2] += pn;
            tq[x2 * K + y2] += sq[x * K + y] * third + pn * kk;
          }
        }
      }
    }
  }
  double *s = Vpre; Vpre = Npre; Npre = s; s = Vpost; Vpost = Npost; Npost = s;
}
int main(int argc, char **argv) {
  if (argc < 14) { fprintf(stderr, "usage\n"); return 1; }
  char X = argv[1][0]; m = atoi(argv[2]); L = atoi(argv[3]); K = atoi(argv[4]); T = atoi(argv[5]); AT = atoi(argv[6]); NEX = atoi(argv[7]);
  fesetround(FE_UPWARD);
  double cs = atof(argv[8]), ct = atof(argv[9]); ca = atof(argv[10]); cb = atof(argv[11]); hB = atof(argv[12]); hC = atof(argv[13]);
  if (!((AT == 2 * K - 3 && T == AT) || (AT <= K - 3 && NEX >= 2 * K - 2 && T > AT))) { fprintf(stderr, "invalid (AT,T,NEX) combination\n"); return 1; }
  /* x = 1/min(c,1) rounded up; 1/3, 1/5 rounded up */
  volatile double one = 1.0, three = 3.0, five = 5.0;
  xs = one / (cs < 1 ? cs : 1); xt = one / (ct < 1 ? ct : 1); third = one / three; fifth = one / five;
  if (L < m || K < m + 3) { fprintf(stderr, "need L >= m, K >= m+3\n"); return 1; }
  build_windows();
  long KK = (long)K * K;
  fprintf(stderr, "m=%d windows=%d K=%d states=%ld\n", m, nw, K, nw * KK);
  Vpre = calloc(nw * KK, sizeof(double)); Vpost = calloc(nw * KK, sizeof(double));
  Npre = calloc(nw * KK, sizeof(double)); Npost = calloc(nw * KK, sizeof(double));
  if (!Vpre || !Vpost || !Npre || !Npost) { fprintf(stderr, "alloc failed\n"); return 1; }
  for (int i = 0; i < GG; i++) for (int j = 0; j < GG; j++) { V1[i][j] = 100000; V2[i][j] = 100000; }
  zux = OFF - 1; zuy = OFF; if (X == 'B') { zvx = OFF + 1; zvy = OFF; } else { zvx = OFF; zvy = OFF + 1; }
  cx = 0; cy = 0; ux = tor(zux, OFF); uy = tor(zuy, OFF); vx = tor(zvx, OFF); vy = tor(zvy, OFF);
  dfs(zux, zuy, 0, 1.0, 0.0);
  printf("# tailmem X=%c m=%d L=%d K=%d T=%d AT=%d NEX=%d cs=%.6f ct=%.6f a=%.6f b=%.6f h=(%.6f,%.6f)\n", X, m, L, K, T, AT, NEX, cs, ct, ca, cb, hB, hC);
  printf("# n  value(h-weighted, upper bound)  [E = exact DFS, D = DP exact regime (c killed, v absorbing), F = free torus]\n");
  for (int n = 1; n <= L; n++) if (closedK[n] > 0) printf("E %d %.12e\n", n, closedK[n]);
  double tail = 0, totpost = 0;
  for (int t = L; t < T; t++) {
    int exact = (t + 1 <= AT);
    step(exact);
    double arr = 0; long sv = vx * K + vy;
    for (int w = 0; w < nw; w++) arr += Vpost[(long)w * KK + sv];
    if (exact) {
      long sc = cx * K + cy;
      for (int w = 0; w < nw; w++) { Vpre[(long)w * KK + sv] = 0; Vpost[(long)w * KK + sv] = 0; Vpre[(long)w * KK + sc] = 0; Vpost[(long)w * KK + sc] = 0; }
    }
    if (t + 1 > NEX) tail += arr;
    if (arr > 0) printf("%c %d %.12e\n", exact ? 'D' : 'F', t + 1, arr);
    fflush(stdout);
  }
  if (T == AT) { printf("# TAIL(%d<n<=%d) <= %.9e   (mode A, no remainder)\n", NEX, T, tail); return 0; }
  /* remainder: left sub-eigenvectors (computed in round-to-nearest, then checked rigorously) */
  fesetround(FE_TONEAREST);
  double *zp = malloc(nw * sizeof(double)), *zq = malloc(nw * sizeof(double)), *tmp = malloc(nw * sizeof(double));
  double kg[4][4]; for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) kg[i][j] = (j == (i + 2) % 4) ? 0 : kappa(0, 0, i, j, 0);
  for (int w = 0; w < nw; w++) zp[w] = 1;
  double lam = 0;
  for (int it = 0; it < 20000; it++) {
    memset(tmp, 0, nw * sizeof(double));
    for (int w = 0; w < nw; w++) for (int d = 0; d < 4; d++) { int t = tgt[w][d]; if (t < 0) continue;
      double wt = kind[w][d] == 2 ? fifth : (kind[w][d] == 0 ? xs : xt) * third; tmp[t] += zp[w] * wt; }
    double mx = 0; for (int w = 0; w < nw; w++) if (tmp[w] > mx) mx = tmp[w];
    double dl = fabs(mx - lam); lam = mx; for (int w = 0; w < nw; w++) zp[w] = tmp[w] / mx;
    if (dl < 1e-14 && it > 100) break;
  }
  double lt = lam * (1 + 1e-9);
  /* z_post: fixed point of z_post = (z_pre Kh + z_post Tpost)/lt */
  for (int w = 0; w < nw; w++) zq[w] = 0;
  for (int it = 0; it < 20000; it++) {
    memset(tmp, 0, nw * sizeof(double));
    for (int w = 0; w < nw; w++) { int ain = wcode[w] & 3; for (int d = 0; d < 4; d++) { int t = tgt[w][d]; if (t < 0) continue;
      if (kind[w][d] == 2) tmp[t] += zq[w] * fifth;
      else tmp[t] += zq[w] * third + zp[w] * (kind[w][d] == 0 ? xs : xt) * third * kg[ain][d]; } }
    double dl = 0; for (int w = 0; w < nw; w++) { double nv = tmp[w] / lt; dl = fmax(dl, fabs(nv - zq[w]) / (nv + 1e-300)); zq[w] = nv; }
    if (dl < 1e-13 && it > 100) break;
  }
  for (int w = 0; w < nw; w++) { zp[w] *= 1.0; zq[w] *= 1 + 1e-7; }
  double lcheck = lam * (1 + 2e-9);
  /* rigorous check: (z T)_pre <= lcheck z_pre, (z T)_post <= lcheck z_post, LHS rounded up, RHS rounded down */
  fesetround(FE_UPWARD);
  double *lp = calloc(nw, sizeof(double)), *lq = calloc(nw, sizeof(double));
  for (int w = 0; w < nw; w++) { int ain = wcode[w] & 3; for (int d = 0; d < 4; d++) { int t = tgt[w][d]; if (t < 0) continue;
    if (kind[w][d] == 2) { lp[t] += zp[w] * fifth; lq[t] += zq[w] * fifth; }
    else { double wp = (kind[w][d] == 0 ? xs : xt) * third; lp[t] += zp[w] * wp;
      double kk = kappa(0, 0, ain, d, 0); lq[t] += zq[w] * third + zp[w] * wp * kk; } } }
  fesetround(FE_DOWNWARD);
  int ok = 1; double worst = 0;
  for (int w = 0; w < nw; w++) {
    double rp = lcheck * zp[w], rq = lcheck * zq[w];
    if (lp[w] > rp || lq[w] > rq) ok = 0;
    if (lq[w] / rq > worst) worst = lq[w] / rq;
  }
  fesetround(FE_UPWARD);
  /* alpha = max V/z (V rounded up; division rounded up) */
  double alpha = 0;
  for (int w = 0; w < nw; w++) for (long s = 0; s < KK; s++) {
    double a1 = Vpre[(long)w * KK + s] / zp[w], a2 = Vpost[(long)w * KK + s] / zq[w];
    if (a1 > alpha) alpha = a1; if (a2 > alpha) alpha = a2;
  }
  double zsum = 0; for (int w = 0; w < nw; w++) zsum += zq[w];
  /* 1 - lcheck rounded down: compute lcheck/(1-lcheck) with upward rounding of numerator, downward of denominator */
  fesetround(FE_DOWNWARD); double den = 1.0 - lcheck; fesetround(FE_UPWARD);
  double rem = alpha * zsum * lcheck / den;
  printf("# remainder: lam_pre=%.9f lcheck=%.9f check=%s (worst post ratio %.9f) alpha=%.6e |z_post|=%.6e remainder<=%.6e\n",
         lam, lcheck, ok ? "OK" : "FAILED", worst, alpha, zsum, rem);
  printf("# TAIL(n>%d) <= %.9e  (sum over t<=%d: %.9e + remainder %.6e)  %s\n", NEX, tail + rem, T, tail, rem, ok ? "" : "CHECK FAILED - NOT RIGOROUS");
  return 0;
}
