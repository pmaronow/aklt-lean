/* Junction loss of the half-split over-count of the closed-trail MASS with a junction window (agent 62, measurement).
   pi1 = exact forward trail from u (length N, avoids c and v), keyed by (end y, last mJ directions, y seen before);
   pi2 = exact trail y -> v (length N, avoids c, v only at the end).  Glue: pi2's bonds must avoid the mJ bonds of the
   pi1 window (pi2 is checked in FULL against the window); pi2 passages at pi1-window sites become revisits (weight 1/5;
   a pi2-internal revisit there would be a third visit: killed).  Junction passage: 1/5 if y seen before in pi1.
   Usage: halves2 X N mJ xs xt  -> n=2N: exact, over-count, ratio. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define G 72
#define OFF 36
static unsigned char hb[G][G], vb[G][G];
static int vx, vy, ux, uy, cx = OFF, cy = OFF, N, mJ, mode;
static int px[80], py[80], pd[80];
static const int dx[4] = {1, 0, -1, 0}, dy[4] = {0, 1, 0, -1};
static double xs, xt, E, S;
static double *A; static int BOX;
static int used(int x, int y, int k) { if (k == 0) return hb[x][y]; if (k == 2) return hb[x-1][y]; if (k == 1) return vb[x][y]; return vb[x][y-1]; }
static void setb(int x, int y, int k, int v) { if (k == 0) hb[x][y] = v; else if (k == 2) hb[x-1][y] = v; else if (k == 1) vb[x][y] = v; else vb[x][y-1] = v; }
static int seen_before(int i) { for (int k = 0; k < i; k++) if (px[k] == px[i] && py[k] == py[i]) return 1; return 0; }
static double fwd_weight(int n) {
  double w = 1;
  for (int j = 0; j < n; j++) {
    if (seen_before(j)) { w *= 0.2; continue; }
    int ain = (j == 0) ? 2 : pd[j-1];
    w *= (pd[j] == ain) ? xs / 3 : xt / 3;
  }
  return w;
}
static long aidx(int x, int y, int code, int f) { return (((long)(x - ux + BOX) * (2 * BOX + 1) + (y - uy + BOX)) * (1L << (2 * mJ)) + code) * 2 + f; }
static void leaf2(int n) {
  /* reverse path w_0 = v .. w_n = y; forward z_i = w_{n-i} */
  int zx[80], zy[80], zd[80];
  for (int i = 0; i <= n; i++) { zx[i] = px[n - i]; zy[i] = py[n - i]; }
  for (int i = 0; i < n; i++) zd[i] = (pd[n - 1 - i] + 2) % 4; /* forward direction z_i -> z_{i+1} */
  int frev[80]; double bw = 1;
  for (int i = 1; i < n; i++) {
    frev[i] = 0; for (int k = 0; k < i; k++) if (zx[k] == zx[i] && zy[k] == zy[i]) frev[i] = 1;
    if (frev[i]) bw *= 0.2; else bw *= (zd[i] == zd[i-1]) ? xs / 3 : xt / 3;
  }
  int y0x = zx[0], y0y = zy[0];
  if (abs(y0x - ux) > BOX || abs(y0y - uy) > BOX) return;
  for (int code = 0; code < (1 << (2 * mJ)); code++) for (int f = 0; f < 2; f++) {
    double a = A[aidx(y0x, y0y, code, f)]; if (a == 0) continue;
    /* window sites: p_mJ = y, going backwards */
    int wd[16], wx[17], wy[17]; int c = code;
    for (int i = mJ - 1; i >= 0; i--) { wd[i] = c & 3; c >>= 2; }
    wx[mJ] = y0x; wy[mJ] = y0y;
    for (int i = mJ - 1; i >= 0; i--) { wx[i] = wx[i+1] - dx[wd[i]]; wy[i] = wy[i+1] - dy[wd[i]]; }
    int bad = 0;
    for (int i = 0; i < n && !bad; i++) for (int k = 0; k < mJ; k++) {
      if ((zx[i] == wx[k] && zy[i] == wy[k] && zx[i+1] == wx[k+1] && zy[i+1] == wy[k+1]) ||
          (zx[i] == wx[k+1] && zy[i] == wy[k+1] && zx[i+1] == wx[k] && zy[i+1] == wy[k])) { bad = 1; break; }
    }
    if (bad) continue;
    double corr = 1;
    for (int i = 1; i < n && !bad; i++) {
      int inw = 0; for (int k = 0; k < mJ; k++) if (zx[i] == wx[k] && zy[i] == wy[k]) inw = 1;
      if (!inw) continue;
      if (frev[i]) { bad = 1; break; }
      corr *= 0.2 / (((zd[i] == zd[i-1]) ? xs : xt) / 3);
    }
    if (bad) continue;
    int ain = mJ > 0 ? wd[mJ - 1] : -1; double J;
    if (f) J = 0.2; else J = (zd[0] == ain) ? xs / 3 : xt / 3;
    if (mJ == 0) J = xt / 3; /* unknown in-direction: max weight */
    S += a * J * bw * corr;
  }
}
static void dfs(int x, int y, int n) {
  px[n] = x; py[n] = y;
  if (mode == 0) {
    if (x == vx && y == vy && n > 0) { if (n == 2 * N) E += fwd_weight(n); return; }
    if (n == 2 * N || abs(x - vx) + abs(y - vy) > 2 * N - n) return;
  } else if (mode == 1) {
    if (n == N) {
      int code = 0; for (int i = N - mJ; i < N; i++) code = code * 4 + pd[i];
      A[aidx(x, y, code, seen_before(n))] += fwd_weight(n); return;
    }
  } else {
    if (n == N) { leaf2(n); return; }
  }
  for (int k = 0; k < 4; k++) {
    int nx = x + dx[k], ny = y + dy[k];
    if (nx == cx && ny == cy) continue;
    if (used(x, y, k)) continue;
    if (mode >= 1 && nx == vx && ny == vy) continue;
    pd[n] = k; setb(x, y, k, 1); dfs(nx, ny, n + 1); setb(x, y, k, 0);
  }
}
int main(int argc, char **argv) {
  char X = argv[1][0]; N = atoi(argv[2]); mJ = atoi(argv[3]); xs = atof(argv[4]); xt = atof(argv[5]);
  ux = OFF - 1; uy = OFF; if (X == 'B') { vx = OFF + 1; vy = OFF; } else { vx = OFF; vy = OFF + 1; }
  BOX = N; A = calloc((size_t)(2 * BOX + 1) * (2 * BOX + 1) * (1L << (2 * mJ)) * 2, sizeof(double));
  mode = 0; dfs(ux, uy, 0);
  mode = 1; dfs(ux, uy, 0);
  mode = 2; dfs(vx, vy, 0);
  printf("X=%c n=%d mJ=%d exact %.6e overcount %.6e ratio %.4f\n", X, 2 * N, mJ, E, S, S / E);
  return 0;
}
