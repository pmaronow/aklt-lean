/* Half-split over-count of the closed-trail MASS (agent 62, measurement).
   Pair (u,v), centre c=(0,0) removed; X=B: u=(-1,0), v=(1,0); X=C: u=(-1,0), v=(0,1).
   Mass of a closed trail u -> v (first arrival at v, avoids c), length n:  prod over passages j=0..n-1 of
     first visit: x_type/3 (type straight/turn w.r.t. in-direction; passage 0 has in-direction West = from c),
     revisit (site visited earlier in the trail): 1/5.
   Exact: closed trails enumerated directly (mode E).  Over-count: forward halves pi1 (from u, avoid c and v) of
   length n1 and backward halves pi2 (into v, avoid c, v only at the end) of length n2, glued at y with the
   junction passage weight; mutual avoidance dropped.
   Usage: halves X N xs xt   -> prints n exact overcount ratio for n <= 2N (exact only for n <= N). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#define G 72
#define OFF 36
#define MN 26
static unsigned char hb[G][G], vb[G][G];
static int nmax, ux, uy, vx, vy, cx = OFF, cy = OFF;
static int px[80], py[80], pd[80];
static const int dx[4] = {1, 0, -1, 0}, dy[4] = {0, 1, 0, -1};
static double xs, xt;
static double A[MN][G][G][4][2], Bw[MN][G][G][4], E[2 * MN + 2];
static int used(int x, int y, int k) { if (k == 0) return hb[x][y]; if (k == 2) return hb[x-1][y]; if (k == 1) return vb[x][y]; return vb[x][y-1]; }
static void setb(int x, int y, int k, int v) { if (k == 0) hb[x][y] = v; else if (k == 2) hb[x-1][y] = v; else if (k == 1) vb[x][y] = v; else vb[x][y-1] = v; }
static int l1(int ax, int ay, int bx, int by) { return abs(ax - bx) + abs(ay - by); }
static int seen_before(int i) { for (int k = 0; k < i; k++) if (px[k] == px[i] && py[k] == py[i]) return 1; return 0; }
/* forward weight of passages 0..n-1 of the path px[0..n] (path starts at u, in-direction West at step 0) */
static double fwd_weight(int n) {
  double w = 1;
  for (int j = 0; j < n; j++) {
    if (seen_before(j)) { w *= 0.2; continue; }
    int ain = (j == 0) ? 2 : pd[j-1];
    w *= (pd[j] == ain) ? xs / 3 : xt / 3;
  }
  return w;
}
static int mode; /* 0: exact closed, 1: forward halves, 2: backward halves */
static void dfs(int x, int y, int n) {
  px[n] = x; py[n] = y;
  if (mode == 0) {
    if (x == vx && y == vy && n > 0) { E[n] += fwd_weight(n); return; }
    if (n == nmax || l1(x, y, vx, vy) > nmax - n) return;
  } else if (mode == 1) {
    if (n > 0) A[n][x][y][pd[n-1]][seen_before(n)] += fwd_weight(n);
    if (n == nmax) return;
  } else {
    if (n > 0) {
      /* forward path z_i = w_{n-i}; passages z_1..z_{n-1}; z_0 = junction (excluded) */
      double w = 1;
      for (int i = 1; i < n; i++) {
        int wi = n - i; /* index in reverse path */
        int rev = 0;
        for (int k = wi + 1; k <= n; k++) if (px[k] == px[wi] && py[k] == py[wi]) rev = 1;
        if (rev) { w *= 0.2; continue; }
        /* forward in-direction: z_{i-1} -> z_i = reverse of step (w_{wi} -> w_{wi+1}) i.e. opposite of pd[wi]
           forward out-direction: z_i -> z_{i+1} = opposite of pd[wi-1] */
        int ain = (pd[wi] + 2) % 4, aout = (pd[wi - 1] + 2) % 4;
        w *= (ain == aout) ? xs / 3 : xt / 3;
      }
      Bw[n][x][y][(pd[n-1] + 2) % 4] += w; /* forward first direction z_0 -> z_1 */
    }
    if (n == nmax) return;
  }
  for (int k = 0; k < 4; k++) {
    int nx = x + dx[k], ny = y + dy[k];
    if (nx == cx && ny == cy) continue;
    if (used(x, y, k)) continue;
    if (mode == 1 && nx == vx && ny == vy) continue;
    if (mode == 2 && nx == vx && ny == vy) continue;
    pd[n] = k; setb(x, y, k, 1); dfs(nx, ny, n + 1); setb(x, y, k, 0);
  }
}
int main(int argc, char **argv) {
  char X = argv[1][0]; int N = atoi(argv[2]); xs = atof(argv[3]); xt = atof(argv[4]);
  ux = OFF - 1; uy = OFF;
  if (X == 'B') { vx = OFF + 1; vy = OFF; } else { vx = OFF; vy = OFF + 1; }
  mode = 0; nmax = N; dfs(ux, uy, 0);
  mode = 1; nmax = N; memset(hb, 0, sizeof hb); memset(vb, 0, sizeof vb); dfs(ux, uy, 0);
  mode = 2; nmax = N; dfs(vx, vy, 0);
  printf("# X=%c N=%d xs=%.6f xt=%.6f ; n exact overcount(n1=ceil(n/2)) ratio\n", X, N, xs, xt);
  for (int n = 2; n <= 2 * N; n += 1) {
    int n1 = (n + 1) / 2, n2 = n - n1; double S = 0;
    if (n2 < 1 || n1 > N || n2 > N) continue;
    for (int x = 0; x < G; x++) for (int y = 0; y < G; y++) for (int d1 = 0; d1 < 4; d1++) for (int f = 0; f < 2; f++) {
      double a = A[n1][x][y][d1][f]; if (a == 0) continue;
      for (int d2 = 0; d2 < 4; d2++) {
        if (d2 == (d1 + 2) % 4) continue;
        double b = Bw[n2][x][y][d2]; if (b == 0) continue;
        double J = f ? 0.2 : ((d1 == d2) ? xs / 3 : xt / 3);
        S += a * J * b;
      }
    }
    if (S > 0) printf("%d %.10e %.10e %.4f\n", n, E[n], S, E[n] > 0 ? S / E[n] : 0);
  }
  return 0;
}
