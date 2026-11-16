/* Weighted trail sums (agent 57).  S_n = sum over trails of length n from the origin of prod_j w_j with
   w = 1/(3 c_start) first step, 1/(3 c_s) straight first-visit step, 1/(3 c_t) turning first-visit step,
   1/5 step out of a site passed once before (rho = 3/5 exactly), 1/4 step out of the start site revisited (rho <= 3/4).
   Usage: trailsum c_start c_s c_t nmax.  Prints S_n and the number of trails t_n. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define NMAX 26
#define W 64
static int dx[4] = {1, 0, -1, 0}, dy[4] = {0, 1, 0, -1};
static unsigned char hb[W][W], vb[W][W];   /* used bonds: horizontal (x,y)-(x+1,y), vertical (x,y)-(x,y+1) */
static unsigned char pass[W][W];
static double S[NMAX + 1]; static long long T[NMAX + 1];
static double ws, wt, wst, wrev = 0.2, wrevx = 0.25; static int nmax;
static int X0 = W / 2, Y0 = W / 2;
static int *bondp(int x, int y, int k) { return 0; }
static unsigned char *bond(int x, int y, int k) {
  switch (k) { case 0: return &hb[x][y]; case 1: return &vb[x][y]; case 2: return &hb[x - 1][y]; default: return &vb[x][y - 1]; }
}
static void dfs(int x, int y, int d, int n, double w) {
  S[n] += w; T[n]++;
  if (n == nmax) return;
  double base;
  int start = (x == X0 && y == Y0);
  /* weight of the step out of (x,y) depends on whether (x,y) was passed before */
  for (int k = 0; k < 4; k++) {
    unsigned char *b = bond(x, y, k);
    if (*b) continue;
    double ww;
    if (n == 0) ww = wst;
    else if (pass[x][y] >= 1) ww = start ? wrevx : wrev;
    else ww = (k == d) ? ws : wt;
    *b = 1; pass[x][y]++;
    dfs(x + dx[k], y + dy[k], k, n + 1, w * ww);
    *b = 0; pass[x][y]--;
  }
}
int main(int argc, char **argv) {
  double cst = atof(argv[1]), cs = atof(argv[2]), ct = atof(argv[3]); nmax = atoi(argv[4]);
  wst = 1.0 / (3 * cst); ws = 1.0 / (3 * cs); wt = 1.0 / (3 * ct);
  memset(hb, 0, sizeof hb); memset(vb, 0, sizeof vb); memset(pass, 0, sizeof pass);
  /* the start site counts as passed once after its first step: handled by pass[] increment at n==0 */
  dfs(X0, Y0, -1, 0, 1.0);
  for (int n = 1; n <= nmax; n++) printf("%d %lld %.10f\n", n, T[n], S[n]);
  return 0;
}
