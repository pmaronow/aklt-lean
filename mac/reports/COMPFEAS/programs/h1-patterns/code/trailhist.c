/* Exact histogram of trails from the origin by step types (agent 57).  For each length n <= nmax and each
   (n_s, n_t, n_r, n_rx) = numbers of straight first-visit / turning first-visit / revisit / start-revisit steps among
   steps 2..n, prints the number of trails (the first step is always the start step).  Usage: trailhist nmax */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define W 64
#define NM 24
static int dx[4] = {1, 0, -1, 0}, dy[4] = {0, 1, 0, -1};
static unsigned char hb[W][W], vb[W][W], pass[W][W];
static long long H[NM + 1][NM][NM][NM][3];   /* [n][ns][nt][nr][nrx], nrx <= 2 */
static int nmax, X0 = W / 2, Y0 = W / 2;
static unsigned char *bond(int x, int y, int k) {
  switch (k) { case 0: return &hb[x][y]; case 1: return &vb[x][y]; case 2: return &hb[x - 1][y]; default: return &vb[x][y - 1]; }
}
static void dfs(int x, int y, int d, int n, int ns, int nt, int nr, int nrx) {
  H[n][ns][nt][nr][nrx]++;
  if (n == nmax) return;
  int start = (x == X0 && y == Y0);
  for (int k = 0; k < 4; k++) {
    unsigned char *b = bond(x, y, k);
    if (*b) continue;
    int a = ns, t = nt, r = nr, rx = nrx;
    if (n > 0) {
      if (pass[x][y] >= 1) { if (start) rx++; else r++; }
      else if (k == d) a++; else t++;
    }
    *b = 1; pass[x][y]++;
    dfs(x + dx[k], y + dy[k], k, n + 1, a, t, r, rx);
    *b = 0; pass[x][y]--;
  }
}
int main(int argc, char **argv) {
  nmax = atoi(argv[1]);
  dfs(X0, Y0, -1, 0, 0, 0, 0, 0);
  for (int n = 1; n <= nmax; n++)
    for (int a = 0; a < NM; a++) for (int t = 0; t < NM; t++) for (int r = 0; r < NM; r++) for (int rx = 0; rx < 3; rx++)
      if (H[n][a][t][r][rx]) printf("%d %d %d %d %d %lld\n", n, a, t, r, rx, H[n][a][t][r][rx]);
  return 0;
}
