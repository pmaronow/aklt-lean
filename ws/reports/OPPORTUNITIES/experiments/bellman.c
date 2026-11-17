/* tailmem6 = tailmem5 with TYPE-DEPENDENT coefficients of Lemma 3.3' (agent 62 NOTES Entry 19): a passage of type
   straight uses (a_s, b_s), a turn (a_t, b_t); if exactly one of f, g is removed (c, or passed twice) the surviving
   pair (other, o) carries b'_type (two-neighbour passage).  Usage:
   tailmem6 X m L K T AT NEX cs ct a_s b_s b'_s a_t b_t b'_t hB hC [D0]
   tailmem5 = tailmem4 + split by the first direction D0 of the trail (argument 14; -1 = all): the DFS keeps only
   trails with first step D0, and in the DP (while t <= AT) the sites u and u+D0 are known to be visited (a passage
   there is a revisit; a window-detected earlier visit there would be a third visit: killed) and the bond (u, u+D0)
   is known to be used (forbidden).  Results of the classes D0 = 0..3 add up (the classes partition the trails).
   tailmem4 = tailmem3 + (i) the start site u is known to be visited at time 0, so every DP passage at the site u
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
static double CA[2], CB[2], CBP[2]; /* [0] straight, [1] turn */
/* h-weighted response of a first-visit passage: straight = 1 if out == in; deadf/deadg: f resp. g removed;
   isB_q: pair q (0 = fg, 1 = fo, 2 = go) collinear */
static double kapcomb(int straight, int deadf, int deadg, const int *isB) {
  int ty = straight ? 0 : 1;
  double h0 = isB[0] ? hB : hC, h1 = isB[1] ? hB : hC, h2 = isB[2] ? hB : hC;
  if (!deadf && !deadg) return CA[ty] * h0 + CB[ty] * h1 + CB[ty] * h2;
  if (deadf && !deadg) return CBP[ty] * h2;
  if (!deadf && deadg) return CBP[ty] * h1;
  return 0;
}
static const int dx[4] = {1, 0, -1, 0}, dy[4] = {0, 1, 0, -1};
static int nw = 0, *wcode, *lut;
static int (*tgt)[4]; static unsigned char (*kind)[4];
static double *V[4], *Nv[4]; /* phases A, B, C, D */
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
static int NSITE, *nbr[4], *repx, *repy, ic, iu, id0 = -1, D0 = -1; static unsigned char *nearc;

static int side;
static int sidx(int x,int y) {
  if(abs(x)>K || abs(y)>K) return -1;
  return (x+K)*side+y+K;
}
static void build_sites(void) {
  side=2*K+1; NSITE=side*side;
  repx=malloc(NSITE*sizeof(int)); repy=malloc(NSITE*sizeof(int));
  for(int d=0;d<4;d++) nbr[d]=malloc(NSITE*sizeof(int));
  for(int x=-K;x<=K;x++) for(int y=-K;y<=K;y++) {
    int s=sidx(x,y); repx[s]=x; repy[s]=y;
    for(int d=0;d<4;d++) nbr[d][s]=sidx(x+dx[d],y+dy[d]);
  }
  ic=sidx(0,0);
}
/* h-weighted response of a first-visit passage at (x,y) with in-direction ain and out-direction out; with killc,
   pairs containing the torus site of c are dead */
static double kappa(int x, int y, int ain, int out, int killc) {
  int back = (ain + 2) % 4, fx[2], fy[2], nf = 0;
  for (int k = 0; k < 4; k++) if (k != back && k != out) { fx[nf] = x + dx[k]; fy[nf] = y + dy[k]; nf++; }
  int ox = x + dx[out], oy = y + dy[out];
  int Ax[3] = {fx[0], fx[0], fx[1]}, Ay[3] = {fy[0], fy[0], fy[1]}, Bx[3] = {fx[1], ox, ox}, By[3] = {fy[1], oy, oy};
  int isB[3]; for (int q = 0; q < 3; q++) isB[q] = (Ax[q] == Bx[q] || Ay[q] == By[q]);
  int deadf = killc && sidx(fx[0], fy[0]) == ic, deadg = killc && sidx(fx[1], fy[1]) == ic;
  return kapcomb(out == ain, deadf, deadg, isB);
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
    int isB[3]; for (int q = 0; q < 3; q++) isB[q] = (Ax[q] == Bx[q] || Ay[q] == By[q]);
    int dfg[2];
    for (int e = 0; e < 2; e++) {
      int cnt = 0; for (int i = 0; i < j; i++) if (qx[i] == fx[e] && qy[i] == fy[e]) cnt++;
      dfg[e] = (fx[e] == zcx && fy[e] == zcy) || cnt >= 2;
    }
    double kap = kapcomb(out == ain, dfg[0], dfg[1], isB);
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
    if (n == 0 && D0 >= 0 && k != D0) continue;
    if (nx == zcx && ny == zcy) continue;
    if (usedb(x, y, k)) continue;
    double A2, B2, C2, D2;
    if (prior > 0) { A2 = PA * fifth; B2 = PB * fifth; C2 = QC * fifth; D2 = QD * fifth; }
    else {
      int ain = (n == 0) ? 2 : pd_[n-1];
      int back = (ain + 2) % 4, fx[2], fy[2], nf = 0;
      for (int kk = 0; kk < 4; kk++) if (kk != back && kk != k) { fx[nf] = x + dx[kk]; fy[nf] = y + dy[kk]; nf++; }
      int Ax[3] = {fx[0], fx[0], fx[1]}, Ay[3] = {fy[0], fy[0], fy[1]}, Bx[3] = {fx[1], nx, nx}, By[3] = {fy[1], ny, ny};
      int isB[3]; for (int q = 0; q < 3; q++) isB[q] = (Ax[q] == Bx[q] || Ay[q] == By[q]);
      int deadf = (fx[0] == zcx && fy[0] == zcy) || pb(fx[0], fy[0], n) >= 2;
      int deadg = (fx[1] == zcx && fy[1] == zcy) || pb(fx[1], fy[1], n) >= 2;
      double kap = kapcomb(k == ain, deadf, deadg, isB);
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

static double *U[4], *Bnd[4], *ktab;
static long nedge=0;
static double kap_at(int w,int d,int s) {
  return ktab[((wcode[w]&3)*4+d)*NSITE+s];
}
static double continuation(int p,int w,int s,int terminal) {
  if(s==terminal) return p>=2 ? 1 : 0;
  if(s==ic) return 0;
  if(s<0) return 0;
  return U[p][(long)w*NSITE+s];
}
static void solve(int p,int terminal) {
  double maxdiff=1e300;
  int it;
  for(it=0;it<20000;it++) {
    maxdiff=0;
    for(int w=0;w<nw;w++)for(int s=0;s<NSITE;s++) {
      if(s==terminal || s==ic) continue;
      double v=0;
      for(int d=0;d<4;d++) {
        int w2=tgt[w][d],s2=nbr[d][s];
        if(w2<0 || s2==ic) continue;
        int k=kind[w][d]; if(s==iu) k=2;
        double ww=k==2?fifth:third;
        if(k==0 && p!=3) ww*=xs;
        if(k==1 && p==0) ww*=xt;
        v+=ww*continuation(p,w2,s2,terminal);
        if((p==0 && k==1)||(p==1 && k==0))
          v+=ww*kap_at(w,d,s)*continuation(p+2,w2,s2,terminal);
      }
      long a=(long)w*NSITE+s;
      double old=U[p][a]; U[p][a]=v;
      if(fabs(v-old)>maxdiff)maxdiff=fabs(v-old);
    }
    if(maxdiff<1e-11) break;
  }
  fprintf(stderr,"phase %d iterations=%d maxdiff=%.4g\n",p,it,maxdiff);
}
int main(int argc,char **argv) {
  if(argc!=5) return 2;
  char X=argv[1][0]; m=atoi(argv[2]); L=atoi(argv[3]); K=atoi(argv[4]);
  if(m<1||m>8||L<m||L>20||K<L+1) return 2;
  xs=1000./961;xt=200./187;third=1./3;fifth=1./5;
  CA[0]=.145217;CB[0]=.352782;CBP[0]=.340008;
  CA[1]=.149953;CB[1]=.357549;CBP[1]=.344661;
  hB=1;hC=1.2;D0=-1;
  build_windows();build_sites();
  long nn=(long)nw*NSITE;
  ktab=calloc(16*NSITE,sizeof(double));
  for(int ain=0;ain<4;ain++)for(int d=0;d<4;d++)if(d!=(ain+2)%4)
    for(int s=0;s<NSITE;s++) ktab[(ain*4+d)*NSITE+s]=kappa(repx[s],repy[s],ain,d,1);
  for(int p=0;p<4;p++) {V[p]=calloc(nn,sizeof(double));U[p]=calloc(nn,sizeof(double));}
  iu=sidx(-1,0);
  int terminal=sidx(X=='B'?1:0,X=='B'?0:1);
  for(int i=0;i<GG;i++)for(int j=0;j<GG;j++) V1[i][j]=V2[i][j]=100000;
  zvx=OFF+(X=='B'?1:0);zvy=OFF+(X=='B'?0:1);
  dfs(OFF-1,OFF,0,1,1,0,0,0);
  solve(3,terminal);solve(2,terminal);solve(1,terminal);solve(0,terminal);
  double val=0,shortval=0;
  for(int p=0;p<4;p++)for(long a=0;a<nn;a++)val+=V[p][a]*U[p][a];
  for(int n=1;n<=L;n++)shortval+=closedK[n];
  printf("HEURISTIC LOWER bound of relaxed infinite-memory-walk bound: X=%c m=%d L=%d R=%d windows=%d sites=%d states=%ld short=%.12g tail=%.12g total=%.12g ratio=%.12g\n",
    X,m,L,K,nw,NSITE,4*nn,shortval,val,shortval+val,(shortval+val)/(X=='B'?1:hC));
}
