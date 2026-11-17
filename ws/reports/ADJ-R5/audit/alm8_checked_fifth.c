/* Rigorous Alm-type growth bound for the weighted trail sums (agent 57, NOTES Entries 5 and 15).
   States: windows = trails of length m (direction strings, all 4 initial directions).  M(s,s') = sum over k-step
   continuations of s (bond-avoiding together with s) ending in window s' of prod of step weights, each step weighted
   with the window as the ONLY history: first visit -> ws (straight) / wt (turn), revisit -> wr = 1/4.
   Rigour: all entries are sums of products of positive numbers, computed with FE_UPWARD (>= exact); the weights are
   ws = 10000/(3 cs4) rounded up for c_s = cs4/10000; the Collatz-Wielandt bound max_i (Mx)_i/x_i is evaluated with
   FE_UPWARD for the positive vector x obtained by power iteration (any positive x is valid).
   Usage: alm8 m k cs4 ct4 [cs4 ct4 ...]   e.g.  alm8 8 8 9700 9350 9600 9250
   Compile: gcc -O2 -frounding-math -o alm8 alm8.c -lm */
#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <fenv.h>
#pragma STDC FENV_ACCESS ON
#define G 64
static int m, k, nst;
static int *code2idx;           /* window code (base 4) -> state index or -1 */
static int *states;             /* state codes */
static int dx[4] = {1, 0, -1, 0}, dy[4] = {0, 1, 0, -1};
static unsigned char hb[G][G], vb[G][G], dep[G][G];
static double ws, wt, wr = 0.2;
static double *acc; static int *touched, ntouched;
static unsigned char *bondp(int x, int y, int d) {
  switch (d) { case 0: return &hb[x][y]; case 1: return &vb[x][y]; case 2: return &hb[x - 1][y]; default: return &vb[x][y - 1]; }
}
static int pw4[24];
static void gen(int len, int code, int x, int y, int last) {
  if (len == m) { code2idx[code] = nst; states[nst++] = code; return; }
  for (int d = 0; d < 4; d++) {
    if (len > 0 && d == (last + 2) % 4) continue;
    unsigned char *b = bondp(x, y, d);
    if (*b) continue;
    *b = 1; gen(len + 1, code + d * pw4[len], x + dx[d], y + dy[d], d); *b = 0;
  }
}
/* extension DFS: seq holds the last m directions as a sliding code */
static int dirs[64];
static void ext(int step, int x, int y, int last, double w) {
  if (step == k) {
    int code = 0;
    for (int i = 0; i < m; i++) code += dirs[k + i] * pw4[i];   /* last m directions: positions k..k+m-1 of dirs */
    int j = code2idx[code];
    if (acc[j] == 0.0) touched[ntouched++] = j;
    acc[j] += w;
    return;
  }
  for (int d = 0; d < 4; d++) {
    unsigned char *b = bondp(x, y, d);
    if (*b) continue;
    double ww = dep[x][y] >= 1 ? wr : (d == last ? ws : wt);
    *b = 1; dep[x][y]++; dirs[m + step] = d;
    ext(step + 1, x + dx[d], y + dy[d], d, w * ww);
    *b = 0; dep[x][y]--;
  }
}

static uint64_t *hnum, sums[9][9];
static int canonical(int code) {
  int best=code;
  for(int sign=-1;sign<=1;sign+=2)for(int r=0;r<4;r++) {
    int c=0;
    for(int i=0;i<m;i++) {
      int d=(code/pw4[i])%4;
      c+=((sign*d+r+4)%4)*pw4[i];
    }
    if(c<best)best=c;
  }
  return best;
}
/* Re-enumerate block continuations with integers, independently of CSR values. */
static void ext_integer(int step,int x,int y,int last,int a,int t) {
  if(step==k) {
    int c=0;
    for(int i=0;i<m;i++)c+=dirs[k+i]*pw4[i];
    int j=code2idx[c];if(j<0)abort();
    sums[a][t]+=hnum[j];return;
  }
  for(int d=0;d<4;d++) {
    unsigned char *b=bondp(x,y,d);if(*b)continue;
    int revisit=dep[x][y]>0;
    *b=1;dep[x][y]++;dirs[m+step]=d;
    ext_integer(step+1,x+dx[d],y+dy[d],d,a+(!revisit&&d==last),t+(!revisit&&d!=last));
    *b=0;dep[x][y]--;
  }
}

int main(int argc, char **argv) {
  if(argc != 5) return 2;
  m = atoi(argv[1]); k = atoi(argv[2]);
  /* This audit copy certifies only the instance under discussion. */
  if(m!=8 || k!=8 || atoi(argv[3])!=9610 || atoi(argv[4])!=9350) return 2;
  pw4[0] = 1; for (int i = 1; i <= m; i++) pw4[i] = pw4[i - 1] * 4;
  code2idx = malloc(sizeof(int) * pw4[m]); for (int i = 0; i < pw4[m]; i++) code2idx[i] = -1;
  states = malloc(sizeof(int) * pw4[m]);
  memset(hb, 0, sizeof hb); memset(vb, 0, sizeof vb); memset(dep, 0, sizeof dep);
  nst = 0; gen(0, 0, G / 2, G / 2, -1);
  fprintf(stderr, "m=%d k=%d windows=%d\n", m, k, nst);
  acc = calloc(nst, sizeof(double)); touched = malloc(sizeof(int) * nst);
  for (int a = 3; a + 1 < argc; a += 2) {
    double cs4 = atof(argv[a]), ct4 = atof(argv[a + 1]);
    fesetround(FE_UPWARD);
    ws = 10000.0 / (3.0 * cs4) ; wt = 10000.0 / (3.0 * ct4);   /* operands exact (integers), quotient rounded up */
    /* build CSR with upward rounding */
    long cap = 1 << 20, nnz = 0;
    int *rowp = malloc(sizeof(int) * (nst + 1)); int *col = malloc(sizeof(int) * cap); double *val = malloc(sizeof(double) * cap);
    for (int i = 0; i < nst; i++) {
      rowp[i] = nnz;
      int c = states[i], x = G / 2, y = G / 2;
      memset(hb, 0, sizeof hb); memset(vb, 0, sizeof vb); memset(dep, 0, sizeof dep);
      int last = -1;
      for (int t = 0; t < m; t++) {
        int d = (c / pw4[t]) % 4; dirs[t] = d;
        *bondp(x, y, d) = 1; dep[x][y]++; x += dx[d]; y += dy[d]; last = d;
      }
      /* shift: dirs[0..m-1] window, extension written at dirs[m..m+k-1]; final window = dirs[k..k+m-1] */
      ntouched = 0;
      ext(0, x, y, last, 1.0);
      for (int t = 0; t < ntouched; t++) {
        int j = touched[t];
        if (nnz >= cap) { cap *= 2; col = realloc(col, sizeof(int) * cap); val = realloc(val, sizeof(double) * cap); }
        col[nnz] = j; val[nnz] = acc[j]; nnz++; acc[j] = 0.0;
      }
    }
    rowp[nst] = nnz;
    /* power iteration (nearest rounding) for a positive vector */
    fesetround(FE_TONEAREST);
    double *xv = malloc(sizeof(double) * nst), *yv = malloc(sizeof(double) * nst);
    for (int i = 0; i < nst; i++) xv[i] = 1.0;
    int nit = m >= 8 ? 200 : 4000; for (int it = 0; it < nit; it++) {
      double mx = 0;
      for (int i = 0; i < nst; i++) { double s = 0; for (long p = rowp[i]; p < rowp[i + 1]; p++) s += val[p] * xv[col[p]]; yv[i] = s; if (s > mx) mx = s; }
      for (int i = 0; i < nst; i++) xv[i] = yv[i] / mx + 1e-300;
    }
    hnum=malloc(nst*sizeof(uint64_t));
    for(int i=0;i<nst;i++)hnum[i]=(uint64_t)ceil(fmax(xv[i],0.01)*1e12);
    for(int i=0;i<nst;i++)hnum[i]=hnum[code2idx[canonical(states[i])]];
    for(int i=0;i<nst;i++)xv[i]=(double)hnum[i]/1e12;
    /* rigorous Collatz-Wielandt bound with upward rounding */
    fesetround(FE_UPWARD);
    double best = 0;
    for (int i = 0; i < nst; i++) {
      double s = 0; for (long p = rowp[i]; p < rowp[i + 1]; p++) s += val[p] * xv[col[p]];
      double r = s / xv[i]; if (r > best) best = r;
    }
    printf("directed quotient_up=%.17g hex=%a\n",best,best);
    uint64_t mn=hnum[0],mx=hnum[0];int orbits=0;
    FILE *out=fopen("audit/h2_integer_certificate_fifth.tsv","w");
    fprintf(out,"H 8 8 7500\n");
    for(int i=0;i<nst;i++) {
      if(hnum[i]<mn)mn=hnum[i];if(hnum[i]>mx)mx=hnum[i];
      if(states[i]!=canonical(states[i]))continue;
      orbits++;
      fprintf(out,"h %d %" PRIu64 "\n",states[i],hnum[i]);
      memset(hb,0,sizeof hb);memset(vb,0,sizeof vb);memset(dep,0,sizeof dep);memset(sums,0,sizeof sums);
      int x=G/2,y=G/2,last=-1;
      for(int l=0;l<m;l++) {
        int d=states[i]/pw4[l]%4;dirs[l]=d;
        *bondp(x,y,d)=1;dep[x][y]++;x+=dx[d];y+=dy[d];last=d;
      }
      ext_integer(0,x,y,last,0,0);
      for(int a=0;a<=k;a++)for(int t=0;t<=k-a;t++)if(sums[a][t])
        fprintf(out,"S %d %d %d %d %" PRIu64 "\n",states[i],a,t,k-a-t,sums[a][t]);
    }
    fclose(out);
    printf("integer vector min=%" PRIu64 " max=%" PRIu64 " orbits=%d\n",mn,mx,orbits);
    fflush(stdout);
    free(rowp); free(col); free(val); free(xv); free(yv);
  }
  return 0;
}
