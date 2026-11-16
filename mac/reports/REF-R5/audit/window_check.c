#define main manuscript_main
#include "/Users/paronow/aklt-lean/bundle/programs/h3-tail/code/tailmem4.c"
#undef main

int main(void) {
  m = 10;
  build_windows();
  int *indeg = calloc(nw, sizeof(int));
  int zero_in = 0, zero_out = 0, sample = -1;
  for (int w = 0; w < nw; ++w) {
    int out = 0;
    for (int d = 0; d < 4; ++d) if (tgt[w][d] >= 0) {
      ++indeg[tgt[w][d]];
      ++out;
    }
    if (!out) ++zero_out;
  }
  for (int w = 0; w < nw; ++w) if (!indeg[w]) {
    ++zero_in;
    if (sample < 0) sample = w;
  }
  printf("windows=%d zero_indegree=%d zero_outdegree=%d\n", nw, zero_in, zero_out);
  int dirs[64]; decode(wcode[sample], dirs);
  printf("example_zero_indegree=");
  for (int j = 0; j < m; ++j) printf("%c", "ENWS"[dirs[j]]);
  printf("\n");
  fesetround(FE_UPWARD);
  volatile double one = 1, three = 3, five = 5;
  xs = one / nextafter(0.961, 0.0);
  xt = one / nextafter(0.935, 0.0);
  third = one / three; fifth = one / five;
  ca = nextafter(0.18094, INFINITY); cb = nextafter(0.36751, INFINITY);
  hB = 1; hC = 1.23;
  double *z[4];
  for (int p = 0; p < 4; ++p) z[p] = malloc(nw * sizeof(double));
  fesetround(FE_TONEAREST);
  double lamA = perron(z[0], xs * third, xt * third);
  double lamB = perron(z[1], xs * third, third);
  double lt = lamA * (1 + 1e-9);
  postvec(z[2], z[0], 1, xt * third, xs * third, third, lt);
  postvec(z[3], z[1], 0, xs * third, third, third, lt);
  printf("lamA=%.17g lamB=%.17g lcheck=%.17g\n", lamA, lamB, lamA*(1+2e-9));
  for (int p = 0; p < 4; ++p) {
    int zeros = 0, neg = 0, nonfinite = 0; double posmin = INFINITY;
    for (int w = 0; w < nw; ++w) {
      if (!isfinite(z[p][w])) ++nonfinite;
      if (z[p][w] < 0) ++neg;
      if (z[p][w] == 0) ++zeros;
      if (z[p][w] > 0 && z[p][w] < posmin) posmin = z[p][w];
    }
    printf("phase=%c zeros=%d negative=%d nonfinite=%d min_positive=%.17g\n", "ABCD"[p], zeros, neg, nonfinite, posmin);
  }
  for (int w = 0; w < nw; ++w) { z[2][w] *= 1+1e-7; z[3][w] *= 1+1e-7; }
  double lcheck = lamA*(1+2e-9);
  double *left[4];
  for (int p = 0; p < 4; ++p) left[p] = calloc(nw, sizeof(double));
  fesetround(FE_UPWARD);
  for (int w=0; w<nw; ++w) for (int d=0; d<4; ++d) {
    int t=tgt[w][d], k=kind[w][d]; if (t<0) continue;
    if (k==2) { for (int p=0;p<4;++p) left[p][t] += z[p][w]*fifth; continue; }
    double coefficient=kappa(0,0,wcode[w]&3,d,0);
    if (k==0) {
      double ws=xs*third;
      left[0][t] += z[0][w]*ws; left[1][t] += z[1][w]*ws; left[2][t] += z[2][w]*ws;
      left[3][t] += z[3][w]*third+z[1][w]*ws*coefficient;
    } else {
      double wt=xt*third;
      left[0][t] += z[0][w]*wt; left[1][t] += z[1][w]*third;
      left[2][t] += z[2][w]*third+z[0][w]*wt*coefficient; left[3][t] += z[3][w]*third;
    }
  }
  fesetround(FE_DOWNWARD);
  int failed=0, zeros_with_incoming=0;
  for(int p=0;p<4;++p)for(int w=0;w<nw;++w) {
    if(left[p][w] > lcheck*z[p][w]) ++failed;
    if(z[p][w]==0 && indeg[w]) ++zeros_with_incoming;
  }
  fesetround(FE_TONEAREST);
  printf("directed_subinvariance_failures=%d zeros_with_incoming=%d\n", failed, zeros_with_incoming);
  return 0;
}
