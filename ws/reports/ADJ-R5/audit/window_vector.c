/* Reuse only the small window/vector routines; never allocate production site arrays. */
#define main unused_production_main
#include "/home/ubuntu/aklt/manuscript/bundle/programs/h3-tail/code/tailmem4.c"
#undef main
int main(void) {
  m=10; build_windows();
  int *indeg=calloc(nw,sizeof(int));
  int zero_in=0,zero_out=0;
  for(int w=0;w<nw;w++) {
    int out=0;
    for(int d=0;d<4;d++) if(tgt[w][d]>=0) { indeg[tgt[w][d]]++; out++; }
    if(!out) zero_out++;
  }
  for(int w=0;w<nw;w++) if(!indeg[w]) zero_in++;
  printf("windows=%d zero_indegree=%d zero_outdegree=%d\n",nw,zero_in,zero_out);
  fesetround(FE_UPWARD);
  volatile double one=1,three=3,five=5;
  xs=one/nextafter(.961,0); xt=one/nextafter(.935,0);
  third=one/three; fifth=one/five;
  ca=nextafter(.18094,INFINITY); cb=nextafter(.36751,INFINITY); hB=1;hC=1.23;
  fesetround(FE_TONEAREST);
  double *z[4];for(int p=0;p<4;p++) z[p]=malloc(nw*sizeof(double));
  double lamA=perron(z[0],xs*third,xt*third),lamB=perron(z[1],xs*third,third);
  double lt=lamA*(1+1e-9);
  postvec(z[2],z[0],1,xt*third,xs*third,third,lt);
  postvec(z[3],z[1],0,xs*third,third,third,lt);
  for(int w=0;w<nw;w++){ z[2][w]*=1+1e-7;z[3][w]*=1+1e-7; }
  double lcheck=lamA*(1+2e-9);
  printf("lamA=%.17g lamB=%.17g lcheck=%.17g lcheck_hex=%a\n",lamA,lamB,lcheck,lcheck);
  FILE *out=fopen("audit/window_vector.tsv","w");
  fprintf(out,"lambda %a\n",lcheck);
  for(int w=0;w<nw;w++) fprintf(out,"%d %a %a %a %a\n",wcode[w],z[0][w],z[1][w],z[2][w],z[3][w]);
  fclose(out);
  for(int p=0;p<4;p++) {
    int zeros=0,bad=0,extra=0;
    for(int w=0;w<nw;w++){if(!isfinite(z[p][w])||z[p][w]<0)bad++; if(z[p][w]==0){zeros++;if(indeg[w])extra++;}}
    printf("phase=%c zero=%d nonfinite_or_negative=%d zero_with_incoming=%d\n","ABCD"[p],zeros,bad,extra);
  }
  return 0;
}
