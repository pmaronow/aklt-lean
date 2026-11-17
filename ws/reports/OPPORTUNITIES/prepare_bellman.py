from pathlib import Path
ROOT=Path(__file__).resolve().parent
src=(ROOT/'experiments/tail.c').read_text()
src=src[:src.index('int main(int argc, char **argv) {')]
start=src.index('static int sidx(')
end=src.index('/* h-weighted response',start)
src=src[:start]+r'''
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
''' +src[end:]
# Prefix weights in doubles for diagnostics. The vector itself is the certificate.
src=src.replace('static float *V[4], *Nv[4]', 'static double *V[4], *Nv[4]')
# Remove unused forward step (float interfaces).
start=src.index('/* ---------------- one DP step')
end=src.index('/* left Perron-type',start)
src=src[:start]+src[end:]
src+=r'''
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
'''
(ROOT/'experiments/bellman.c').write_text(src)
