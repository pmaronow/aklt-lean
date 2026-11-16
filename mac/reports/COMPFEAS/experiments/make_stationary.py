from pathlib import Path
root=Path(__file__).resolve().parents[1]
s=(root/'experiments/tailmem6_min.c').read_text()
a=s.index('static void dfs(');b=s.index('/* ---------------- one DP step',a)
dfs=s[a:b].replace('static void dfs(','static void prefixdfs(').replace(' dfs(nx, ny,',' prefixdfs(nx, ny,')
a2=dfs.index('  if (n == L) {');b2=dfs.index('  int *slot',a2)
dfs=dfs[:a2]+'''  if (n == L) {
    int w=lut[code & ((1 << (2*m))-1)];int si=(x-OFF+RR)*SIDE+(y-OFF+RR);
    if(w<0 || si<0 || si>=SS){fprintf(stderr,"prefix out of grid\\n");exit(1);}
    prefix_total+=PA*Gv[0][(long)w*SS+si]+PB*Gv[1][(long)w*SS+si]+QC*Gv[2][(long)w*SS+si]+QD*Gv[3][(long)w*SS+si]; return;
  }
'''+dfs[b2:]
pre='''#define main original_main
#include "tailmem6_min.c"
#undef main
static int RR,SIDE,SS,*nbg[4],iternow;
static double *Gv[4],*gz[4],*buf[4],prefix_total;
static uint64_t opedges;
'''
helper=r'''
static double livekap(int x,int y,int ain,int d) {
 int back=(ain+2)%4,f[2],nf=0;
 for(int j=0;j<4;j++)if(j!=back&&j!=d)f[nf++]=j;
 int isB[3]={(dx[f[0]]==dx[f[1]]||dy[f[0]]==dy[f[1]]),(dx[f[0]]==dx[d]||dy[f[0]]==dy[d]),(dx[f[1]]==dx[d]||dy[f[1]]==dy[d])};
 return kapcomb(d==ain,x+dx[f[0]]==0&&y+dy[f[0]]==0,x+dx[f[1]]==0&&y+dy[f[1]]==0,isB);
}
static double freekap(int ain,int d){return kappa(1000,1000,ain,d,0);}
static void right_vector(void) {
 for(int p=0;p<4;p++){gz[p]=malloc(nw*sizeof(double));buf[p]=malloc(nw*sizeof(double));for(int w=0;w<nw;w++)gz[p][w]=1;}
 fesetround(FE_TONEAREST);
 for(int it=0;it<20000;it++){
  double err=0;
  for(int w=0;w<nw;w++){
   double v[4]={1,1,1,1};int ain=wcode[w]&3;
   for(int d=0;d<4;d++){int t=tgt[w][d];if(t<0)continue;int k=kind[w][d];
    if(k==2){for(int p=0;p<4;p++)v[p]+=gz[p][t]*fifth;}
    else if(k==0){double ws=xs*third;double kap=freekap(ain,d);v[0]+=ws*gz[0][t];v[1]+=ws*(gz[1][t]+kap*gz[3][t]);v[2]+=ws*gz[2][t];v[3]+=third*gz[3][t];}
    else{double wt=xt*third;double kap=freekap(ain,d);v[0]+=wt*(gz[0][t]+kap*gz[2][t]);v[1]+=third*gz[1][t];v[2]+=third*gz[2][t];v[3]+=third*gz[3][t];}
   }
   for(int p=0;p<4;p++){buf[p][w]=v[p];double e=fabs(v[p]-gz[p][w])/(1+v[p]);if(e>err)err=e;}
  }
  for(int p=0;p<4;p++){double*t=gz[p];gz[p]=buf[p];buf[p]=t;}
  if(err<1e-14&&it>200){fprintf(stderr,"right vector iterations=%d error=%.3e\n",it+1,err);break;}
 }
 // Normalize the constant supersolution to dominate terminal rewards 1.
 double mn=1e300;
 for(int w=0;w<nw;w++)for(int p=2;p<4;p++)if(gz[p][w]<mn)mn=gz[p][w];
 fesetround(FE_UPWARD);double fac=(1+1e-8)/mn;
 for(int p=0;p<4;p++)for(int w=0;w<nw;w++)gz[p][w]*=fac;
 // Check W z <= z; the strict residual is recorded, not needed for generation.
 double resid=1e300;
 for(int w=0;w<nw;w++){
  double v[4]={0};int ain=wcode[w]&3;
  for(int d=0;d<4;d++){int t=tgt[w][d];if(t<0)continue;int k=kind[w][d];
   if(k==2){for(int p=0;p<4;p++)v[p]+=gz[p][t]*fifth;}
   else if(k==0){double ws=xs*third,kap=freekap(ain,d);v[0]+=ws*gz[0][t];v[1]+=ws*(gz[1][t]+kap*gz[3][t]);v[2]+=ws*gz[2][t];v[3]+=third*gz[3][t];}
   else{double wt=xt*third,kap=freekap(ain,d);v[0]+=wt*(gz[0][t]+kap*gz[2][t]);v[1]+=third*gz[1][t];v[2]+=third*gz[2][t];v[3]+=third*gz[3][t];}
  }
  for(int p=0;p<4;p++){if(v[p]>gz[p][w]){fprintf(stderr,"right vector check failed\n");exit(1);}fesetround(FE_DOWNWARD);double e=gz[p][w]-v[p];fesetround(FE_UPWARD);if(e<resid)resid=e;}
 }
 fprintf(stderr,"right vector checked min_slack=%.12g\n",resid);
}
static double prefval(char X){
 memset(closedK,0,sizeof closedK);prefix_total=0;
 for(int i=0;i<GG;i++)for(int j=0;j<GG;j++)V1[i][j]=V2[i][j]=100000;
 prefixdfs(OFF-1,OFF,0,1,1,0,0,0);
 for(int n=1;n<=L;n++)prefix_total+=closedK[n];
 return prefix_total;
}
static void bellman_row(int w,int write,double *upmax) {
 int ain=wcode[w]&3;
 for(int p=0;p<4;p++)memset(buf[p],0,SS*sizeof(double));
 for(int d=0;d<4;d++){
  int t=tgt[w][d];if(t<0)continue;int k=kind[w][d];
  double kap= k==2 ? 0 : freekap(ain,d), ws=xs*third,wt=xt*third;
  for(int s=0;s<SS;s++){
   int x=s/SIDE-RR,y=s%SIDE-RR;
   int cpos=(x==0&&y==0),vpos=(x==zvx-OFF&&y==zvy-OFF);
   if(cpos||vpos)continue;
   int known=(x==-1&&y==0)||(D0>=0&&x==-1+dx[D0]&&y==dy[D0]);
   if(known){if(k==2)continue;if(D0>=0&&((x==-1&&y==0&&d==D0)||(x==-1+dx[D0]&&y==dy[D0]&&d==(D0+2)%4)))continue;}
   int sn=nbg[d][s];long a=(long)t*SS+(sn<0?0:sn);double vv[4];
   for(int p=0;p<4;p++)vv[p]=sn<0?gz[p][t]:Gv[p][a];
   if(k==2||known){for(int p=0;p<4;p++)buf[p][s]+=fifth*vv[p];}
   else{
    double kk=abs(x)+abs(y)==1?livekap(x,y,ain,d):kap;
    if(k==0){buf[0][s]+=ws*vv[0];buf[1][s]+=ws*vv[1]+(ws*kk)*vv[3];buf[2][s]+=ws*vv[2];buf[3][s]+=third*vv[3];}
    else{buf[0][s]+=wt*vv[0]+(wt*kk)*vv[2];buf[1][s]+=third*vv[1];buf[2][s]+=third*vv[2];buf[3][s]+=third*vv[3];}
   }
  }
 }
 int sv=(zvx-OFF+RR)*SIDE+(zvy-OFF+RR),sc=RR*SIDE+RR;
 for(int p=0;p<4;p++){buf[p][sc]=0;buf[p][sv]=p>=2?1:0;}
 for(int p=0;p<4;p++)for(int s=0;s<SS;s++){
  double old=Gv[p][(long)w*SS+s],v=buf[p][s];
  if(v>old){double up=(v-old)/(1+old);if(up>*upmax)*upmax=up;}
  if(write)Gv[p][(long)w*SS+s]=v;
 }
}
int main(int argc,char**argv){
 if(argc<6)return 1;char X=argv[1][0];m=atoi(argv[2]);L=atoi(argv[3]);RR=atoi(argv[4]);int maxit=atoi(argv[5]);D0=argc>6?atoi(argv[6]):-1;
 if(L<m+2||RR<L+2||RR>=OFF-2){fprintf(stderr,"need m+2<=L<R and R<54 (prefix grid limit)\n");return 1;}
 // The prefix uses the original fixed-size grid; only L must fit. R itself may be larger.
 xs=1/nextafter(.961,0);xt=1/nextafter(.935,0);third=1.0/3.0;fifth=1.0/5.0;
 CA[0]=nextafter(.145217,INFINITY);CB[0]=nextafter(.352782,INFINITY);CBP[0]=nextafter(.340008,INFINITY);
 CA[1]=nextafter(.150000,INFINITY);CB[1]=nextafter(.357549,INFINITY);CBP[1]=nextafter(.344661,INFINITY);hB=1;hC=1.20;ca=CA[0];cb=CB[0];
 fesetround(FE_UPWARD);volatile double one=1,three=3,five=5;xs=one/nextafter(.961,0);xt=one/nextafter(.935,0);third=one/three;fifth=one/five;
 build_windows();compress_windows();K=m+3;build_sites();
 SIDE=2*RR+1;SS=SIDE*SIDE;
 right_vector();for(int p=0;p<4;p++){free(buf[p]);buf[p]=malloc(SS*sizeof(double));Gv[p]=malloc((long)nw*SS*sizeof(double));if(!Gv[p])return 1;for(int w=0;w<nw;w++)for(int s=0;s<SS;s++)Gv[p][(long)w*SS+s]=gz[p][w];}
 for(int d=0;d<4;d++){nbg[d]=malloc(SS*sizeof(int));for(int s=0;s<SS;s++){int x=s/SIDE+dx[d],y=s%SIDE+dy[d];nbg[d][s]=(x<0||y<0||x>=SIDE||y>=SIDE)?-1:x*SIDE+y;}}
 zvx=X=='B'?OFF+1:OFF;zvy=X=='B'?OFF:OFF+1;
 int sv=(zvx-OFF+RR)*SIDE+(zvy-OFF+RR),sc=RR*SIDE+RR;
 for(int p=0;p<4;p++)for(int w=0;w<nw;w++){Gv[p][(long)w*SS+sc]=0;Gv[p][(long)w*SS+sv]=p>=2?1:0;}
 double cpu0=(double)clock()/CLOCKS_PER_SEC;
 for(int it=0;it<maxit;it++){
  double up=0;for(int w=0;w<nw;w++)bellman_row(w,1,&up);
  if(up>1e-12){fprintf(stderr,"monotonicity failed %.12g\n",up);return 1;}
  if((it+1)%50==0||it==maxit-1){double val=prefval(X);printf("ITER %d bound %.12g ratio %.12g max_increase %.3g cpu %.3f\n",it+1,val,val/(X=='B'?hB:hC),up,(double)clock()/CLOCKS_PER_SEC-cpu0);fflush(stdout);if(it>=100&&val/(X=='B'?hB:hC)<.98)break;}
 }
 double up=0;for(int w=0;w<nw;w++)bellman_row(w,0,&up);
 printf("FINAL_CHECK max_relative_increase %.12g bound %.12g\n",up,prefval(X));
 const char*fn=getenv("CERT_OUTPUT");if(fn){FILE*f=fopen(fn,"wb");long hdr[7]={m,L,RR,nw,SS,X,D0};fwrite(hdr,sizeof(long),7,f);for(int p=0;p<4;p++)fwrite(gz[p],sizeof(double),nw,f);for(int p=0;p<4;p++)fwrite(Gv[p],sizeof(double),(long)nw*SS,f);fclose(f);}
 struct rusage ru;getrusage(RUSAGE_SELF,&ru);printf("PROFILE nw=%d sites=%d edges=%ld state_values=%ld bytes=%ld maxrss_bytes=%ld cpu=%.6f\n",nw,SS,(long)0,(long)nw*SS*4,(long)nw*SS*4*8,ru.ru_maxrss,(double)clock()/CLOCKS_PER_SEC-cpu0);
 return 0;
}
'''
# Radius does not constrain the prefix's fixed board: only L does.
helper=helper.replace('||RR>=OFF-2','||L>=OFF-2').replace('R<54 (prefix grid limit)','L<54 (prefix grid limit)')
(root/'experiments/stationary.c').write_text(pre+dfs+helper)
