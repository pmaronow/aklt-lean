#define main original_main
#include "tailmem6_min.c"
#undef main
static int RR,SIDE,SS,*nbg[4],iternow;
static double *Gv[4],*gz[4],*buf[4],prefix_total;
static uint64_t opedges;
static void prefixdfs(int x, int y, int n, double PA, double PB, double QC, double QD, int code) {
  dfsnodes++; levels[n]++;
  if (x == zvx && y == zvy && n > 0) { closedK[n] += sorted_value(n); return; }
  if (n == L) {
    int w=lut[code & ((1 << (2*m))-1)];int si=(x-OFF+RR)*SIDE+(y-OFF+RR);
    if(w<0 || si<0 || si>=SS){fprintf(stderr,"prefix out of grid\n");exit(1);}
    prefix_total+=PA*Gv[0][(long)w*SS+si]+PB*Gv[1][(long)w*SS+si]+QC*Gv[2][(long)w*SS+si]+QD*Gv[3][(long)w*SS+si]; return;
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
    pd_[n] = k; setb(x, y, k, 1); prefixdfs(nx, ny, n + 1, A2, B2, C2, D2, (int)((((unsigned)code << 2) | (unsigned)k) & ((1u << (2 * m)) - 1))); setb(x, y, k, 0);
  }
  *slot = 100000;
}

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

#include "stationary_weights.h"
typedef unsigned __int128 U128;
static uint64_t quant(double v,double z){double a=ceil(ldexp(v+ldexp(z,-14),16));if(!isfinite(a)||a<0||a>=4294967296.0){fprintf(stderr,"coarse quant overflow %.17g\n",a);exit(1);}return (uint64_t)a;}
static uint64_t qu(int p,int w,int s){
 int x=s/SIDE-RR,y=s%SIDE-RR;
 if(x==0&&y==0)return 0;
 if(x==zvx-OFF&&y==zvy-OFF)return p>=2?UINT64_C(65536):0;
 return quant(Gv[p][(long)w*SS+s],gz[p][w]);
}
static int exact_check(void){
 uint64_t *zz[4];for(int p=0;p<4;p++){zz[p]=malloc(nw*sizeof(uint64_t));for(int w=0;w<nw;w++)zz[p][w]=quant(gz[p][w],gz[p][w]);}
 uint64_t bad=0,caps=0,checked=0,prods=0;
 for(int w=0;w<nw;w++){
  int ain=wcode[w]&3;U128 rows[4]={0};
  for(int d=0;d<4;d++){int t=tgt[w][d];if(t<0)continue;int k=kind[w][d];
   if(k==2){for(int p=0;p<4;p++){rows[p]+=(U128)q5*zz[p][t];prods++;}}
   else {uint64_t dg[4]={k==0?qs:qt,k==0?qs:q3,k==0?qs:q3,q3};for(int p=0;p<4;p++){rows[p]+=(U128)dg[p]*zz[p][t];prods++;}int ps=k==0?1:0,pd=k==0?3:2;rows[ps]+=(U128)qresp[ain][d][4]*zz[pd][t];prods++;}
  }
  for(int p=0;p<4;p++)if(rows[p]>(U128)QSCALE*zz[p][w])bad++;
 }
 if(bad){printf("EXACT_RIGHT_FAILED %llu\n",(unsigned long long)bad);return 0;}
 for(int w=0;w<nw;w++){
  int ain=wcode[w]&3;
  for(int s0=0;s0<SS;s0++){
   int x=s0/SIDE-RR,y=s0%SIDE-RR;
   if((x==0&&y==0)||(x==zvx-OFF&&y==zvy-OFF))continue;
   U128 rows[4]={0};int known=(x==-1&&y==0)||(D0>=0&&x==-1+dx[D0]&&y==dy[D0]);
   int dead=4;for(int d=0;d<4;d++)if(x+dx[d]==0&&y+dy[d]==0)dead=d;
   for(int d=0;d<4;d++){
    int t=tgt[w][d];if(t<0)continue;int k=kind[w][d];
    if(known){if(k==2)continue;if(D0>=0&&((x==-1&&y==0&&d==D0)||(x==-1+dx[D0]&&y==dy[D0]&&d==(D0+2)%4)))continue;}
    int sn=nbg[d][s0];uint64_t qv[4];for(int p=0;p<4;p++)qv[p]=sn<0?zz[p][t]:qu(p,t,sn);
    if(k==2||known){for(int p=0;p<4;p++){rows[p]+=(U128)q5*qv[p];prods++;}}
    else{uint64_t dg[4]={k==0?qs:qt,k==0?qs:q3,k==0?qs:q3,q3};for(int p=0;p<4;p++){rows[p]+=(U128)dg[p]*qv[p];prods++;}int ps=k==0?1:0,pd=k==0?3:2;rows[ps]+=(U128)qresp[ain][d][dead]*qv[pd];prods++;}
   }
   for(int p=0;p<4;p++){uint64_t val=qu(p,w,s0);if(val>zz[p][w])caps++;if(rows[p]>(U128)QSCALE*val)bad++;checked++;}
  }
 }
 printf("EXACT_CHECK inequalities=%llu bad=%llu outside_cap_failures=%llu integer_products=%llu scale_bits=48 padding_bits=24\n",(unsigned long long)checked,(unsigned long long)bad,(unsigned long long)caps,(unsigned long long)prods);
 if(bad||caps)return 0;
 const char*fn=getenv("CERT_OUTPUT");gzFile gf=fn?gzopen(fn,"wb1"):NULL;
 if(gf){long hdr[9]={m,L,RR,nw,SS,zvx-OFF,zvy-OFF,16,D0};gzwrite(gf,hdr,sizeof hdr);for(int p=0;p<4;p++)for(int w=0;w<nw;w++){uint32_t u=zz[p][w];gzwrite(gf,&u,sizeof u);};}
 uint64_t *tmp=malloc(SS*sizeof(uint64_t));
 for(int p=0;p<4;p++)for(int w=0;w<nw;w++){
  for(int si=0;si<SS;si++)tmp[si]=qu(p,w,si);
  if(gf)for(int si=0;si<SS;si++){uint32_t u=tmp[si];gzwrite(gf,&u,sizeof u);}
  for(int si=0;si<SS;si++)Gv[p][(long)w*SS+si]=(double)tmp[si]/65536;
 }
 if(gf)gzclose(gf);free(tmp);for(int p=0;p<4;p++)free(zz[p]);
 return 1;
}

int main(int argc,char**argv){
 if(argc<3)return 1;D0=atoi(argv[2]);gzFile f=gzopen(argv[1],"rb");if(!f)return 1;long hdr[7];if(gzread(f,hdr,sizeof hdr)!=sizeof hdr)return 1;
 m=hdr[0];L=hdr[1];RR=hdr[2];SIDE=2*RR+1;SS=SIDE*SIDE;zvx=OFF+hdr[5];zvy=OFF+hdr[6];char X=hdr[5]==1?'B':'C';
 fesetround(FE_UPWARD);volatile double one=1,three=3,five=5;xs=one/nextafter(.961,0);xt=one/nextafter(.935,0);third=one/three;fifth=one/five;
 CA[0]=nextafter(.145217,INFINITY);CB[0]=nextafter(.352782,INFINITY);CBP[0]=nextafter(.340008,INFINITY);CA[1]=nextafter(.150000,INFINITY);CB[1]=nextafter(.357549,INFINITY);CBP[1]=nextafter(.344661,INFINITY);hB=1;hC=1.20;ca=CA[0];cb=CB[0];
 build_windows();compress_windows();if(nw!=hdr[3]||SS!=hdr[4])return 1;uint64_t*tmp=malloc(SS*sizeof(uint64_t));
 for(int p=0;p<4;p++){gz[p]=malloc(nw*sizeof(double));if(gzread(f,tmp,nw*sizeof(uint64_t))!=nw*sizeof(uint64_t))return 1;for(int w=0;w<nw;w++)gz[p][w]=ldexp((double)tmp[w],-48);}
 for(int p=0;p<4;p++){Gv[p]=malloc((long)nw*SS*sizeof(double));if(!Gv[p])return 1;for(int w=0;w<nw;w++){if(gzread(f,tmp,SS*sizeof(uint64_t))!=SS*sizeof(uint64_t))return 1;for(int si=0;si<SS;si++)Gv[p][(long)w*SS+si]=ldexp((double)tmp[si],-48);}}
 gzclose(f);free(tmp);
 for(int d=0;d<4;d++){nbg[d]=malloc(SS*sizeof(int));for(int si=0;si<SS;si++){int x=si/SIDE+dx[d],y=si%SIDE+dy[d];nbg[d][si]=(x<0||y<0||x>=SIDE||y>=SIDE)?-1:x*SIDE+y;}}
 double t=(double)clock()/CLOCKS_PER_SEC;int ok=exact_check();double bound=prefval(X);printf("COARSE_FINAL exact=%s bound %.12g ratio %.12g\n",ok?"OK":"FAILED",bound,bound/(X=='B'?hB:hC));struct rusage ru;getrusage(RUSAGE_SELF,&ru);printf("COARSE_PROFILE maxrss_bytes=%ld cpu=%.6f\n",ru.ru_maxrss,(double)clock()/CLOCKS_PER_SEC-t);return ok?0:1;
}
