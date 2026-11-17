#define main original_main
#include "tailmem6_min.c"
#undef main
static int RR,SIDE,SS,*nbg[4],iternow;
static double *Gv[4],*gz[4],*buf[4],prefix_total;
static uint64_t opedges;
static double capvalue(int p,int w,int x,int y);
static void prefixdfs(int x, int y, int n, double PA, double PB, double QC, double QD, int code) {
  dfsnodes++; levels[n]++;
  if (x == zvx && y == zvy && n > 0) { closedK[n] += sorted_value(n); return; }
  if (n == L) {
    int w=lut[code & ((1 << (2*m))-1)];int ex=x-OFF,ey=y-OFF;int si=(ex+RR)*SIDE+(ey+RR);
    if(w<0){fprintf(stderr,"prefix bad window\n");exit(1);}double vals[4];
    for(int p=0;p<4;p++)vals[p]=abs(ex)<=RR&&abs(ey)<=RR?Gv[p][(long)w*SS+si]:capvalue(p,w,ex,ey);
    prefix_total+=PA*vals[0]+PB*vals[1]+QC*vals[2]+QD*vals[3]; return;
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
static double *capvec,*linevec; static double cap_a; static int lineR,lineS;
static double linevalue(int axis,int p,int w,int t){
 if(t>=-lineR&&t<=lineR)return linevec[(((long)axis*4+p)*nw+w)*lineS+t+lineR]*(1+1e-10);
 double a=capvec[((long)(2*axis)*4+p)*nw+w]*exp(-cap_a*t),b=capvec[((long)(2*axis+1)*4+p)*nw+w]*exp(cap_a*t);
 return fmin(a,b)*(1+1e-10);
}
static double capvalue(int p,int w,int x,int y){double sc=getenv("CAP_SCALE")?atof(getenv("CAP_SCALE")):1;return sc*fmin(linevalue(0,p,w,x-(zvx-OFF)),linevalue(1,p,w,y-(zvy-OFF)));}
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
   for(int p=0;p<4;p++)vv[p]=sn<0?capvalue(p,t,x+dx[d],y+dy[d]):Gv[p][a];
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
 if(L<m+2||L>=OFF-2){fprintf(stderr,"need m+2<=L<R and L<54 (prefix grid limit)\n");return 1;}
 // The prefix uses the original fixed-size grid; only L must fit. R itself may be larger.
 xs=1/nextafter(.961,0);xt=1/nextafter(.935,0);third=1.0/3.0;fifth=1.0/5.0;
 CA[0]=nextafter(.145217,INFINITY);CB[0]=nextafter(.352782,INFINITY);CBP[0]=nextafter(.340008,INFINITY);
 CA[1]=nextafter(.150000,INFINITY);CB[1]=nextafter(.357549,INFINITY);CBP[1]=nextafter(.344661,INFINITY);hB=1;hC=1.20;ca=CA[0];cb=CB[0];
 fesetround(FE_UPWARD);volatile double one=1,three=3,five=5;xs=one/nextafter(.961,0);xt=one/nextafter(.935,0);third=one/three;fifth=one/five;
 if(getenv("CS"))xs=1.0/atof(getenv("CS"));
 if(getenv("CT"))xt=1.0/atof(getenv("CT"));
 if(getenv("HC"))hC=atof(getenv("HC"));
 if(getenv("TIGHT_COEFF"))for(int k=0;k<2;k++){double cc=1.0/(k?xt:xs);double ff=-log(.928*cc)/(1-.928*cc);CA[k]=ff/3-(-log(.928)/(1-.928))/5;CB[k]=ff/3;CBP[k]=-log(cc)/(1-cc)/3;}
 build_windows();compress_windows();K=m+3;build_sites();
 SIDE=2*RR+1;SS=SIDE*SIDE;
 zvx=X=='B'?OFF+1:OFF;zvy=X=='B'?OFF:OFF+1;
 cap_a=atof(getenv("CAP_A"));capvec=malloc(16L*nw*sizeof(double));FILE*cf=fopen(getenv("CAP_FILE"),"rb");if(!cf)return 2;if(fread(capvec,sizeof(double),16L*nw,cf)!=16L*nw)return 3;fclose(cf);
 FILE*lf=fopen(getenv("LINE_FILE"),"rb");long hdr[3];if(!lf||fread(hdr,sizeof(long),3,lf)!=3)return 4;if(hdr[0]!=m||hdr[2]!=nw)return 5;lineR=hdr[1];lineS=2*lineR+1;linevec=malloc(8L*nw*lineS*sizeof(double));if(fread(linevec,sizeof(double),8L*nw*lineS,lf)!=8L*nw*lineS)return 6;fclose(lf);

 for(int p=0;p<4;p++){buf[p]=malloc(SS*sizeof(double));Gv[p]=malloc((long)nw*SS*sizeof(double));gz[p]=malloc(nw*sizeof(double));for(int w=0;w<nw;w++){gz[p][w]=capvalue(p,w,0,0);for(int s=0;s<SS;s++)Gv[p][(long)w*SS+s]=capvalue(p,w,s/SIDE-RR,s%SIDE-RR)/(getenv("CAP_SCALE")?atof(getenv("CAP_SCALE")):1);}}

 for(int d=0;d<4;d++){nbg[d]=malloc(SS*sizeof(int));for(int s=0;s<SS;s++){int x=s/SIDE+dx[d],y=s%SIDE+dy[d];nbg[d][s]=(x<0||y<0||x>=SIDE||y>=SIDE)?-1:x*SIDE+y;}}
 zvx=X=='B'?OFF+1:OFF;zvy=X=='B'?OFF:OFF+1;
 int sv=(zvx-OFF+RR)*SIDE+(zvy-OFF+RR),sc=RR*SIDE+RR;
 for(int p=0;p<4;p++)for(int w=0;w<nw;w++){Gv[p][(long)w*SS+sc]=0;Gv[p][(long)w*SS+sv]=p>=2?1:0;}
 double cpu0=(double)clock()/CLOCKS_PER_SEC;
 for(int it=0;it<maxit;it++){
  double up=0;for(int w=0;w<nw;w++)bellman_row(w,1,&up);
  if(up>1e-12){fprintf(stderr,"monotonicity failed %.12g\n",up);return 1;}
  if((it+1)%50==0||it==maxit-1){double val=prefval(X);printf("ITER %d bound %.12g ratio %.12g max_increase %.3g cpu %.3f\n",it+1,val,val/(X=='B'?hB:hC),up,(double)clock()/CLOCKS_PER_SEC-cpu0);fflush(stdout);if(getenv("EARLY")&&it>=100&&val/(X=='B'?hB:hC)<.98)break;}
 }
 double up=0;for(int w=0;w<nw;w++)bellman_row(w,0,&up);
 printf("FINAL_CHECK max_relative_increase %.12g bound %.12g\n",up,prefval(X));
 double bdr[4]={0};for(int p=0;p<4;p++)for(int w=0;w<nw;w++)for(int s=0;s<SS;s++){int xx=s/SIDE-RR,yy=s%SIDE-RR;if(abs(xx)==RR||abs(yy)==RR){double v=capvalue(p,w,xx,yy);if(v>0&&Gv[p][(long)w*SS+s]/v>bdr[p])bdr[p]=Gv[p][(long)w*SS+s]/v;}}
 printf("BOUNDARY %.12g %.12g %.12g %.12g\n",bdr[0],bdr[1],bdr[2],bdr[3]);
 const char*fn=getenv("CERT_OUTPUT");if(fn){FILE*f=fopen(fn,"wb");long hdr[7]={m,L,RR,nw,SS,X,D0};fwrite(hdr,sizeof(long),7,f);for(int p=0;p<4;p++)fwrite(gz[p],sizeof(double),nw,f);for(int p=0;p<4;p++)fwrite(Gv[p],sizeof(double),(long)nw*SS,f);fclose(f);}
 struct rusage ru;getrusage(RUSAGE_SELF,&ru);printf("PROFILE nw=%d sites=%d edges=%ld state_values=%ld bytes=%ld maxrss_bytes=%ld cpu=%.6f\n",nw,SS,(long)0,(long)nw*SS*4,(long)nw*SS*4*8,ru.ru_maxrss,(double)clock()/CLOCKS_PER_SEC-cpu0);
 return 0;
}
