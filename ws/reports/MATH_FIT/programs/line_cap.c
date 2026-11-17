#define main original_main
#include "tailmem6_min.c"
#undef main
static double *zax,*linev;static int RR,SS;static double aa;
static double axis_cap(int axis,int p,int w,int s){double a=zax[((long)(2*axis)*4+p)*nw+w]*exp(-aa*s),b=zax[((long)(2*axis+1)*4+p)*nw+w]*exp(aa*s);return fmin(a,b)*(1+1e-10);}
static double kval(int ain,int d){return kappa(1000,1000,ain,d,0);}
int main(int argc,char**argv){
 m=atoi(argv[1]);RR=atoi(argv[2]);int nit=atoi(argv[3]);aa=atof(argv[4]);SS=2*RR+1;
 xs=1/.961;xt=1/.935;third=1.0/3;fifth=.2;hB=1;hC=1.2;
 CA[0]=.145217;CB[0]=.352782;CBP[0]=.340008;CA[1]=.150000;CB[1]=.357549;CBP[1]=.344661;
 build_windows();compress_windows();
 zax=malloc(16L*nw*sizeof(double));FILE*f=fopen(argv[5],"rb");if(!f||fread(zax,sizeof(double),16L*nw,f)!=16L*nw)return 2;fclose(f);
 linev=malloc(8L*nw*SS*sizeof(double));
 for(int axis=0;axis<2;axis++)for(int p=0;p<4;p++)for(int w=0;w<nw;w++)for(int s=0;s<SS;s++)linev[(((long)axis*4+p)*nw+w)*SS+s]=(s==RR&&p>=2)?1:axis_cap(axis,p,w,s-RR);
 double start=(double)clock()/CLOCKS_PER_SEC;
 for(int it=0;it<nit;it++){
  double diff=0,up=0;
  for(int axis=0;axis<2;axis++)for(int w=0;w<nw;w++)for(int s=0;s<SS;s++){
   double v[4]={0};int ain=wcode[w]&3;
   for(int d=0;d<4;d++){
    int t=tgt[w][d];if(t<0)continue;int k=kind[w][d];int sn=s+(axis==0?dx[d]:dy[d]);double vv[4];
    for(int p=0;p<4;p++)vv[p]=sn<0||sn>=SS?axis_cap(axis,p,t,s-RR+(axis==0?dx[d]:dy[d])):linev[(((long)axis*4+p)*nw+t)*SS+sn];
    if(k==2){for(int p=0;p<4;p++)v[p]+=.2*vv[p];}
    else if(k==0){double ws=xs/3,kap=kval(ain,d);v[0]+=ws*vv[0];v[1]+=ws*(vv[1]+kap*vv[3]);v[2]+=ws*vv[2];v[3]+=vv[3]/3;}
    else{double wt=xt/3,kap=kval(ain,d);v[0]+=wt*(vv[0]+kap*vv[2]);v[1]+=vv[1]/3;v[2]+=vv[2]/3;v[3]+=vv[3]/3;}
   }
   if(s==RR){v[2]=v[3]=1;}
   for(int p=0;p<4;p++){long j=(((long)axis*4+p)*nw+w)*SS+s;double old=linev[j];diff=fmax(diff,(old-v[p])/(1+old));up=fmax(up,(v[p]-old)/(1+old));linev[j]=v[p];}
  }
  if((it+1)%100==0){printf("ITER %d diff %.6g up %.6g cpu %.3f\n",it+1,diff,up,(double)clock()/CLOCKS_PER_SEC-start);fflush(stdout);}
 }
 double mx[4]={0},omax[2]={0};int r0=0;
 for(int axis=0;axis<2;axis++)for(int p=0;p<4;p++)for(int w=0;w<nw;w++)for(int s=0;s<SS;s++){
  double v=linev[(((long)axis*4+p)*nw+w)*SS+s];mx[p]=fmax(mx[p],v);
  if(p>=2&&s!=RR){omax[p-2]=fmax(omax[p-2],v);if(v>1+1e-12&&abs(s-RR)>r0)r0=abs(s-RR);}
 }
 printf("MAX %.12g %.12g %.12g %.12g OFF_C_D %.12g %.12g R0 %d\n",mx[0],mx[1],mx[2],mx[3],omax[0],omax[1],r0);
 f=fopen(argv[6],"wb");long hdr[3]={m,RR,nw};fwrite(hdr,sizeof(long),3,f);fwrite(linev,sizeof(double),8L*nw*SS,f);fclose(f);
 return 0;
}
