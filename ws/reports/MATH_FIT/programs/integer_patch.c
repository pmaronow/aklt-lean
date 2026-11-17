#define main original_main
#include "tailmem6_min.c"
#undef main
#include "h3_integer_weights.h"
#include <zlib.h>
typedef unsigned __int128 U128;
static uint32_t *uv,*lv;static int RR,SIDE,SS,LR,LS,vxx,vyy,dd0;
static size_t ui(int p,int w,int s){return ((size_t)p*nw+w)*SS+s;}
static uint32_t linev(int axis,int p,int w,int t){if(abs(t)>LR){fprintf(stderr,"line lookup out of range\n");exit(3);}return lv[(((size_t)axis*4+p)*nw+w)*LS+t+LR];}
static uint32_t outer(int p,int w,int x,int y){uint32_t a=linev(0,p,w,x-vxx),b=linev(1,p,w,y-vyy);return a<b?a:b;}
static uint64_t diagw(int p,int k){return k==2?q5:(p==0?(k==0?qs:qt):(p==1||p==2?(k==0?qs:q3):q3));}
static uint32_t nextv(int p,int w,int x,int y){if(abs(x)>RR||abs(y)>RR)return outer(p,w,x,y);return uv[ui(p,w,(x+RR)*SIDE+y+RR)];}
static U128 rowval(int p,int w,int x,int y){
 U128 sum=0;int ain=wcode[w]&3,known=(x==-1&&y==0)||(x==-1+dx[dd0]&&y==dy[dd0]);int delta=4;
 for(int d=0;d<4;d++)if(x+dx[d]==0&&y+dy[d]==0)delta=d;
 for(int d=0;d<4;d++){
  int t=tgt[w][d];if(t<0)continue;int k=kind[w][d];
  if(known&&(k==2||(x==-1&&y==0&&d==dd0)||(x==-1+dx[dd0]&&y==dy[dd0]&&d==(dd0+2)%4)))continue;
  int nx=x+dx[d],ny=y+dy[d];sum+=(U128)(known?q5:diagw(p,k))*nextv(p,t,nx,ny);
  if(!known&&((p==0&&k==1)||(p==1&&k==0)))sum+=(U128)qresp[ain][d][delta]*nextv(p==0?2:3,t,nx,ny);
 }return sum;
}
static void gzwriteall(gzFile f,const void*p,size_t n){if(gzwrite(f,p,n)!=(int)n){fprintf(stderr,"write failed\n");exit(4);}}
int main(int argc,char**argv){
 if(argc<5)return 2;char X=argv[1][0];RR=atoi(argv[2]);int maxit=atoi(argv[3]);dd0=atoi(argv[4]);SIDE=2*RR+1;SS=SIDE*SIDE;vxx=X=='B'?1:0;vyy=X=='B'?0:1;
 m=10;build_windows();compress_windows();FILE*f=fopen("data/line_integer.bin","rb");long hdr[5];if(!f||fread(hdr,sizeof(long),5,f)!=5)return 2;LR=hdr[1];LS=2*LR+1;if(hdr[0]!=m||hdr[2]!=nw||hdr[3]!=VBITS||hdr[4]!=48)return 2;
 lv=malloc(8L*nw*LS*4);if(fread(lv,4,8L*nw*LS,f)!=8L*nw*LS)return 2;fclose(f);uv=malloc(4L*nw*SS*4);
 for(int p=0;p<4;p++)for(int w=0;w<nw;w++)for(int s=0;s<SS;s++){int x=s/SIDE-RR,y=s%SIDE-RR;uv[ui(p,w,s)]=(x==0&&y==0)?0:((x==vxx&&y==vyy)?(p>=2?VSCALE:0):outer(p,w,x,y));}
 clock_t tic=clock();uint64_t ups=0;
 for(int it=0;it<maxit;it++){
  uint64_t changed=0,up=0;
  for(int w=0;w<nw;w++)for(int s=0;s<SS;s++){
   int x=s/SIDE-RR,y=s%SIDE-RR;if((x==0&&y==0)||(x==vxx&&y==vyy))continue;
   uint64_t v[4];for(int p=0;p<4;p++){U128 a=rowval(p,w,x,y);v[p]=(uint64_t)((a+QSCALE-1)>>48);if(v[p]>UINT32_MAX)return 3;}
   for(int p=0;p<4;p++){size_t j=ui(p,w,s);changed+=v[p]!=uv[j];up+=v[p]>uv[j];uv[j]=v[p];}
  }
  ups+=up;if((it+1)%100==0||changed==0){printf("ITER %d changed %llu up %llu cpu %.3f\n",it+1,(unsigned long long)changed,(unsigned long long)up,(double)(clock()-tic)/CLOCKS_PER_SEC);fflush(stdout);}if(changed==0)break;
 }
 uint64_t bad=0,caps=0,terminal=0,rows=0;uint32_t mx=0;
 for(int p=0;p<4;p++)for(int w=0;w<nw;w++)for(int s=0;s<SS;s++){
  int x=s/SIDE-RR,y=s%SIDE-RR;uint32_t v=uv[ui(p,w,s)];if(v>mx)mx=v;if(v>outer(p,w,x,y))caps++;
  if(x==0&&y==0){if(v!=0)terminal++;}
  else if(x==vxx&&y==vyy){if(v!=(p>=2?VSCALE:0))terminal++;}
  else{rows++;if(rowval(p,w,x,y)>(U128)QSCALE*v)bad++;}
 }
 printf("EXACT_PATCH X=%c d=%d R=%d rows=%llu bad=%llu caps=%llu terminal=%llu ups=%llu max=%u cpu=%.6f\n",X,dd0,RR,(unsigned long long)rows,(unsigned long long)bad,(unsigned long long)caps,(unsigned long long)terminal,(unsigned long long)ups,mx,(double)(clock()-tic)/CLOCKS_PER_SEC);
 if(bad||caps||terminal)return 1;
 char name[256];snprintf(name,sizeof name,"data/line_%c_m10_R%d_d%d_integer.bin.gz",X,RR,dd0);gzFile of=gzopen(name,"wb1");long head[9]={m,12,RR,nw,SS,vxx,vyy,VBITS,dd0};gzwriteall(of,head,sizeof head);
 uint32_t*tmp=malloc(nw*4);for(int p=0;p<4;p++){for(int w=0;w<nw;w++)tmp[w]=linev(0,p,w,0);gzwriteall(of,tmp,nw*4);}
 for(int p=0;p<4;p++)for(int w=0;w<nw;w++)gzwriteall(of,uv+ui(p,w,0),SS*4);gzclose(of);return 0;
}
