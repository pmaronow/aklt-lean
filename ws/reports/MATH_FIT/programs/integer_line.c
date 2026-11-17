#define main original_main
#include "tailmem6_min.c"
#undef main
#include "h3_integer_weights.h"
typedef unsigned __int128 U128;
static uint32_t *lin,*initial,*tail;static int RR=70,SS=141;
static size_t ix(int axis,int p,int w,int s){return (((size_t)axis*4+p)*nw+w)*SS+s;}
static uint32_t nextval(int axis,int p,int w,int sn){return sn<0||sn>=SS?tail[(((size_t)axis*4+p)*nw+w)*2+(sn<0?0:1)]:lin[ix(axis,p,w,sn)];}
static uint64_t dg(int p,int k){return k==2?q5:(p==0?(k==0?qs:qt):(p==1||p==2?(k==0?qs:q3):q3));}
static U128 rowval(int axis,int p,int w,int s){
 U128 acc=0;int ain=wcode[w]&3;
 for(int d=0;d<4;d++){int t=tgt[w][d];if(t<0)continue;int k=kind[w][d],sn=s+(axis==0?dx[d]:dy[d]);acc+=(U128)dg(p,k)*nextval(axis,p,t,sn);
  if((p==0&&k==1)||(p==1&&k==0))acc+=(U128)qresp[ain][d][4]*nextval(axis,p==0?2:3,t,sn);
 }return acc;
}
static void readall(const char *fn,void *dst,size_t n){FILE*f=fopen(fn,"rb");if(!f||fread(dst,1,n,f)!=n){fprintf(stderr,"read failed %s\n",fn);exit(2);}fclose(f);}
int main(int argc,char**argv){
 m=10;build_windows();compress_windows();size_t count=8L*nw*SS;initial=malloc(count*4);lin=malloc(count*4);tail=malloc(16L*nw*4);
 readall("data/line_init_integer.bin",initial,count*4);memcpy(lin,initial,count*4);readall("data/line_tails_integer.bin",tail,16L*nw*4);
 for(int axis=0;axis<2;axis++)for(int p=2;p<4;p++)for(int w=0;w<nw;w++)lin[ix(axis,p,w,RR)]=VSCALE;
 int nit=argc>1?atoi(argv[1]):2000;clock_t tic=clock();uint64_t totalup=0;
 for(int it=0;it<nit;it++){
  uint64_t changed=0,up=0;
  for(int axis=0;axis<2;axis++)for(int w=0;w<nw;w++)for(int s=0;s<SS;s++)for(int p=0;p<4;p++){
   if(p>=2&&s==RR)continue;
   U128 a=rowval(axis,p,w,s);uint64_t v=(uint64_t)((a+QSCALE-1)>>48);if(v>UINT32_MAX){fprintf(stderr,"overflow\n");return 3;}
   size_t j=ix(axis,p,w,s);changed+=v!=lin[j];up+=v>lin[j];lin[j]=v;
  }
  totalup+=up;
  if((it+1)%100==0||changed==0){printf("ITER %d changed %llu up %llu cpu %.3f\n",it+1,(unsigned long long)changed,(unsigned long long)up,(double)(clock()-tic)/CLOCKS_PER_SEC);fflush(stdout);}
  if(changed==0)break;
 }
 uint64_t bad=0,caps=0,off=0,rows=0;uint32_t mx=0;
 for(int axis=0;axis<2;axis++)for(int p=0;p<4;p++)for(int w=0;w<nw;w++)for(int s=0;s<SS;s++){
  size_t j=ix(axis,p,w,s);uint32_t v=lin[j];if(v>mx)mx=v;
  if(v>initial[j])caps++;
  if(p>=2){if(s==RR){if(v!=VSCALE)bad++;continue;}if(v>VSCALE)off++;}
  rows++;if(rowval(axis,p,w,s)>(U128)QSCALE*v)bad++;
 }
 printf("EXACT_LINE rows=%llu bad=%llu caps=%llu off_excess=%llu total_up=%llu max=%u bits=%d cpu=%.6f\n",(unsigned long long)rows,(unsigned long long)bad,(unsigned long long)caps,(unsigned long long)off,(unsigned long long)totalup,mx,VBITS,(double)(clock()-tic)/CLOCKS_PER_SEC);
 if(bad||caps||off)return 1;
 FILE*f=fopen("data/line_integer.bin","wb");long hdr[5]={10,70,nw,VBITS,48};fwrite(hdr,sizeof(long),5,f);fwrite(lin,4,count,f);fclose(f);return 0;
}
