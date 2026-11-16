/* Standalone checker for the stored uint32 stationary witness; no floating arithmetic in the check. */
#define main unused_generator_main
#include "tailmem6_min.c"
#undef main
#include "stationary_weights.h"
#include <assert.h>
typedef unsigned __int128 U128;
int main(int argc,char **argv){
 if(argc<4){fprintf(stderr,"usage: certificate.gz B|C D0\n");return 1;}
 _Static_assert(sizeof(long)==8,"64-bit header required");unsigned test=1;if(*(unsigned char*)&test!=1)return 1;
 char X=argv[2][0];int d0=atoi(argv[3]);gzFile f=gzopen(argv[1],"rb");if(!f)return 1;long hdr[9];if(gzread(f,hdr,sizeof hdr)!=sizeof hdr)return 1;
 m=hdr[0];int Lp=hdr[1],R=hdr[2],SSp=hdr[4],SIDEp=2*R+1;long expectednw=hdr[3];
 int vb=hdr[7];if(m<6||m>12||Lp<m+2||Lp>22||R<Lp+2||R>100||vb<1||vb>30||SSp!=SIDEp*SIDEp||hdr[5]!=(X=='B'?1:0)||hdr[6]!=(X=='B'?0:1)||hdr[8]!=d0)return 1;
 build_windows();compress_windows();if(nw!=expectednw)return 1;
 uint32_t *zz[4],*uv[4];for(int p=0;p<4;p++){zz[p]=malloc(nw*sizeof(uint32_t));if(gzread(f,zz[p],nw*4)!=nw*4)return 1;}
 for(int p=0;p<4;p++){uv[p]=malloc((long)nw*SSp*4);if(!uv[p])return 1;for(int w=0;w<nw;w++)if(gzread(f,uv[p]+(long)w*SSp,SSp*4)!=SSp*4)return 1;}
 unsigned char extra;if(gzread(f,&extra,1)!=0)return 1;if(gzclose(f)!=Z_OK)return 1;
 int *nb[4],*known=calloc(SSp,sizeof(int)),*dead=malloc(SSp*sizeof(int));
 int su=(-1+R)*SIDEp+R,sd=(-1+dx[d0]+R)*SIDEp+dy[d0]+R,sc=R*SIDEp+R,sv=(hdr[5]+R)*SIDEp+hdr[6]+R;
 known[su]=known[sd]=1;
 for(int s=0;s<SSp;s++){int x=s/SIDEp-R,y=s%SIDEp-R;dead[s]=4;for(int d=0;d<4;d++)if(x+dx[d]==0&&y+dy[d]==0)dead[s]=d;}
 for(int d=0;d<4;d++){nb[d]=malloc(SSp*sizeof(int));for(int s=0;s<SSp;s++){int x=s/SIDEp+dx[d],y=s%SIDEp+dy[d];nb[d][s]=(x<0||y<0||x>=SIDEp||y>=SIDEp)?-1:x*SIDEp+y;}}
 U128 *sum[4];for(int p=0;p<4;p++)sum[p]=malloc(SSp*sizeof(U128));
 uint64_t bad=0,caps=0,terminal=0,checks=0,products=0;uint32_t maxu=0,maxz=0;clock_t tic=clock();
 for(int w=0;w<nw;w++){
  int ain=wcode[w]&3;U128 zrow[4]={0};
  for(int d=0;d<4;d++){int t=tgt[w][d];if(t<0)continue;int k=kind[w][d];uint64_t dg[4]={k==2?q5:k==0?qs:qt,k==2?q5:k==0?qs:q3,k==2?q5:k==0?qs:q3,k==2?q5:q3};for(int p=0;p<4;p++){zrow[p]+=(U128)dg[p]*zz[p][t];products++;}if(k!=2){int ps=k==0?1:0,pd=k==0?3:2;zrow[ps]+=(U128)qresp[ain][d][4]*zz[pd][t];products++;}}
  for(int p=0;p<4;p++){if(zrow[p]>(U128)QSCALE*zz[p][w]||zz[p][w]==0)bad++;if(p>=2&&zz[p][w]<(UINT32_C(1)<<vb))terminal++;if(zz[p][w]>maxz)maxz=zz[p][w];memset(sum[p],0,SSp*sizeof(U128));}
  for(int d=0;d<4;d++){
   int t=tgt[w][d];if(t<0)continue;int k=kind[w][d];uint64_t dg[4]={k==2?q5:k==0?qs:qt,k==2?q5:k==0?qs:q3,k==2?q5:k==0?qs:q3,k==2?q5:q3};
   for(int s=0;s<SSp;s++){
    if(s==sc||s==sv)continue;
    if(known[s]&&(k==2||(s==su&&d==d0)||(s==sd&&d==(d0+2)%4)))continue;
    int sn=nb[d][s];long j=(long)t*SSp+(sn<0?0:sn);uint32_t v[4];for(int p=0;p<4;p++)v[p]=sn<0?zz[p][t]:uv[p][j];
    for(int p=0;p<4;p++){sum[p][s]+=(U128)(known[s]?q5:dg[p])*v[p];products++;}
    if(!known[s]&&k!=2){int ps=k==0?1:0,pd=k==0?3:2;sum[ps][s]+=(U128)qresp[ain][d][dead[s]]*v[pd];products++;}
   }
  }
  for(int p=0;p<4;p++)for(int s=0;s<SSp;s++){
   uint32_t v=uv[p][(long)w*SSp+s];if(v>maxu)maxu=v;if(v>zz[p][w])caps++;
   if(s==sc){if(v!=0)terminal++;}
   else if(s==sv){if(v!=(p>=2?(UINT32_C(1)<<vb):0))terminal++;}
   else {if(sum[p][s]>(U128)QSCALE*v)bad++;checks++;}
  }
 }
 struct rusage ru;getrusage(RUSAGE_SELF,&ru);printf("INTEGER_FILE_CHECK inequalities=%llu products=%llu bad=%llu cap_fail=%llu terminal_fail=%llu max_u=%u max_z=%u cpu=%.6f maxrss_bytes=%ld\n",(unsigned long long)checks,(unsigned long long)products,(unsigned long long)bad,(unsigned long long)caps,(unsigned long long)terminal,maxu,maxz,(double)(clock()-tic)/CLOCKS_PER_SEC,ru.ru_maxrss);
 return bad||caps||terminal?1:0;
}
