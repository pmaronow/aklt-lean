from pathlib import Path
root=Path(__file__).resolve().parents[1]
s=(root/'experiments/stationary_split.c').read_text()
helper=r'''
#include "stationary_weights.h"
typedef unsigned __int128 U128;
static uint64_t quant(double v,double z){return (uint64_t)ceil(ldexp(v+ldexp(z,-24),48));}
static uint64_t qu(int p,int w,int s){
 int x=s/SIDE-RR,y=s%SIDE-RR;
 if(x==0&&y==0)return 0;
 if(x==zvx-OFF&&y==zvy-OFF)return p>=2?QSCALE:0;
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
 if(gf){long hdr[7]={m,L,RR,nw,SS,zvx-OFF,zvy-OFF};gzwrite(gf,hdr,sizeof hdr);for(int p=0;p<4;p++)gzwrite(gf,zz[p],nw*sizeof(uint64_t));}
 uint64_t *tmp=malloc(SS*sizeof(uint64_t));
 for(int p=0;p<4;p++)for(int w=0;w<nw;w++){
  for(int si=0;si<SS;si++)tmp[si]=qu(p,w,si);
  if(gf)gzwrite(gf,tmp,SS*sizeof(uint64_t));
  for(int si=0;si<SS;si++)Gv[p][(long)w*SS+si]=(double)tmp[si]/QSCALE;
 }
 if(gf)gzclose(gf);free(tmp);for(int p=0;p<4;p++)free(zz[p]);
 return 1;
}
'''
# insert before main but after all functions and globals it uses
p=s.index('int main(int argc,char**argv)');s=s[:p]+helper+s[p:]
a=s.index(' const char*fn=getenv("CERT_OUTPUT");if(fn){FILE*f=fopen(fn,"wb")')
b=s.index(' struct rusage ru;',a)
s=s[:a]+''' int exok=exact_check();printf("DYADIC_FINAL exact=%s bound %.12g ratio %.12g\\n",exok?"OK":"FAILED",prefval(X),prefval(X)/(X=='B'?hB:hC));
'''+s[b:]
(root/'experiments/stationary_exact.c').write_text(s)
