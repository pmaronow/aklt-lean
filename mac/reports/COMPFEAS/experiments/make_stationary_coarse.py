from pathlib import Path
root=Path(__file__).resolve().parents[1];s=(root/'experiments/stationary_exact.c').read_text()
s=s.replace('return (uint64_t)ceil(ldexp(v+ldexp(z,-24),48));','double a=ceil(ldexp(v+ldexp(z,-14),16));if(!isfinite(a)||a<0||a>=4294967296.0){fprintf(stderr,"coarse quant overflow %.17g\\n",a);exit(1);}return (uint64_t)a;')
s=s.replace('scale_bits=48 padding_bits=24','value_scale_bits=16 padding_bits=14 coefficient_scale_bits=48')
s=s.replace('return p>=2?QSCALE:0;','return p>=2?UINT64_C(65536):0;')
s=s.replace('gzwrite(gf,zz[p],nw*sizeof(uint64_t))','for(int w=0;w<nw;w++){uint32_t u=zz[p][w];gzwrite(gf,&u,sizeof u);}')
s=s.replace('long hdr[7]={m,L,RR,nw,SS,zvx-OFF,zvy-OFF};','long hdr[9]={m,L,RR,nw,SS,zvx-OFF,zvy-OFF,16,D0};')
s=s.replace('if(gf)gzwrite(gf,tmp,SS*sizeof(uint64_t));','if(gf)for(int si=0;si<SS;si++){uint32_t u=tmp[si];gzwrite(gf,&u,sizeof u);}')
s=s.replace('(double)tmp[si]/QSCALE','(double)tmp[si]/65536')
a=s.index('int main(int argc,char**argv)')
s=s[:a]+r'''
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
'''
(root/'experiments/stationary_coarse.c').write_text(s)
