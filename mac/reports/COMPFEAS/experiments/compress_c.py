from pathlib import Path
root=Path(__file__).resolve().parents[1]
load='''
static void compress_windows(void) {
 const char *fn=getenv("AUTOMATON"); if(!fn)return;
 FILE *f=fopen(fn,"r");if(!f){perror(fn);exit(1);}int nraw,nclass;
 if(fscanf(f,"%d%d",&nraw,&nclass)!=2||nraw!=nw){fprintf(stderr,"bad partition header\\n");exit(1);}
 int *cls=malloc(nw*sizeof(int));
 for(int i=0;i<nraw;i++){int code,cl;if(fscanf(f,"%d%d",&code,&cl)!=2||code!=wcode[i]||cl<0||cl>=nclass){fprintf(stderr,"bad partition map\\n");exit(1);}cls[i]=cl;}
 int *newcode=malloc(nclass*sizeof(int));int (*newt)[4]=malloc(nclass*sizeof *newt);unsigned char (*newk)[4]=malloc(nclass*sizeof *newk);
 for(int c=0;c<nclass;c++){
  int ks[4];if(fscanf(f,"%d%d%d%d%d%d%d%d%d",&newcode[c],&newt[c][0],&newt[c][1],&newt[c][2],&newt[c][3],&ks[0],&ks[1],&ks[2],&ks[3])!=9){fprintf(stderr,"bad partition states\\n");exit(1);}
  for(int d=0;d<4;d++)newk[c][d]=ks[d]<0?255:ks[d];
 }
 for(int i=0;i<nraw;i++)for(int d=0;d<4;d++){
  int c=cls[i],t=tgt[i][d];if((t<0? -1:cls[t])!=newt[c][d]||(t>=0&&kind[i][d]!=newk[c][d])){fprintf(stderr,"bad quotient transition\\n");exit(1);}
  if(t>=0&&kind[i][d]!=2&&(wcode[i]&3)!=(newcode[c]&3)){fprintf(stderr,"bad quotient direction\\n");exit(1);}
 }
 for(int i=0;i<nraw;i++)lut[wcode[i]]=cls[i];
 fprintf(stderr,"QUOTIENT raw=%d minimized=%d\\n",nw,nclass);
 free(wcode);free(tgt);free(kind);free(cls);wcode=newcode;tgt=newt;kind=newk;nw=nclass;fclose(f);
}
'''
for name in ['tailmem4','tailmem5','tailmem6']:
 s=(root/'experiments'/f'{name}_profile.c').read_text()
 s=s.replace('static int modK(int z)',load+'\nstatic int modK(int z)')
 s=s.replace('build_windows(); build_sites();','build_windows(); compress_windows(); build_sites();')
 (root/'experiments'/f'{name}_min.c').write_text(s)
