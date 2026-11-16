from pathlib import Path
root=Path(__file__).resolve().parents[1]
helper='''
static int prefix_cached(void) {
 const char*fn=getenv("PREFIX_CACHE");if(!fn)return 0;
 FILE*f=fopen(fn,"rb");if(!f)return 0;
 long hdr[3];if(fread(hdr,sizeof(long),3,f)!=3||hdr[0]!=nw||hdr[1]!=NSITE||hdr[2]!=L){fprintf(stderr,"bad cache header\\n");exit(1);}
 if(fread(closedK,sizeof(double),256,f)!=256){fprintf(stderr,"bad cache closed\\n");exit(1);}
 for(int p=0;p<4;p++)if(fread(V[p],sizeof(float),(long)nw*NSITE,f)!=(long)nw*NSITE){fprintf(stderr,"bad cache vector\\n");exit(1);}
 fclose(f);fprintf(stderr,"PREFIX_CACHE loaded %s\\n",fn);return 1;
}
static void save_prefix(void) {
 const char*fn=getenv("PREFIX_CACHE");if(!fn)return;
 FILE*f=fopen(fn,"wb");if(!f){perror(fn);exit(1);}long hdr[3]={nw,NSITE,L};
 fwrite(hdr,sizeof(long),3,f);fwrite(closedK,sizeof(double),256,f);
 for(int p=0;p<4;p++)fwrite(V[p],sizeof(float),(long)nw*NSITE,f);
 fclose(f);fprintf(stderr,"PREFIX_CACHE saved %s\\n",fn);
}
'''
for name in ['tailmem5','tailmem6']:
 s=(root/'experiments'/f'{name}_min.c').read_text()
 s=s.replace('/* ---------------- one DP step on the torus ---------------- */',helper+'\n/* ---------------- one DP step on the torus ---------------- */')
 s=s.replace('dfs(zux, zuy, 0, 1.0, 1.0, 0.0, 0.0, 0);','if(!prefix_cached()){dfs(zux, zuy, 0, 1.0, 1.0, 0.0, 0.0, 0);save_prefix();}')
 (root/'experiments'/f'{name}_cached.c').write_text(s)
