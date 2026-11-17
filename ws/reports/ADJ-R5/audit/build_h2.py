from pathlib import Path
src=Path('/home/ubuntu/aklt/manuscript/bundle/programs/h2-trails/alm8.c').read_text()
src=src.replace('#include <stdio.h>', '#include <stdio.h>\n#include <stdint.h>\n#include <inttypes.h>')
src=src.replace('  m = atoi(argv[1]); k = atoi(argv[2]);',
'''  if(argc != 5) return 2;
  m = atoi(argv[1]); k = atoi(argv[2]);
  /* This audit copy certifies only the instance under discussion. */
  if(m!=8 || k!=8 || atoi(argv[3])!=9610 || atoi(argv[4])!=9350) return 2;''')
src=src.replace('for (int i = 1; i < 24; i++)', 'for (int i = 1; i <= m; i++)')
helper=r'''
static uint64_t *hnum, sums[9][9];
static int canonical(int code) {
  int best=code;
  for(int sign=-1;sign<=1;sign+=2)for(int r=0;r<4;r++) {
    int c=0;
    for(int i=0;i<m;i++) {
      int d=(code/pw4[i])%4;
      c+=((sign*d+r+4)%4)*pw4[i];
    }
    if(c<best)best=c;
  }
  return best;
}
/* Re-enumerate block continuations with integers, independently of CSR values. */
static void ext_integer(int step,int x,int y,int last,int a,int t) {
  if(step==k) {
    int c=0;
    for(int i=0;i<m;i++)c+=dirs[k+i]*pw4[i];
    int j=code2idx[c];if(j<0)abort();
    sums[a][t]+=hnum[j];return;
  }
  for(int d=0;d<4;d++) {
    unsigned char *b=bondp(x,y,d);if(*b)continue;
    int revisit=dep[x][y]>0;
    *b=1;dep[x][y]++;dirs[m+step]=d;
    ext_integer(step+1,x+dx[d],y+dy[d],d,a+(!revisit&&d==last),t+(!revisit&&d!=last));
    *b=0;dep[x][y]--;
  }
}
'''
src=src.replace('int main(int argc, char **argv) {',helper+'\nint main(int argc, char **argv) {')
src=src.replace('    /* rigorous Collatz-Wielandt bound with upward rounding */',
'''    hnum=malloc(nst*sizeof(uint64_t));
    for(int i=0;i<nst;i++)hnum[i]=(uint64_t)ceil(fmax(xv[i],0.01)*1e12);
    for(int i=0;i<nst;i++)hnum[i]=hnum[code2idx[canonical(states[i])]];
    for(int i=0;i<nst;i++)xv[i]=(double)hnum[i]/1e12;
    /* rigorous Collatz-Wielandt bound with upward rounding */''')
start=src.index('    fesetround(FE_TONEAREST);\n    double rate = exp(log(best) / k)')
end=src.index('    fflush(stdout);',start)
src=src[:start]+r'''    printf("directed quotient_up=%.17g hex=%a\n",best,best);
    uint64_t mn=hnum[0],mx=hnum[0];int orbits=0;
    FILE *out=fopen("audit/h2_integer_certificate.tsv","w");
    fprintf(out,"H 8 8 7500\n");
    for(int i=0;i<nst;i++) {
      if(hnum[i]<mn)mn=hnum[i];if(hnum[i]>mx)mx=hnum[i];
      if(states[i]!=canonical(states[i]))continue;
      orbits++;
      fprintf(out,"h %d %" PRIu64 "\n",states[i],hnum[i]);
      memset(hb,0,sizeof hb);memset(vb,0,sizeof vb);memset(dep,0,sizeof dep);memset(sums,0,sizeof sums);
      int x=G/2,y=G/2,last=-1;
      for(int l=0;l<m;l++) {
        int d=states[i]/pw4[l]%4;dirs[l]=d;
        *bondp(x,y,d)=1;dep[x][y]++;x+=dx[d];y+=dy[d];last=d;
      }
      ext_integer(0,x,y,last,0,0);
      for(int a=0;a<=k;a++)for(int t=0;t<=k-a;t++)if(sums[a][t])
        fprintf(out,"S %d %d %d %d %" PRIu64 "\n",states[i],a,t,k-a-t,sums[a][t]);
    }
    fclose(out);
    printf("integer vector min=%" PRIu64 " max=%" PRIu64 " orbits=%d\n",mn,mx,orbits);
''' +src[end:]
Path('audit/alm8_checked.c').write_text(src)
