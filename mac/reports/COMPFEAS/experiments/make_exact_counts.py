from pathlib import Path
root=Path(__file__).resolve().parents[1]
s=(root/'experiments/tailmem6_min.c').read_text()
helper=r'''
static uint64_t count_first=0,count_rev=0,count_known=0,count_skip=0;
static void count_step(int exact) {
 int special[2]={iu,id0};int ns=D0>=0?2:1;
 for(int w=0;w<nw;w++)for(int d=0;d<4;d++)if(tgt[w][d]>=0){
  int k=kind[w][d];uint64_t reg=NSITE-(exact?ns:0);
  if(k==2)count_rev+=reg;else count_first+=reg;
  if(exact)for(int j=0;j<ns;j++){
   int ss=special[j];
   if(k==2||(D0>=0&&((ss==iu&&d==D0)||(ss==id0&&d==(D0+2)%4))))count_skip++;
   else count_known++;
  }
 }
}
static void exact_profile(void) {
 fprintf(stderr,"ARITHMETIC first=%llu revisit=%llu known=%llu skipped=%llu fp_mul=%llu fp_add=%llu\n",(unsigned long long)count_first,(unsigned long long)count_rev,(unsigned long long)count_known,(unsigned long long)count_skip,(unsigned long long)(5*count_first+4*(count_rev+count_known)),(unsigned long long)(5*count_first+4*(count_rev+count_known)));
}
'''
s=s.replace('/* ---------------- one DP step on the torus ---------------- */',helper+'\n/* ---------------- one DP step on the torus ---------------- */')
s=s.replace('  steps++;','  steps++; count_step(exact);')
s=s.replace('atexit(profile);','atexit(profile); atexit(exact_profile);')
(root/'experiments/tailmem6_count.c').write_text(s)
