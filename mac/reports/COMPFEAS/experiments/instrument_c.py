from pathlib import Path
root=Path(__file__).resolve().parents[1]
for name in ['tailmem4','tailmem5','tailmem6','tailmem7']:
 s=(root/'programs/h3-tail/code'/f'{name}.c').read_text()
 s=s.replace('#include <stdio.h>', '#include <stdio.h>\n#include <stdint.h>\n#include <time.h>\n#include <sys/resource.h>\nstatic uint64_t dfsnodes=0, leaves=0, closedcalls=0, sortpasses=0, steps=0;\nstatic uint64_t levels[128];\nstatic double startcpu;')
 s=s.replace('static void dfs(int x, int y, int n, double PA, double PB, double QC, double QD, int code) {','static void dfs(int x, int y, int n, double PA, double PB, double QC, double QD, int code) {\n  dfsnodes++; levels[n]++;')
 s=s.replace('static double sorted_value(int n) {','static double sorted_value(int n) {\n  closedcalls++; sortpasses+=n;')
 s=s.replace('if (n == L) {','if (n == L) {\n    leaves++;',1)
 s=s.replace('static void step(int exact) {','static void step(int exact) {\n  steps++;')
 s=s.replace('int main(int argc, char **argv) {','''static void profile(void) {
 uint64_t ne[3]={0,0,0};
 for(int w=0;w<nw;w++)for(int d=0;d<4;d++)if(tgt[w][d]>=0)ne[kind[w][d]]++;
 struct rusage ru; getrusage(RUSAGE_SELF,&ru);
 fprintf(stderr,"PROFILE dfsnodes=%llu leaves=%llu closed=%llu sortpasses=%llu steps=%llu edges_s=%llu edges_t=%llu edges_r=%llu sites=%d cpu=%.6f maxrss_bytes=%ld\\n",(unsigned long long)dfsnodes,(unsigned long long)leaves,(unsigned long long)closedcalls,(unsigned long long)sortpasses,(unsigned long long)steps,(unsigned long long)ne[0],(unsigned long long)ne[1],(unsigned long long)ne[2],NSITE,(double)clock()/CLOCKS_PER_SEC-startcpu,ru.ru_maxrss);
 for(int i=0;i<=L;i++)fprintf(stderr,"LEVEL %d %llu\\n",i,(unsigned long long)levels[i]);
}
int main(int argc, char **argv) {
 startcpu=(double)clock()/CLOCKS_PER_SEC; atexit(profile);''')
 (root/'experiments'/f'{name}_profile.c').write_text(s)
s=(root/'programs/h2-trails/alm8.c').read_text()
s=s.replace('#include <stdio.h>','#include <stdio.h>\n#include <stdint.h>\n#include <time.h>\n#include <sys/resource.h>\nstatic uint64_t nodes=0, terminal=0, mults=0;\nstatic uint64_t levels[64];')
s=s.replace('static void ext(int step, int x, int y, int last, double w) {','static void ext(int step, int x, int y, int last, double w) {\n nodes++; levels[step]++;')
s=s.replace('if (step == k) {','if (step == k) {\n terminal++;',1)
s=s.replace('ext(step + 1, x + dx[d], y + dy[d], d, w * ww);','mults++; ext(step + 1, x + dx[d], y + dy[d], d, w * ww);')
s=s.replace('static int pw4[24];','static uint64_t pw4[24];')
s=s.replace('int main(int argc, char **argv) {','int main(int argc, char **argv) {\n double startcpu=(double)clock()/CLOCKS_PER_SEC;')
s=s.replace('return 0;\n}', '''struct rusage ru; getrusage(RUSAGE_SELF,&ru);
 fprintf(stderr,"PROFILE extnodes=%llu terminal=%llu weight_mults=%llu cpu=%.6f maxrss_bytes=%ld\\n",(unsigned long long)nodes,(unsigned long long)terminal,(unsigned long long)mults,(double)clock()/CLOCKS_PER_SEC-startcpu,ru.ru_maxrss);
 for(int i=0;i<=k;i++)fprintf(stderr,"LEVEL %d %llu\\n",i,(unsigned long long)levels[i]);
 return 0;
}''')
(root/'experiments/alm_profile.c').write_text(s)
