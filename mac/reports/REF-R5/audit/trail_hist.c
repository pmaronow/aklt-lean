#include <stdio.h>
#define G 64
#define N 15
static unsigned char hb[G][G], vb[G][G], dep[G][G];
static const int dx[4]={1,0,-1,0}, dy[4]={0,1,0,-1};
static unsigned long long hist[N+1][N+1][N+1], restricted[N+1][N+1][N+1];
static unsigned char *bond(int x,int y,int d) {
  if(d==0)return &hb[x][y]; if(d==1)return &vb[x][y];
  if(d==2)return &hb[x-1][y]; return &vb[x][y-1];
}
static void dfs(int x,int y,int len,int last,int ns,int nt,int allowed) {
  ++hist[len][ns][nt]; if(allowed)++restricted[len][ns][nt];
  if(len==N)return;
  for(int d=0;d<4;++d) {
    unsigned char *b=bond(x,y,d); if(*b)continue;
    int rev=dep[x][y]>0;
    *b=1; ++dep[x][y];
    dfs(x+dx[d],y+dy[d],len+1,d,ns+(!rev && d==last),nt+(!rev && d!=last),allowed && !(len==0 && d==2));
    --dep[x][y]; *b=0;
  }
}
int main(void) {
  dfs(G/2,G/2,0,0,0,0,1);
  puts("n,ns,nt,all,forbid_initial_reverse");
  for(int n=0;n<=N;++n)for(int s=0;s<=n;++s)for(int t=0;t<=n-s;++t)
    if(hist[n][s][t])printf("%d,%d,%d,%llu,%llu\n",n,s,t,hist[n][s][t],restricted[n][s][t]);
}
