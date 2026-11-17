/* Independent departure-count histogram, with either initial direction convention. */
#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#define N 15
#define SIDE 64
static unsigned char used[SIDE][SIDE][2],departed[SIDE][SIDE];
static uint64_t count[2][N+1][N+1][N+1];
static const int dx[]={1,0,-1,0},dy[]={0,1,0,-1};
static unsigned char *bond(int x,int y,int d){
  if(d==2)x--; if(d==3)y--;
  return &used[x][y][d%2];
}
static void visit(int x,int y,int last,int n,int s,int t,int forbid){
  count[0][n][s][t]++;if(forbid)count[1][n][s][t]++;
  if(n==N)return;
  for(int d=0;d<4;d++){
    unsigned char *e=bond(x,y,d);if(*e)continue;
    int fresh=!departed[x][y];
    *e=1;departed[x][y]++;
    visit(x+dx[d],y+dy[d],d,n+1,s+(fresh&&d==last),t+(fresh&&d!=last),forbid&&!(n==0&&d==2));
    departed[x][y]--;*e=0;
  }
}
int main(void){
  visit(SIDE/2,SIDE/2,0,0,0,0,1);
  puts("n,s,t,all,forbid");
  for(int n=0;n<=N;n++)for(int s=0;s<=n;s++)for(int t=0;t<=n-s;t++)if(count[0][n][s][t])
    printf("%d,%d,%d,%" PRIu64 ",%" PRIu64 "\n",n,s,t,count[0][n][s][t],count[1][n][s][t]);
}
