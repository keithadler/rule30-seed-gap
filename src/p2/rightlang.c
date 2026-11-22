// Which words e = (column 1 at the "free" times) can a right half produce, with column 0 = (t+ph)&1 ?
// DFS over right-half bits R(1..M); R(1..m+1) decides y(m)=x_m(1). Counts distinct e-words by length.
#include <stdio.h>
#include <stdlib.h>
#define TM 64
static unsigned char rt[TM][TM]; static int ph, M; static unsigned char *seen[40];
static inline int c(int t){ return (t+ph)&1; }
static inline int add(int m,int b){ rt[0][m]=b;
  for(int t=1;t<=m;t++){ int j=m-t; int l= j>=1? rt[t-1][j-1] : c(t-1); rt[t][j]= l ^ (rt[t-1][j] | rt[t-1][j+1]); }
  return rt[m][0]; }
static void dfs(int m, unsigned w, int n){ // n = number of e bits so far
  if(m>=M) return;
  for(int b=0;b<2;b++){ int y=add(m,b); unsigned w2=w; int n2=n;
    if(!c(m)){ w2=w|((unsigned)y<<n); n2=n+1; seen[n2][w2]=1; }
    dfs(m+1,w2,n2); }
}
int main(int argc,char**argv){ M=atoi(argv[1]); ph=atoi(argv[2]);
  for(int n=0;n<40&&n<=M/2+1;n++) seen[n]=calloc(1u<<n,1);
  dfs(0,0,0);
  for(int n=1;n<=M/2+1;n++){ long k=0; for(unsigned w=0;w<(1u<<n);w++) k+=seen[n][w]; if(k) printf("ph=%d len=%d words=%ld\n",ph,n,k); }
  if(argc>3){ int n=atoi(argv[3]); for(unsigned w=0;w<(1u<<n);w++) if(seen[n][w]){ for(int i=0;i<n;i++) putchar('0'+((w>>i)&1)); putchar('\n'); } }
}
