// One-sided period-2 problem for Rule 30.
// Left half L(1..A) = x_0(-1..-A), boundary column 0 fixed to c(t) = (t+ph)&1.
// The left half-plane evolves on its own. Necessary conditions for a two-sided seed:
//  (R1) at times with c(t)=1: x_t(-1)=1
//  (R2) at times with c(t)=0 ("free"): x_t(-1)=0 => x_{t+2}(-1)=1   (from the right side: y(t)=1 => y(t+2)=0)
// DFS over L prefixes; a prefix of length m+1 decides the check at time m.
// For each valid prefix, continue with zeros and record the first failing time tf.
// Output per exact width m: max tf+1 (comparable to SAT "first UNSAT T"), and number of valid prefixes.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define TM 4000
static unsigned char *tri[TM]; static int ph, useR2, Amax;
static long long cnt[TM]; static int best[TM]; static long long nbest[TM];
static unsigned char Lb[TM]; static long long hist[400][200]; static unsigned char bestL[TM][400];
static inline int c(int t){ return (t+ph)&1; }
// add bit b as L(m+1); returns x_m(-1)
static inline int add(int m, int b){
  tri[0][m]=b;
  for(int t=1;t<=m;t++){ int j=m-t; int l=tri[t-1][j+1], ce=tri[t-1][j], r= j>=1? tri[t-1][j-1] : c(t-1);
    tri[t][j]= l ^ (ce|r); }
  return tri[m][0];
}
static inline int ok(int m){ // check at time m, after add(m,.)
  int v=tri[m][0];
  if(c(m)) return v==1;
  if(useR2 && m>=2 && v==0 && tri[m-2][0]==0) return 0;
  return 1;
}
static void dfs(int m){
  cnt[m]++;
  if(m==0 || Lb[m-1]){ int mm=m; while(mm<TM-1){ add(mm,0); if(!ok(mm)) break; mm++; }
    int T=mm+1; if(m<400 && T-m<200) hist[m][T-m]++; if(T>best[m]){best[m]=T;nbest[m]=1; memcpy(bestL[m],Lb,m);} else if(T==best[m]) nbest[m]++; }
  if(m>=Amax) return;
  for(int b=0;b<2;b++){ add(m,b); if(ok(m)){ Lb[m]=b; dfs(m+1);} }
}
int main(int argc,char**argv){ Amax=atoi(argv[1]); ph=atoi(argv[2]); useR2=atoi(argv[3]);
  for(int t=0;t<TM;t++) tri[t]=calloc(TM,1);
  dfs(0);
  int run=0; for(int m=0;m<=Amax;m++){ if(best[m]>run) run=best[m];
    printf("A=%d ph=%d valid=%lld T_exact=%d T=%d n=%lld L=",m,ph,cnt[m],best[m],run,nbest[m]); for(int i=0;i<m;i++)putchar('0'+bestL[m][i]); putchar('\n'); }
  for(int m=Amax-1;m<=Amax;m++){ printf("HIST A=%d:",m); for(int g=0;g<200;g++) if(hist[m][g]) printf(" %d:%lld",g,hist[m][g]); printf("\n"); }
}
