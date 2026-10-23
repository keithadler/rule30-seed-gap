// Same bitsliced search as gapscan.c, generalized to rules f(l,c,r) = l XOR g(c,r) with g(0,0)=0.  RULEG = g as 4 bits: bit0 g(0,0), bit1 g(0,1), bit2 g(1,0), bit3 g(1,1).  RULEG=14 is Rule 30 (g = c OR r); 6 is XOR (Rule 150); 8 is AND (Rule 120)
// Copyright 2026 Keith Adler, Apache-2.0.  Written with Claude (Anthropic) assisting.  Compile: cc -O3 -DMAXN=400 -o gapscan_rules src/gapscan_rules.c
// Bitsliced forced-left-half search: 64 right halves per machine word (one per lane). Rule 30 is bitwise, so every step handles all 64 at once.
//   forced64 H r tr lo hi   : horizon histogram over right halves R in [lo,hi) (lo multiple of 64), trace tr 0..3. Prints best horizon and its count.
//   forced64 T w tr N start maxp lo hi : right halves whose forced left half has an eventually periodic tail (depths start..N, period <= maxp); prints "R period".
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t W;
static W G0,G1,G2,G3;
static inline W GG(W c,W r){ return (G0&~c&~r)|(G1&~c&r)|(G2&c&~r)|(G3&c&r); }
#ifndef MAXN
#define MAXN 1700
#endif
#define MAXW 40
static const W LANE[6]={0xAAAAAAAAAAAAAAAAULL,0xCCCCCCCCCCCCCCCCULL,0xF0F0F0F0F0F0F0F0ULL,0xFF00FF00FF00FF00ULL,0xFFFF0000FFFF0000ULL,0xFFFFFFFF00000000ULL};
static unsigned char TR[MAXN+8];
static inline W trace_mask(int tr,int t){ if(tr==9) return TR[t]?~0ULL:0ULL; int b; switch(tr){case 0:b=0;break;case 1:b=1;break;case 2:b=t&1;break;default:b=(t&1)^1;} return b?~0ULL:0ULL; }
// Rolling version: O(N) memory per call. D_k[t] = cell (t, t-k); only the last two diagonals, the trace and column 1 over time are kept.
static W Dbuf[3][MAXN+4], COL1[MAXN+4], ROW[2*MAXN+MAXW+16];
static void forced(int tr,int w,uint64_t R0,int N,W*L){
  int Wd=w+N+3;
  for(int p=1;p<=Wd;p++){ W v=0; if(p<=w){ int b=p-1; v=(b<6)? LANE[b] : (((R0>>b)&1)?~0ULL:0ULL); } ROW[p]=v; }
  ROW[Wd+1]=0;
  for(int t=0;t<=N;t++){
    COL1[t]=ROW[1];
    if(t==N) break;
    W prev=trace_mask(tr,t);                       // old x_0^t
    int lim=Wd-1; for(int p=1;p<=lim;p++){ W cur=ROW[p]; ROW[p]=prev^GG(cur,ROW[p+1]); prev=cur; }
  }
  W *Dm2=Dbuf[0],*Dm1=Dbuf[1],*D=Dbuf[2];
  Dm1[0]=trace_mask(tr,0);                          // diagonal 0 = the single cell (0,0)
  for(int k=1;k<=N;k++){
    D[0]=0;
    for(int t=1;t<k;t++) D[t]=D[t-1]^GG(Dm1[t-1],Dm2[t-1]);
    W pred=D[k-1]^GG(trace_mask(tr,k-1),COL1[k-1]);
    W flip=pred^trace_mask(tr,k);
    if(flip) for(int t=0;t<k;t++) D[t]^=flip;
    L[k]=flip; D[k]=trace_mask(tr,k);
    W *tmp=Dm2; Dm2=Dm1; Dm1=D; D=tmp;
  }
}
int main(int argc,char**argv){
  static W L[MAXN+2];
  { const char*g=getenv("RULEG"); int v=g?atoi(g):14; G0=(v&1)?~0ULL:0; G1=(v&2)?~0ULL:0; G2=(v&4)?~0ULL:0; G3=(v&8)?~0ULL:0; }
  if(getenv("TRACE")){ const char*t=getenv("TRACE"); for(int i=0;t[i]&&i<MAXN+4;i++) TR[i]=t[i]-48; }
  if(!strcmp(argv[1],"H")){
    int r=atoi(argv[2]),tr=atoi(argv[3]); uint64_t lo=strtoull(argv[4],0,10),hi=strtoull(argv[5],0,10); int N=2*r+40;
    static long hist[MAXN+4]; memset(hist,0,sizeof hist);
    for(uint64_t R0=lo;R0<hi;R0+=64){
      forced(tr,r,R0,N,L);
      W nz = (trace_mask(tr,0)); for(int p=1;p<=r;p++){ W v=0; int b=p-1; v=(b<6)?LANE[b]:(((R0>>b)&1)?~0ULL:0ULL); nz|=v; }
      for(int k=1;k<=r;k++) nz|=L[k];
      W done=0;
      for(int k=r+1;k<=N;k++){ W nb=L[k]&~done&nz; if(nb){ hist[k]+=__builtin_popcountll(nb); done|=nb; } }
      W rest=nz&~done; if(rest) hist[N+1]+=__builtin_popcountll(rest);
    }
    int best=0; for(int k=N+1;k>=0;k--) if(hist[k]){best=k;break;}
    printf("r=%d tr=%d R=[%llu,%llu) best=%d count=%ld\n",r,tr,(unsigned long long)lo,(unsigned long long)hi,best,hist[best]);
    return 0; }
  if(!strcmp(argv[1],"G")){ // G r tr lo hi : histogram of the gap = (depth of first forced one beyond r) - r, over nonzero seeds of radius <= r
    int r=atoi(argv[2]),tr=atoi(argv[3]); uint64_t lo=strtoull(argv[4],0,10),hi=strtoull(argv[5],0,10); int N=2*r+60; if(N>MAXN)N=MAXN;
    static long gh[MAXN+4]; 
    for(uint64_t R0=lo;R0<hi;R0+=64){ forced(tr,r,R0,N,L);
      W nz=trace_mask(tr,0); for(int p=1;p<=r;p++){ W v=0; int b=p-1; v=(b<6)?LANE[b]:(((R0>>b)&1)?~0ULL:0ULL); nz|=v; } for(int k=1;k<=r;k++) nz|=L[k];
      W done=0; for(int k=r+1;k<=N;k++){ W nb=L[k]&~done&nz; if(nb){ gh[k-r]+=__builtin_popcountll(nb); done|=nb; } } W rest=nz&~done; if(rest) gh[N-r+1]+=__builtin_popcountll(rest); }
    for(int g=1;g<=N;g++) if(gh[g]) printf("%d %ld\n",g,gh[g]); return 0; }
  if(!strcmp(argv[1],"Z")){ // Z w tr N lo hi : zero-run statistics; buckets of start depth: [1,50),[50,100),[100,200),[200,400),[400,800),[800,N]
    int w=atoi(argv[2]),tr=atoi(argv[3]),N=atoi(argv[4]); uint64_t lo=strtoull(argv[5],0,10),hi=strtoull(argv[6],0,10);
    static long hist[6][80]; static long ones[6][80]; int bnd[7]={1,50,100,200,400,800,N+1};
    for(uint64_t R0=lo;R0<hi;R0+=64){ forced(tr,w,R0,N,L);
      for(int lane=0;lane<64;lane++){ int run=0,rs=0,cur=-1; 
        for(int k=1;k<=N;k++){ int b=(L[k]>>lane)&1; int want=0; 
          if(cur==-1||b!=cur){ if(cur!=-1){ int bk=0; while(bk<5&&rs>=bnd[bk+1]) bk++; int r=run>79?79:run; if(cur==0) hist[bk][r]++; else ones[bk][r]++; } cur=b; run=1; rs=k; }
          else run++; (void)want; } } }
    for(int bk=0;bk<6;bk++){ int mx=0; for(int r=0;r<80;r++) if(hist[bk][r]) mx=r; printf("B %d maxzero %d zerohist",bk,mx); for(int r=1;r<=mx;r++) printf(" %ld",hist[bk][r]); printf(" | onehist"); for(int r=1;r<=20;r++) printf(" %ld",ones[bk][r]); printf("\n"); }
    return 0; }
  if(!strcmp(argv[1],"T")){
    int w=atoi(argv[2]),tr=atoi(argv[3]),N=atoi(argv[4]),start=atoi(argv[5]),maxp=atoi(argv[6]); uint64_t lo=strtoull(argv[7],0,10),hi=strtoull(argv[8],0,10);
    for(uint64_t R0=lo;R0<hi;R0+=64){
      forced(tr,w,R0,N,L);
      W found=0;
      for(int p=1;p<=maxp&&start+p<N;p++){
        W ok=~found; for(int k=start;k+p<=N&&ok;k++) ok&=~(L[k]^L[k+p]);
        if(ok){ for(int lane=0;lane<64;lane++) if((ok>>lane)&1) printf("%llu %d\n",(unsigned long long)(R0+lane),p); found|=ok; }
        if(found==~0ULL) break; }
    }
    return 0; }
}
