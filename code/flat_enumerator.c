// flats.c -- independent exhaustive checker (written from scratch; shares no code with the SAT encoders).
//
// Variables: column j (weight 2^j), operand i  ->  bit j*k+i of the point x.   N = k*ncol <= 16.
// K_j(x) = carry (integer) into column j:  K_0 = 0, K_{j+1} = floor((K_j + popcount(column j))/2).
// SUM(x) = (sum of the k operand words) mod 2^ncol, computed by plain integer addition; build() asserts
//          bit_j(SUM) == (K_j mod 2) xor parity(column j), i.e. the heap model equals real addition.
//
// A flat through p is p + D, D a linear subspace.  Every subspace has a unique reduced echelon basis:
// pivot set P; the row with pivot v is  (1<<v) | (subset of the non-pivot positions below v).
// rec() enumerates all of them (rows in increasing pivot order).  With pruning on, a partial basis is
// abandoned as soon as the target is not affine on p + span(partial basis); this is sound because
// affine on p+D implies affine on p+D' for every D' <= D.
//
// modes:
//   mc  k n c [p|all] [noprune]  count flats of codim c through p (default all-ones) on which all n bits of
//                             x_1+..+x_k mod 2^n are affine, in ALL k*n variables (no projection argument).
//   lem k m                   all flats through all-ones of the m-column heap (all dims, no pruning):
//                             check the carry-rank lemma (Lemma 10.2), (F) and the flat bound on each.
//   lay k m                   all flats through all-ones with P_j (C_1..C_j affine), built column by column
//                             as (U_j, F, y_0); checks Lemma 10.2, (F) and the flat bound on each; min codim per level.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
typedef uint32_t u32; typedef uint64_t u64;

static int k, ncol, N;
static uint8_t *Kt[9];      // Kt[j][x], j = 0..ncol
static uint16_t *SUM;
static int M[10];

static void build(void){
  u32 sz = 1u<<N;
  for(int j=0;j<=ncol;j++) Kt[j]=malloc(sz);
  SUM=malloc(sz*sizeof(uint16_t));
  for(u32 x=0;x<sz;x++){
    int K=0; Kt[0][x]=0;
    for(int j=0;j<ncol;j++){ K=(K+__builtin_popcount((x>>(j*k))&((1u<<k)-1)))>>1; Kt[j+1][x]=(uint8_t)K; }
    u32 s=0;
    for(int i=0;i<k;i++){ u32 w=0; for(int j=0;j<ncol;j++) w|=((x>>(j*k+i))&1u)<<j; s+=w; }
    SUM[x]=(uint16_t)(s&((1u<<ncol)-1));
    for(int j=0;j<ncol;j++){
      int par=__builtin_popcount((x>>(j*k))&((1u<<k)-1))&1;
      if((((SUM[x]>>j)&1) ^ (Kt[j][x]&1) ^ par)!=0){ fprintf(stderr,"heap model mismatch\n"); exit(2);} }
  }
  M[0]=0; for(int j=0;j<ncol+1;j++) M[j+1]=(M[j]+k)/2;
}

// ---------- generic echelon enumeration ----------
static u32 span[1u<<16];
static u32 basis[16];
static int piv[16];
static u32 P0;                 // base point
static int prune;
static u64 leaves, nodes;
static void (*leafcb)(int d);

static inline int ok_add(int r, u32 b){   // SUM affine on P0+span(basis[0..r-1], b), given affine on the first r
  uint16_t dl = SUM[P0^b]^SUM[P0];
  u32 n=1u<<r;
  for(u32 s=1;s<n;s++){ u32 x=P0^span[s]; if((SUM[x^b]^SUM[x])!=dl) return 0; }
  return 1;
}
static void rec(int r,int d,u32 Pm){
  if(r==d){ leaves++; if(leafcb) leafcb(d); return; }
  int pv=piv[r]; u32 fm=((1u<<pv)-1)&~Pm, sub=0;
  do{
    u32 b=(1u<<pv)|sub; nodes++;
    if(!prune || ok_add(r,b)){
      basis[r]=b; u32 n=1u<<r; for(u32 s=0;s<n;s++) span[n+s]=span[s]^b;
      rec(r+1,d,Pm);
    }
    sub=(sub-fm)&fm;
  }while(sub);
}
static void enum_dim(int d){   // all subspaces of F_2^N of dimension d
  span[0]=0;
  if(d==0){ leaves++; if(leafcb) leafcb(0); return; }
  for(u32 Pm=0; Pm<(1u<<N); Pm++){
    if(__builtin_popcount(Pm)!=d) continue;
    int r=0; for(int v=0;v<N;v++) if((Pm>>v)&1) piv[r++]=v;
    rec(0,d,Pm);
  }
}
static double gbin(int n,int d){ double x=1; for(int i=0;i<d;i++) x*= (ldexp(1.0,n-i)-1)/(ldexp(1.0,i+1)-1); return x; }

// ---------- helpers on a flat  p + span(basis[0..d-1]) with span[] filled in the standard order ----------
static int rank_masked(const u32*b,int d,u32 mask){
  u32 t[16]; int r=0;
  for(int i=0;i<d;i++){ u32 v=b[i]&mask;
    for(int q=0;q<r;q++){ u32 hb=1u<<(31-__builtin_clz(t[q])); if(v&hb) v^=t[q]; }
    if(v){ u32 hb=1u<<(31-__builtin_clz(v));
      for(int q=0;q<r;q++) if(t[q]&hb) t[q]^=v;
      t[r++]=v; }
  }
  return r;
}
static int affine_bit(const uint8_t*T,u32 p,int d){   // (T[x]&1) affine on p+span ?
  for(int i=0;i<d;i++){ u32 b=span[1u<<i]; int dl=(T[p^b]^T[p])&1; u32 n=1u<<i;
    for(u32 s=1;s<n;s++){ u32 x=p^span[s]; if(((T[x^b]^T[x])&1)!=dl) return 0; } }
  return 1;
}
static int inv_dim(const uint8_t*T,u32 p,int d){     // dim { v in span : T(x+v)=T(x) for all x in flat }
  u32 n=1u<<d, c=0;
  for(u32 v=0;v<n;v++){ u32 vv=span[v]; int good=1;
    for(u32 s=0;s<n;s++){ u32 x=p^span[s]; if(T[x^vv]!=T[x]){good=0;break;} }
    c+=good; }
  int e=0; while((1u<<e)<c) e++;
  if((1u<<e)!=c){ fprintf(stderr,"Inv not a subspace?!\n"); exit(2); }
  return e;
}

// ---------- statistics for the lemma checks ----------
static u64 hypL4[9],violL4[9],tightL4[9], hypC5[10],violC5[10],tightC5[10], hypF[9],violF[9],tightF[9], hypT,violT;
static u64 Fd2[9], Fd2viol[9];
static int minco; static u64 mincnt;
static u64 codhist[10][17];

static void check_flat(int d,u32 ONE,int m){
  // m = number of columns present in the flat (variables 0..m*k-1)
  int dimU[10], aff[10], r[10];
  for(int j=0;j<=m;j++){
    u32 mask = (1u<<(j*k))-1;
    dimU[j]=rank_masked(basis,d,mask);
    aff[j]= (j==0)?1:affine_bit(Kt[j],ONE,d);
    r[j]= d - inv_dim(Kt[j],ONE,d);        // = dim U_j - dim Inv(K_j on U_j)  (kernel of projection lies in Inv)
  }
  if(dimU[m]!=d || r[0]!=0){ fprintf(stderr,"internal\n"); exit(2); }
  int Pj[11]; Pj[0]=1; for(int j=1;j<=m;j++) Pj[j]=Pj[j-1]&&aff[j];
  for(int j=0;j<m;j++){
    int dj=dimU[j+1]-dimU[j], odd=(M[j]+k)&1;
    if(aff[j]){ hypL4[j]++; int lhs=r[j+1], rhs=r[j]+dj-odd; if(lhs<rhs) violL4[j]++; if(lhs==rhs) tightL4[j]++; }
    if(Pj[j+1]){ hypF[j]++; int mx=M[j]-r[j]; if(mx<0) mx=0; int rhs=k-M[j+1]+mx;
      if(dj>rhs) violF[j]++; if(dj==rhs) tightF[j]++;
      if(dj==2 && j>=1){ Fd2[j]++; if(r[j]>M[j]-1) Fd2viol[j]++; } }
  }
  for(int j=1;j<=m;j++){
    if(Pj[j-1]){ hypC5[j]++; int S=0; for(int i=1;i<=j;i++) S+=M[i];
      int lhs=j*k-dimU[j]+r[j], rhs=S+M[j]; if(lhs<rhs) violC5[j]++; if(lhs==rhs) tightC5[j]++; }
  }
  if(Pj[m]){ hypT++; int S=0; for(int i=1;i<=m;i++) S+=M[i]; int co=m*k-d;
    if(co<S) violT++;
    if(co<minco){minco=co;mincnt=0;} if(co==minco) mincnt++; codhist[m][co]++; }
}
static u64 aff_leaves;
static void mc_leaf(int d){   // unpruned cross-check: full affinity test of every output bit at the leaf
  for(int i=0;i<d;i++){ u32 b=span[1u<<i]; uint16_t dl=SUM[P0^b]^SUM[P0]; u32 n=1u<<i;
    for(u32 s=1;s<n;s++){ u32 x=P0^span[s]; if((SUM[x^b]^SUM[x])!=dl) return; } }
  aff_leaves++;
}
static int g_m;
static void lem_leaf(int d){ check_flat(d,(1u<<N)-1,g_m); }

static void print_stats(int m){
  for(int j=0;j<m;j++) printf("  Lemma4 j=%d: hyp %llu viol %llu tight %llu\n",j,(unsigned long long)hypL4[j],(unsigned long long)violL4[j],(unsigned long long)tightL4[j]);
  for(int j=1;j<=m;j++) printf("  Cor5   j=%d: hyp %llu viol %llu tight %llu\n",j,(unsigned long long)hypC5[j],(unsigned long long)violC5[j],(unsigned long long)tightC5[j]);
  for(int j=0;j<m;j++) printf("  (F)    j=%d: hyp %llu viol %llu tight %llu | d_j=2 cases %llu, of which r_j>M_j-1: %llu\n",j,(unsigned long long)hypF[j],(unsigned long long)violF[j],(unsigned long long)tightF[j],(unsigned long long)Fd2[j],(unsigned long long)Fd2viol[j]);
  printf("  (T): flats with P_m %llu, with codim < sum M: %llu\n",(unsigned long long)hypT,(unsigned long long)violT);
}

// ---------- layered enumeration ----------
typedef struct { uint8_t d; u32 b[14]; } flat_t;
static flat_t *lev[10]; static u64 nlev[10], caplev[10];
static int store_level;
static u32 ONEj1; static int Lj; // extending by column Lj
static const flat_t *par; static u32 reps[64]; static int nreps;
static u64 lay_cnt[10];

static inline int ok_add_bit(const uint8_t*T,u32 p,int r,u32 b){
  int dl=(T[p^b]^T[p])&1; u32 n=1u<<r;
  for(u32 s=1;s<n;s++){ u32 x=p^span[s]; if(((T[x^b]^T[x])&1)!=dl) return 0; }
  return 1;
}
static void lay_emit(int d){
  int m=Lj+1;
  // independent full recheck: all of C_1..C_m affine on the new flat
  for(int j=1;j<=m;j++) if(!affine_bit(Kt[j],ONEj1,d)){ fprintf(stderr,"layer recheck failed\n"); exit(2); }
  lay_cnt[m]++;
  check_flat(d,ONEj1,m);
  if(store_level){
    if(nlev[m]==caplev[m]){ caplev[m]=caplev[m]?2*caplev[m]:1024; lev[m]=realloc(lev[m],caplev[m]*sizeof(flat_t)); if(!lev[m]){fprintf(stderr,"oom\n");exit(2);} }
    flat_t *f=&lev[m][nlev[m]++]; f->d=(uint8_t)d; memcpy(f->b,basis,sizeof(u32)*d);
  }
}
static void lay_rec(int i,int r){   // i = index of parent basis vector to lift, r = current number of basis vectors
  if(i==par->d){ lay_emit(r); return; }
  for(int q=0;q<nreps;q++){
    u32 b=par->b[i] | (reps[q]<<(Lj*k));
    if(ok_add_bit(Kt[Lj+1],ONEj1,r,b)){
      basis[r]=b; u32 n=1u<<r; for(u32 s=0;s<n;s++) span[n+s]=span[s]^b;
      lay_rec(i+1,r+1);
    }
  }
}
static void lay_extend(int j){      // from level j to level j+1
  Lj=j; ONEj1=(1u<<((j+1)*k))-1;
  for(u64 t=0;t<nlev[j];t++){
    par=&lev[j][t];
    // all subspaces F of F_2^k in echelon form
    for(u32 Pm=0;Pm<(1u<<k);Pm++){
      int fd=__builtin_popcount(Pm); int pv[8],c=0; for(int v=0;v<k;v++) if((Pm>>v)&1) pv[c++]=v;
      u32 fm[8]; for(int q=0;q<fd;q++) fm[q]=((1u<<pv[q])-1)&~Pm;
      u32 sub[8]; memset(sub,0,sizeof sub);
      for(;;){
        nreps=0; for(u32 y=0;y<(1u<<k);y++) if(!(y&Pm)) reps[nreps++]=y;   // representatives of F_2^k / F
        span[0]=0; int r=0, good=1;
        for(int q=0;q<fd && good;q++){ u32 b=((1u<<pv[q])|sub[q])<<(j*k);
          if(ok_add_bit(Kt[j+1],ONEj1,r,b)){ basis[r]=b; u32 n=1u<<r; for(u32 s=0;s<n;s++) span[n+s]=span[s]^b; r++; } else good=0; }
        if(good) lay_rec(0,r);
        int q=0; for(;q<fd;q++){ sub[q]=(sub[q]-fm[q])&fm[q]; if(sub[q]) break; }
        if(q==fd) break;
      }
    }
  }
}

int main(int argc,char**argv){
  if(argc<4){ fprintf(stderr,"usage: flats mc k n c [p|all] [noprune] | lem k m | lay k m\n"); return 1; }
  k=atoi(argv[2]); ncol=atoi(argv[3]); N=k*ncol;
  if(N>16 || ncol>8){ fprintf(stderr,"N too large\n"); return 1; }
  build();
  if(!strcmp(argv[1],"mc")){
    int c=atoi(argv[4]); int all=0; P0=(1u<<N)-1; prune=1;
    for(int a=5;a<argc;a++){ if(!strcmp(argv[a],"all")) all=1; else if(!strcmp(argv[a],"noprune")){ prune=0; leafcb=mc_leaf; } else P0=(u32)strtoul(argv[a],0,0); }
    if(!all){
      leaves=nodes=0; enum_dim(N-c);
      if(!prune) printf("  [unpruned run: affine flats found by leaf test = %llu]\n",(unsigned long long)aff_leaves);
      printf("mc k=%d n=%d N=%d codim=%d point=0x%x prune=%d: flats_counted=%llu nodes=%llu (all subspaces of that codim: %.0f)\n",
        k,ncol,N,c,P0,prune,(unsigned long long)leaves,(unsigned long long)nodes,gbin(N,N-c));
    } else {
      u64 pts_with=0, tot=0;
      for(u32 p=0;p<(1u<<N);p++){ P0=p; leaves=nodes=0; enum_dim(N-c); if(leaves) pts_with++; tot+=leaves; }
      printf("mc-all k=%d n=%d N=%d codim=%d: points having an affine flat of this codim: %llu of %u ; total (point,flat) pairs %llu\n",
        k,ncol,N,c,(unsigned long long)pts_with,1u<<N,(unsigned long long)tot);
    }
  } else if(!strcmp(argv[1],"lem")){
    prune=0; leafcb=lem_leaf; g_m=ncol; minco=99; leaves=0;
    double tot=0; for(int d=0;d<=N;d++){ enum_dim(d); tot+=gbin(N,d); }
    printf("lem k=%d m=%d N=%d: subspaces enumerated %llu (sum of Gaussian binomials %.0f)\n",k,ncol,N,(unsigned long long)leaves,tot);
    print_stats(ncol);
    int S=0; for(int i=1;i<=ncol;i++) S+=M[i];
    printf("  min codim of a flat through 1 with P_m: %d (count %llu); sum M = %d\n",minco,(unsigned long long)mincnt,S);
  } else if(!strcmp(argv[1],"lay")){
    lev[0]=calloc(1,sizeof(flat_t)); nlev[0]=1;
    for(int j=0;j<ncol;j++){
      store_level=(j+1<ncol); minco=99; mincnt=0;
      lay_extend(j);
      int S=0; for(int i=1;i<=j+1;i++) S+=M[i];
      printf("lay k=%d columns=%d: flats through 1 with P_%d: %llu ; min codim %d (count %llu) ; sum M = %d\n",k,j+1,j+1,(unsigned long long)lay_cnt[j+1],minco,(unsigned long long)mincnt,S);
      printf("   codim histogram:"); for(int c=0;c<=16;c++) if(codhist[j+1][c]) printf(" %d:%llu",c,(unsigned long long)codhist[j+1][c]); printf("\n");
      fflush(stdout);
    }
    printf(" cumulative lemma statistics over all levels (each flat checked as an m-column flat):\n");
    print_stats(ncol);
  }
  return 0;
}
