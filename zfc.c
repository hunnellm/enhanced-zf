/* zfc.c — zero forcing / PSD / loop forcing / enhanced zero forcing engine.
 *
 * Conventions match the Python reference zf.py:
 *  - loop rule: v forces u iff u is the unique unfilled vertex of N(v) ∪ ({v} if loop at v);
 *    the forcer v need NOT be filled.
 *  - standard rule: filled v forces its unique unfilled neighbor.
 *  - PSD rule: filled v with exactly one neighbor in some component of the unfilled subgraph.
 *  - Zhat(G) = max over 2^n loopings of Z(looped G).
 *
 * Modes (first argv):
 *   census    : per graph6 line: g6 n Zp Zhat Z kappa delta cut sep2
 *   cutcheck  : verify Zhat cut-vertex formula on all decompositions; print violations + stats
 *   sepcheck  : verify Zhat 2-separation formula; print violations + stats (+ Z-formula comparison)
 *   spread    : min/max of Zhat(G)-Zhat(G-v) over all v, all graphs
 *   single    : verbose report for one graph
 *   edgedel   : find graphs with Zhat(G-e) > Zhat(G) (monotonicity probe)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint32_t mask;
#define MAXN 20
static inline int pc(mask x){ return __builtin_popcount(x); }
static inline int lsb(mask x){ return __builtin_ctz(x); }

typedef struct { int n; mask adj[MAXN]; } Graph;

/* ---------- graph6 ---------- */
static int parse_g6(const char*s, Graph*g){
    int n = s[0]-63; if(n<0||n>MAXN) return -1;
    g->n=n; for(int i=0;i<n;i++) g->adj[i]=0;
    int idx=0; const char*p=s+1;
    int need = n*(n-1)/2;
    int bitbuf=0,bits=0;
    for(int j=1;j<n;j++) for(int i=0;i<j;i++){
        if(bits==0){ bitbuf=(*p++)-63; bits=6; }
        if((bitbuf>>(bits-1))&1){ g->adj[i]|=1u<<j; g->adj[j]|=1u<<i; }
        bits--; idx++;
    }
    (void)need; (void)idx;
    return 0;
}
static void print_g6(const Graph*g, char*out){
    int n=g->n; char*o=out; *o++=(char)(n+63);
    int bitbuf=0,bits=0;
    for(int j=1;j<n;j++) for(int i=0;i<j;i++){
        bitbuf=(bitbuf<<1)|((g->adj[i]>>j)&1); bits++;
        if(bits==6){ *o++=(char)(bitbuf+63); bitbuf=0;bits=0; }
    }
    if(bits){ bitbuf<<=(6-bits); *o++=(char)(bitbuf+63); }
    *o=0;
}

/* ---------- closures ---------- */
static mask closure_loop(const Graph*g, mask loops, mask filled){
    int n=g->n; mask N[MAXN];
    for(int v=0;v<n;v++) N[v]=g->adj[v] | (loops & (1u<<v));
    int changed=1;
    while(changed){ changed=0;
        for(int v=0;v<n;v++){
            mask m=N[v] & ~filled;
            if(m && !(m&(m-1))){ filled|=m; changed=1; }
        }
    }
    return filled;
}
static mask closure_std(const Graph*g, mask filled){
    int n=g->n; int changed=1;
    while(changed){ changed=0;
        for(int v=0;v<n;v++) if((filled>>v)&1){
            mask m=g->adj[v] & ~filled;
            if(m && !(m&(m-1))){ filled|=m; changed=1; }
        }
    }
    return filled;
}
static int ncomps_mask(const Graph*g, mask sub, mask*comps){
    int cnt=0; mask rem=sub;
    while(rem){
        mask comp = rem & (-(int32_t)rem) ;
        mask frontier=comp;
        while(frontier){
            mask newm=0, f=frontier;
            while(f){ int v=lsb(f); f&=f-1; newm |= g->adj[v] & sub & ~comp; }
            comp|=newm; frontier=newm;
        }
        if(comps) comps[cnt]=comp;
        cnt++;
        rem &= ~comp;
    }
    return cnt;
}
static mask closure_psd(const Graph*g, mask filled){
    int n=g->n; mask full=(1u<<n)-1;
    int changed=1;
    while(changed){ changed=0;
        mask unf = full & ~filled;
        if(!unf) break;
        mask comps[MAXN]; int nc=ncomps_mask(g,unf,comps);
        mask f=filled;
        while(f){ int v=lsb(f); f&=f-1;
            for(int c=0;c<nc;c++){
                mask m=g->adj[v]&comps[c];
                if(m && !(m&(m-1))){ filled|=m; changed=1; }
            }
        }
    }
    return filled;
}

/* iterate k-subsets of n bits via Gosper */
static inline mask gosper_next(mask v){
    mask c = v & (mask)(-(int32_t)v);
    mask r = v + c;
    return (((r ^ v) >> 2) / c) | r;
}

static int Z_std(const Graph*g){
    int n=g->n; if(n==0) return 0;
    mask full=(1u<<n)-1;
    for(int k=1;k<=n;k++){
        mask S=(1u<<k)-1;
        while(S<=full){
            if(closure_std(g,S)==full) return k;
            if(S==full) break;
            mask nx=gosper_next(S);
            if(nx>full) break;
            S=nx;
        }
    }
    return n;
}
static int Z_psd(const Graph*g){
    int n=g->n; if(n==0) return 0;
    mask full=(1u<<n)-1;
    for(int k=1;k<=n;k++){
        mask S=(1u<<k)-1;
        while(S<=full){
            if(closure_psd(g,S)==full) return k;
            if(S==full) break;
            mask nx=gosper_next(S);
            if(nx>full) break;
            S=nx;
        }
    }
    return n;
}

/* does some s-subset loop-force everything? uses a small MTF cache of successes */
#define CSZ 24
static int has_sset(const Graph*g, mask loops, int s, mask full, mask*cache, int*ncache){
    if(s>=g->n) return closure_loop(g,loops,full)==full;
    if(s==0) return closure_loop(g,loops,0)==full;
    for(int i=0;i<*ncache;i++){
        if(closure_loop(g,loops,cache[i])==full){
            mask t=cache[i];
            memmove(cache+1,cache,i*sizeof(mask));
            cache[0]=t;
            return 1;
        }
    }
    mask S=(1u<<s)-1;
    while(S<=full){
        if(closure_loop(g,loops,S)==full){
            if(*ncache<CSZ) (*ncache)++;
            memmove(cache+1,cache,((*ncache)-1)*sizeof(mask));
            cache[0]=S;
            return 1;
        }
        if(S==full) break;
        mask nx=gosper_next(S);
        if(nx>full) break;
        S=nx;
    }
    return 0;
}

/* exact Zhat.  Optionally returns a witness looping attaining the max. */
static int Zhat_exact(const Graph*g, int Zval, mask*witness){
    int n=g->n; if(n==0){ if(witness)*witness=0; return 0; }
    mask full=(1u<<n)-1;
    mask nl = 1u<<n;
    int s=Zval-1;
    mask lastwit=full; /* all-loops looping attains Z(G) frequently; also any looping attains >= s+1 once s-level fails */
    while(s>=0){
        mask cache[CSZ]; int ncache=0;
        int all_ok=1;
        /* try all-loops first (heuristically extremal), then everything else */
        for(mask t=0;t<nl;t++){
            mask loops = (t==0)? (nl-1) : (t==nl-1 ? 0 : t);
            if(!has_sset(g,loops,s,full,cache,&ncache)){
                all_ok=0; lastwit=loops; break;
            }
        }
        if(!all_ok){ if(witness)*witness=lastwit; return s+1; }
        s--;
    }
    if(witness)*witness=0;
    return 0;
}

/* connectivity utilities */
static int connected_mask(const Graph*g, mask sub){
    if(!sub) return 1;
    return ncomps_mask(g,sub,NULL)==1;
}
static int kappa(const Graph*g){
    int n=g->n; mask full=(1u<<n)-1;
    /* complete? */
    int comp=1;
    for(int v=0;v<n;v++) if(g->adj[v]!=(full&~(1u<<v))){comp=0;break;}
    if(comp) return n-1;
    for(int k=1;k<=n-2;k++){
        mask S=(1u<<k)-1;
        while(S<=full){
            if(!connected_mask(g, full&~S)) return k;
            if(S==full) break;
            mask nx=gosper_next(S);
            if(nx>full) break;
            S=nx;
        }
    }
    return n-1;
}
static int mindeg(const Graph*g){
    int d=g->n;
    for(int v=0;v<g->n;v++){ int dv=pc(g->adj[v]); if(dv<d)d=dv; }
    return d;
}
static int has_cutvertex(const Graph*g){
    mask full=(1u<<g->n)-1;
    for(int v=0;v<g->n;v++)
        if(!connected_mask(g, full&~(1u<<v))) return 1;
    return 0;
}
static int has_2sep(const Graph*g){ /* pair whose removal disconnects */
    mask full=(1u<<g->n)-1;
    for(int a=0;a<g->n;a++)for(int b=a+1;b<g->n;b++)
        if(!connected_mask(g, full&~((1u<<a)|(1u<<b)))) return 1;
    return 0;
}

/* induced subgraph on mask, relabeled */
static void induce(const Graph*g, mask sub, Graph*h, int*map /*old->new or NULL*/){
    int lbl[MAXN]; int m=0;
    for(int v=0;v<g->n;v++) if((sub>>v)&1){ lbl[v]=m++; }
    h->n=m;
    for(int v=0;v<m;v++) h->adj[v]=0;
    for(int v=0;v<g->n;v++) if((sub>>v)&1){
        mask a=g->adj[v]&sub;
        while(a){ int u=lsb(a); a&=a-1; h->adj[lbl[v]] |= 1u<<lbl[u]; }
        if(map) map[v]=lbl[v];
    }
}

/* memoized zhat on small graphs (pieces) */
#define HSZ (1u<<21)
typedef struct { uint64_t key; int val; } HEnt;
static HEnt *htab=NULL;
static uint64_t hash_graph(const Graph*g){
    uint64_t h=1469598103934665603ULL ^ g->n;
    for(int v=0;v<g->n;v++){ h^=g->adj[v]; h*=1099511628211ULL; }
    return h?h:1;
}
static int zhat_of(const Graph*g){
    if(g->n==0) return 0;
    uint64_t k=hash_graph(g);
    uint32_t i=(uint32_t)(k&(HSZ-1));
    while(htab[i].key){
        if(htab[i].key==k) return htab[i].val;
        i=(i+1)&(HSZ-1);
    }
    int z=Z_std(g);
    int v=Zhat_exact(g,z,NULL);
    htab[i].key=k; htab[i].val=v;
    return v;
}
static int z_of(const Graph*g){ if(g->n==0) return 0; return Z_std(g); }

/* -------- cut-vertex formula check on one graph.
 * returns number of decompositions checked; increments *viol on violations,
 * prints each violation. actcnt[0]: term Zh(G1)+Zh(G2) active; actcnt[1]: deletion term active (ties count both) */
static long cutcheck_graph(const Graph*g, const char*g6, long*viol, long acts[2]){
    int n=g->n; mask full=(1u<<n)-1;
    int zh_g=-1;
    long checked=0;
    for(int v=0;v<n;v++){
        mask rest = full & ~(1u<<v);
        mask comps[MAXN]; int nc=ncomps_mask(g,rest,comps);
        if(nc<2) continue;
        if(zh_g<0){ int z=Z_std(g); zh_g=Zhat_exact(g,z,NULL); }
        /* bipartitions of comps: subset containing comp 0, proper */
        for(mask t=0; t+1 < (1u<<(nc-1)); t++){ /* t over comps 1..nc-1; side A = comp0 + chosen; complement nonempty */
            mask A=comps[0], B=0;
            for(int c=1;c<nc;c++){ if((t>>(c-1))&1) A|=comps[c]; else B|=comps[c]; }
            if(!B) continue;
            Graph g1,g2,g1v,g2v;
            induce(g,A|(1u<<v),&g1,NULL);
            induce(g,B|(1u<<v),&g2,NULL);
            induce(g,A,&g1v,NULL);
            induce(g,B,&g2v,NULL);
            int t1=zhat_of(&g1)+zhat_of(&g2);
            int t2=zhat_of(&g1v)+zhat_of(&g2v);
            int rhs=(t1>t2?t1:t2)-1;
            checked++;
            if(t1>=t2) acts[0]++;
            if(t2>=t1) acts[1]++;
            if(rhs!=zh_g){
                printf("CUTVIOL %s v=%d zhat=%d rhs=%d t1=%d t2=%d\n",g6,v,zh_g,rhs,t1,t2);
                (*viol)++;
            }
        }
    }
    return checked;
}

/* identify r1,r2 in a piece: r1<r2 as labels within piece; drop loop if adjacent */
static void identify(const Graph*g, int r1, int r2, Graph*h){
    int n=g->n;
    /* new graph on n-1 vertices: delete r2, merge into r1 */
    int lbl[MAXN]; int m=0;
    for(int v=0;v<n;v++) if(v!=r2) lbl[v]=m++;
    h->n=n-1;
    for(int v=0;v<h->n;v++) h->adj[v]=0;
    for(int v=0;v<n;v++){
        if(v==r2) continue;
        mask a=g->adj[v];
        while(a){ int u=lsb(a); a&=a-1;
            int uu = (u==r2)? r1 : u;
            if(uu==v) continue; /* drop loop from identification */
            h->adj[lbl[v]] |= 1u<<lbl[uu];
            h->adj[lbl[uu]] |= 1u<<lbl[v];
        }
    }
}

/* 2-separation check; returns #separations checked.
 * For each separation computes the six Zhat terms; compares max-2 with Zhat(G).
 * Also computes the six-term formula with plain Z of pieces (RHSZ) and records whether Z(G)>RHSZ.
 * acts[i] counts term i being (one of the) maximizers in the Zhat formula.
 * Aggregates per graph: sets *anyZviol if some separation has Z(G) > RHSZ(sep); *allZviol if all have. */
static long sepcheck_graph(const Graph*g, const char*g6, long*viol, long acts[6],
                           int zh_g, int z_g, int*anyZviol, int*allZviol){
    int n=g->n; mask full=(1u<<n)-1;
    long checked=0;
    *anyZviol=0; *allZviol=1;
    int found_any=0;
    for(int a=0;a<n;a++)for(int b=a+1;b<n;b++){
        mask R=(1u<<a)|(1u<<b);
        mask rest=full&~R;
        if(!rest) continue;
        mask comps[MAXN]; int nc=ncomps_mask(g,rest,comps);
        if(nc<2) continue;
        int edgeR = (g->adj[a]>>b)&1;
        for(mask t=0; t+1 < (1u<<(nc-1)); t++){
            mask A=comps[0], B=0;
            for(int c=1;c<nc;c++){ if((t>>(c-1))&1) A|=comps[c]; else B|=comps[c]; }
            if(!B) continue;
            for(int eass=0; eass < (edgeR?2:1); eass++){
                /* eass=0: r1r2 edge (if any) in G1; eass=1: in G2 */
                Graph G1,G2;
                int map1[MAXN],map2[MAXN];
                induce(g,A|R,&G1,map1);
                induce(g,B|R,&G2,map2);
                int a1=map1[a],b1=map1[b],a2=map2[a],b2=map2[b];
                if(edgeR){
                    if(eass==0){ G2.adj[a2]&=~(1u<<b2); G2.adj[b2]&=~(1u<<a2); }
                    else       { G1.adj[a1]&=~(1u<<b1); G1.adj[b1]&=~(1u<<a1); }
                }
                Graph H1=G1,H2=G2;
                H1.adj[a1]|=1u<<b1; H1.adj[b1]|=1u<<a1;
                H2.adj[a2]|=1u<<b2; H2.adj[b2]|=1u<<a2;
                Graph Gb1,Gb2;
                identify(&G1,a1,b1,&Gb1);
                identify(&G2,a2,b2,&Gb2);
                Graph G1r1,G2r1,G1r2,G2r2,G1R,G2R;
                induce(g,(A|R)&~(1u<<a),&G1r1,NULL); if(edgeR&&eass==1){/*edge absent already in induced? induced keeps edge; but edge involves a which is deleted: fine*/}
                induce(g,(B|R)&~(1u<<a),&G2r1,NULL);
                induce(g,(A|R)&~(1u<<b),&G1r2,NULL);
                induce(g,(B|R)&~(1u<<b),&G2r2,NULL);
                induce(g,A,&G1R,NULL);
                induce(g,B,&G2R,NULL);
                /* NOTE: deletion pieces G_i - r contain the r1r2 edge only if it exists... it involves a deleted vertex, so no issue.
                 * But careful: G1 - r1 should be (G1 as built, incl. edge assignment) minus r1.  Edge r1r2 involves r1, so
                 * assignment doesn't matter for deletion terms.  Induced versions are correct. */
                int T[6];
                T[0]=zhat_of(&G1)+zhat_of(&G2);
                T[1]=zhat_of(&H1)+zhat_of(&H2);
                T[2]=zhat_of(&Gb1)+zhat_of(&Gb2);
                T[3]=zhat_of(&G1r1)+zhat_of(&G2r1);
                T[4]=zhat_of(&G1r2)+zhat_of(&G2r2);
                T[5]=zhat_of(&G1R)+zhat_of(&G2R);
                int mx=T[0]; for(int i=1;i<6;i++) if(T[i]>mx)mx=T[i];
                int rhs=mx-2;
                checked++; found_any=1;
                for(int i=0;i<6;i++) if(T[i]==mx) acts[i]++;
                if(rhs!=zh_g){
                    (*viol)++;
                    if(zh_g<rhs){ printf("SEPBELOW %s R={%d,%d} eass=%d zhat=%d rhs=%d T=[%d,%d,%d,%d,%d,%d]\n",
                        g6,a,b,eass,zh_g,rhs,T[0],T[1],T[2],T[3],T[4],T[5]); }
                }
                /* Z-version of the formula */
                int TZ[6];
                TZ[0]=z_of(&G1)+z_of(&G2);
                TZ[1]=z_of(&H1)+z_of(&H2);
                TZ[2]=z_of(&Gb1)+z_of(&Gb2);
                TZ[3]=z_of(&G1r1)+z_of(&G2r1);
                TZ[4]=z_of(&G1r2)+z_of(&G2r2);
                TZ[5]=z_of(&G1R)+z_of(&G2R);
                int mz=TZ[0]; for(int i=1;i<6;i++) if(TZ[i]>mz)mz=TZ[i];
                int rhsZ=mz-2;
                if(z_g>rhsZ) *anyZviol=1; else *allZviol=0;
            }
        }
    }
    if(!found_any){ *allZviol=0; }
    return checked;
}

int main(int argc,char**argv){
    if(argc<2){ fprintf(stderr,"mode?\n"); return 1; }
    const char*mode=argv[1];
    htab=calloc(HSZ,sizeof(HEnt));
    char line[256];
    if(!strcmp(mode,"census")){
        long tot=0, zpltz=0, gap=0, zplt_nogap=0;
        while(fgets(line,sizeof line,stdin)){
            line[strcspn(line,"\r\n")]=0; if(!line[0])continue;
            Graph g; if(parse_g6(line,&g)) continue;
            int z=Z_std(&g);
            int zp=Z_psd(&g);
            int zh;
            if(zp==z) zh=z; else zh=Zhat_exact(&g,z,NULL);
            int kap=kappa(&g), dl=mindeg(&g);
            int cut=has_cutvertex(&g), s2=has_2sep(&g);
            tot++;
            if(zp<z) zpltz++;
            if(zh<z){ gap++; printf("GAP %s n=%d Zp=%d Zhat=%d Z=%d kappa=%d delta=%d cut=%d sep2=%d\n",line,g.n,zp,zh,z,kap,dl,cut,s2); }
            else if(zp<z) zplt_nogap++;
            if(!(zp<=zh && zh<=z)) printf("SANDWICHFAIL %s %d %d %d\n",line,zp,zh,z);
            if(argc>2 && !strcmp(argv[2],"full"))
                printf("ROW %s %d %d %d %d %d %d %d %d\n",line,g.n,zp,zh,z,kap,dl,cut,s2);
        }
        fprintf(stderr,"total=%ld Zp<Z=%ld gap=%ld  (Zp<Z but Zhat=Z)=%ld\n",tot,zpltz,gap,zplt_nogap);
    } else if(!strcmp(mode,"cutcheck")){
        long viol=0, checked=0, graphs=0; long acts[2]={0,0};
        while(fgets(line,sizeof line,stdin)){
            line[strcspn(line,"\r\n")]=0; if(!line[0])continue;
            Graph g; if(parse_g6(line,&g)) continue;
            if(!has_cutvertex(&g)) continue;
            graphs++;
            checked+=cutcheck_graph(&g,line,&viol,acts);
        }
        fprintf(stderr,"cutcheck: graphs=%ld decomps=%ld violations=%ld act(main)=%ld act(del)=%ld\n",graphs,checked,viol,acts[0],acts[1]);
    } else if(!strcmp(mode,"sepcheck")){
        long viol=0, checked=0, graphs=0; long acts[6]={0,0,0,0,0,0};
        long gap_any=0,gap_all=0,gap_tot=0,nogap_any=0,nogap_tot=0;
        while(fgets(line,sizeof line,stdin)){
            line[strcspn(line,"\r\n")]=0; if(!line[0])continue;
            Graph g; if(parse_g6(line,&g)) continue;
            if(!has_2sep(&g)) continue;
            graphs++;
            int z=Z_std(&g);
            int zp=Z_psd(&g);
            int zh = (zp==z)? z : Zhat_exact(&g,z,NULL);
            int anyv,allv;
            checked+=sepcheck_graph(&g,line,&viol,acts,zh,z,&anyv,&allv);
            if(zh<z){ gap_tot++; if(anyv)gap_any++; if(allv)gap_all++; }
            else { nogap_tot++; if(anyv)nogap_any++; }
        }
        fprintf(stderr,"sepcheck: graphs=%ld seps=%ld violations=%ld\n",graphs,checked,viol);
        fprintf(stderr,"acts: G=%ld H=%ld Gbar=%ld -r1=%ld -r2=%ld -R=%ld\n",acts[0],acts[1],acts[2],acts[3],acts[4],acts[5]);
        fprintf(stderr,"Zhyp: gap graphs=%ld (anyZviol=%ld allZviol=%ld); nogap graphs=%ld (anyZviol=%ld)\n",
            gap_tot,gap_any,gap_all,nogap_tot,nogap_any);
    } else if(!strcmp(mode,"spread")){
        int mn=99,mx=-99; long bad=0, cnt=0;
        while(fgets(line,sizeof line,stdin)){
            line[strcspn(line,"\r\n")]=0; if(!line[0])continue;
            Graph g; if(parse_g6(line,&g)) continue;
            int zh=zhat_of(&g);
            mask full=(1u<<g.n)-1;
            for(int v=0;v<g.n;v++){
                Graph h; induce(&g,full&~(1u<<v),&h,NULL);
                int zhv=zhat_of(&h);
                int sp=zh-zhv;
                cnt++;
                if(sp<mn)mn=sp; if(sp>mx)mx=sp;
                if(sp<-1||sp>1){ bad++; printf("SPREADBAD %s v=%d zh=%d zh-v=%d\n",line,v,zh,zhv); }
            }
        }
        fprintf(stderr,"spread: pairs=%ld min=%d max=%d outside[-1,1]=%ld\n",cnt,mn,mx,bad);
    } else if(!strcmp(mode,"edgedel")){
        long found=0,cnt=0;
        while(fgets(line,sizeof line,stdin)){
            line[strcspn(line,"\r\n")]=0; if(!line[0])continue;
            Graph g; if(parse_g6(line,&g)) continue;
            int zh=zhat_of(&g);
            for(int a=0;a<g.n;a++)for(int b=a+1;b<g.n;b++) if((g.adj[a]>>b)&1){
                Graph h=g; h.adj[a]&=~(1u<<b); h.adj[b]&=~(1u<<a);
                int zhe=zhat_of(&h);
                cnt++;
                if(zhe>zh){ found++; printf("EDGEDELUP %s e=(%d,%d) zh=%d zh-e=%d\n",line,a,b,zh,zhe); }
            }
        }
        fprintf(stderr,"edgedel: pairs=%ld increases=%ld\n",cnt,found);
    } else if(!strcmp(mode,"single")){
        while(fgets(line,sizeof line,stdin)){
            line[strcspn(line,"\r\n")]=0; if(!line[0])continue;
            Graph g; if(parse_g6(line,&g)) continue;
            int z=Z_std(&g), zp=Z_psd(&g);
            mask wit;
            int zh=Zhat_exact(&g,z,&wit);
            printf("%s n=%d Z+=%d Zhat=%d Z=%d kappa=%d delta=%d cut=%d sep2=%d witnessloops=%u\n",
                line,g.n,zp,zh,z,kappa(&g),mindeg(&g),has_cutvertex(&g),has_2sep(&g),wit);
        }
    } else { fprintf(stderr,"unknown mode\n"); return 1; }
    return 0;
}
