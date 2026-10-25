/* sch.c -- Schur-row forcing of depth k (the parameter Zhat_(k)).

   For a symmetric matrix A with graph G and a set U of looped vertices with
   A[U] nonsingular, every z in N(U) - U gives a vector in the row space of A,
     rho_{U,z} = row_z - A[z,U] A[U]^{-1} A[U,*],
   which vanishes on U.  Its entries are
     t in U                     : 0
     t = z                      : nonzero iff det A[U+z] != 0          (status nu(U+z))
     t in N(U) - U - z          : nonzero iff det A[U+z, U+t] != 0     (status pi(U;z,t))
                                  (definitely nonzero if |U| = 1 and zt not an edge)
     t outside N(U) and U       : a_zt (definite).
   A configuration fixes the loops (nu of singletons) and every status nu(W)
   (|W| >= 2; definitely nonzero if |W| = 2 and W has an unlooped vertex) and
   pi(U;z,t), for connected looped U with |U| <= k.  Forcing uses the rows of A
   and every rho_{U,z} with nu(U) nonzero: a vector with exactly one white
   column carrying a nonzero entry colors that column.  Zhat_(k) is the max
   over configurations of the least size of a forcing set.  Sound: any matrix
   determines a configuration, so M <= Zhat_(k) <= Zhat.

   Exact algorithm: statuses are decided lazily, a partial assignment is
   covered by a seed if the seed works for all completions, and otherwise the
   search splits on a status some seed queried (as in z2.c).

   Input graph6 (n <= 12).  Output: g6 n Zhat Zk cut flag   (flag: cut vertex
   formula fails for Zhat_(k) at some cut vertex / split).
   argv[1] = k (default 1); argv[2] = "nocut" skips the formula check.  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 16
#define MAXS 6000
#define MAXR 4000
static int K = 1, FREE = 0, NOTAU = 0, ANYU = 0, UC = 0, OC = 0;
static unsigned char isTau[6000];
static int n, full, adj[MAXN], L;
static int *ordt[MAXN + 1], startt[MAXN + 1][MAXN + 2];
static void prep(int m) {
  if (ordt[m]) return; ordt[m] = malloc(sizeof(int) << m); int c = 0;
  for (int s = 0; s <= m; s++) { startt[m][s] = c; for (int B = 0; B < (1 << m); B++) if (__builtin_popcount(B) == s) ordt[m][c++] = B; }
  startt[m][m + 1] = c; }

/* ---- statuses ---- */
static int NS;                      /* number of free statuses */
/* nu codes: -1 definite nonzero, -3 definite zero, >=0 status index; hashed by vertex set */
#define HN 8192
static int hkey[HN], hval[HN], hgen[HN], GEN = 0;
typedef struct { int U, z, nuU, ncol, col[MAXN], st[MAXN], Dm; } Row;   /* st: status index for col */
static Row R[MAXR]; static int NR;
static int nbrs(int S) { int m = 0; for (int u = 0; u < n; u++) if (S >> u & 1) m |= adj[u]; return m & ~S; }
static int connected(int S) {
  if (!S) return 0; int C = S & -S, o; do { o = C; for (int u = 0; u < n; u++) if (C >> u & 1) C |= adj[u] & S; } while (C != o); return C == S; }
static int nu(int W) {              /* status code for det A[W] != 0 */
  int c = __builtin_popcount(W);
  if (c == 1) return (L & W) ? -1 : -3;
  if (c == 2 && (W & ~L)) return -1;                   /* zero diagonal entry: det = -a^2 */
  unsigned h = (unsigned)W * 2654435761u;
  for (unsigned i = h % HN;; i = (i + 1) % HN) {
    if (hgen[i] != GEN) { hgen[i] = GEN; hkey[i] = W; return hval[i] = NS++; }
    if (hkey[i] == W) return hval[i]; } }

static void build(void) {
  NS = 0; NR = 0; GEN++; memset(isTau, 0, sizeof isTau);
  /* connected sets of looped vertices of size <= K, by extension */
  static int sets[4096]; int ns = 0;
  for (int u = 0; u < n && K > 0; u++) if (ANYU || (L >> u & 1)) sets[ns++] = 1 << u;
  for (int lev = 0, lo = 0; lev < K - 1; lev++) { int hi = ns;
    for (int i = lo; i < hi; i++) { int ext = nbrs(sets[i]) & (ANYU ? full : L);
      for (int u = 0; u < n; u++) if (ext >> u & 1) { int W = sets[i] | 1 << u, dup = 0;
        for (int j = hi; j < ns; j++) if (sets[j] == W) { dup = 1; break; }
        if (!dup && ns < 4096) sets[ns++] = W; } }
    lo = hi; }
  /* base rows */
  for (int z = 0; z < n; z++) { Row *r = &R[NR++]; r->U = 0; r->z = z; r->nuU = -1; r->ncol = 0;
    r->Dm = adj[z] | ((L >> z & 1) << z); }
  for (int si = 0; si < ns; si++) { int U = sets[si];
    int nuU = nu(U), NU = nbrs(U);
    if (nuU == -3) continue;
    int piIdx[MAXN][MAXN];
    for (int z = 0; z < n; z++) for (int t = 0; t < n; t++) piIdx[z][t] = -9;
    for (int z = 0; z < n; z++) if (NU >> z & 1) {
      if (NR >= MAXR) { fprintf(stderr, "MAXR\n"); exit(1); }
      Row *r = &R[NR++]; r->U = U; r->z = z; r->nuU = nuU; r->ncol = 0;
      r->Dm = adj[z] & ~NU & ~U;                       /* definite entries a_zt outside N(U) */
      int s = nu(U | 1 << z);
      if (s == -1) r->Dm |= 1 << z; else if (s >= 0) { r->col[r->ncol] = z; r->st[r->ncol++] = s; }
      for (int t = 0; t < n; t++) if ((NU >> t & 1) && t != z) {
        if (__builtin_popcount(U) == 1 && !(adj[z] >> t & 1)) { r->Dm |= 1 << t; continue; }
        int a = z < t ? z : t, b = z < t ? t : z;
        if (piIdx[a][b] == -9) { piIdx[a][b] = NS; isTau[NS] = 1; NS++; }
        r->col[r->ncol] = t; r->st[r->ncol++] = piIdx[a][b]; } } }
  if (NS > MAXS) { fprintf(stderr, "MAXS %d\n", NS); exit(1); } }

/* ---- unique cover rule: number (capped at 2) of spanning covers of G[W] by loops at L,
   edges and cycles; det A[W] is a single monomial iff this is 1 ---- */
#define CN 65536
static int ckey[CN], cval[CN], cgen[CN];
static int ccount(int W);
static int cyc_acc; static int cyc_W;
static void cycdfs(int start, int last, int path, int len, int second) {
  if (cyc_acc >= 2) return;
  for (int v = 0; v < n; v++) if ((cyc_W >> v & 1) && (adj[last] >> v & 1)) {
    if (v == start && len >= 3 && last > second) { cyc_acc += ccount(cyc_W & ~path); if (cyc_acc >= 2) return; continue; }
    if (path >> v & 1) continue;
    if (v < start) continue;
    cycdfs(start, v, path | 1 << v, len + 1, len == 1 ? v : second); } }
static int ccount(int W) {
  if (!W) return 1;
  unsigned h = (unsigned)W * 2654435761u;
  unsigned i = h % CN;
  for (;; i = (i + 1) % CN) { if (cgen[i] != GEN) break; if (ckey[i] == W) return cval[i]; }
  int u = __builtin_ctz(W), r = 0;
  if (L >> u & 1) r += ccount(W & ~(1 << u));
  for (int v = 0; v < n && r < 2; v++) if ((adj[u] & W) >> v & 1) r += ccount(W & ~(1 << u) & ~(1 << v));
  if (r < 2) { int sW = cyc_W, sa = cyc_acc; cyc_W = W; cyc_acc = 0;
    cycdfs(u, u, 1 << u, 1, -1); r += cyc_acc; cyc_W = sW; cyc_acc = sa; }
  if (r > 2) r = 2;
  for (i = h % CN;; i = (i + 1) % CN) if (cgen[i] != GEN) { cgen[i] = GEN; ckey[i] = W; cval[i] = r; break; }
  return r; }
static int isoddcycle(int C) {
  int k = __builtin_popcount(C); if (k < 3 || !(k & 1) || (C & L)) return 0;
  for (int u = 0; u < n; u++) if ((C >> u & 1) && __builtin_popcount(adj[u] & C) != 2) return 0;
  return 1; }
static int ucfire(int S) {     /* apply the component rule once; returns new S */
  int Wt = full & ~S, T = S;
  while (Wt) { int C = Wt & -Wt, o; do { o = C; for (int u = 0; u < n; u++) if (C >> u & 1) C |= adj[u] & Wt; } while (C != o);
    Wt &= ~C;
    if ((OC && isoddcycle(C)) || (UC && ccount(C) == 1)) T |= C; }
  return T; }

/* value of status code under assignment: 1 nonzero, 0 zero, -1 undecided */
static inline int val(int code, const signed char *as) { return code == -1 ? 1 : code == -3 ? 0 : as[code]; }

static unsigned char Q[MAXS];       /* statuses queried */
static int closeS(int S, const signed char *as) {
  int ch = 1;
  while (ch && S != full) { ch = 0;
    for (int i = 0; i < NR; i++) { Row *r = &R[i];
      if (r->nuU != -1 && val(r->nuU, as) != 1) continue;
      int W = full & ~S & ~r->U;
      int nz = r->Dm & W, cnt = __builtin_popcount(nz), und = 0, tgt = nz;
      if (cnt > 1) continue;
      for (int j = 0; j < r->ncol && cnt <= 1; j++) if (W >> r->col[j] & 1) {
        int v = as[r->st[j]]; if (v == 1) { cnt++; tgt = 1 << r->col[j]; } else if (v == -1) und++; }
      if (cnt == 1 && !und) { S |= tgt; ch = 1; } }
    if (!ch && S != full && (UC || OC)) { int T = ucfire(S); if (T != S) { S = T; ch = 1; } } }
  return S; }

static int works(int S, signed char *as) {
  S = closeS(S, as);
  if (S == full) return 1;
  if (FREE) return 0;
  int br = -1;
  for (int i = 0; i < NR && br < 0; i++) { Row *r = &R[i];
    int W = full & ~S & ~r->U, cnt = __builtin_popcount(r->Dm & W), firstund = -1;
    if (cnt > 1) continue;
    for (int j = 0; j < r->ncol; j++) if (W >> r->col[j] & 1) {
      int v = as[r->st[j]]; if (v == 1) cnt++; else if (v == -1 && firstund < 0 && !(NOTAU && isTau[r->st[j]])) firstund = r->st[j]; }
    if (cnt > 1) continue;
    if (r->nuU >= 0 && as[r->nuU] == -1) { if (cnt == 1 || firstund >= 0) br = r->nuU; continue; }
    if (r->nuU >= 0 && as[r->nuU] == 0) continue;
    if (firstund >= 0) br = firstund; }
  if (br < 0) return 0;
  Q[br] = 1;
  as[br] = 1; int ok = works(S, as);
  if (ok) { as[br] = 0; ok = works(S, as); }
  as[br] = -1; return ok; }

static int covered(int k, signed char *as) {
  memset(Q, 0, NS);
  unsigned char q[MAXS]; memset(q, 0, NS);
  for (int i = startt[n][k]; i < startt[n][k + 1]; i++) {
    memset(Q, 0, NS);
    if (works(ordt[n][i], as)) return 1;
    for (int s = 0; s < NS; s++) q[s] |= Q[s]; }
  int e = -1; for (int s = 0; s < NS; s++) if (q[s] && as[s] == -1 && !(NOTAU && isTau[s])) { e = s; break; }
  if (e < 0) return 0;
  as[e] = 1; int ok = covered(k, as);
  if (ok) { as[e] = 0; ok = covered(k, as); }
  as[e] = -1; return ok; }

static int lclose(int S) {
  int ch = 1;
  while (ch && S != full) { ch = 0;
    for (int u = 0; u < n; u++) { int w = (adj[u] | ((L >> u & 1) << u)) & ~S; if (w && !(w & (w - 1))) { S |= w; ch = 1; } }
    if (!ch && S != full && (UC || OC)) { int T = ucfire(S); if (T != S) { S = T; ch = 1; } } }
  return S; }
static int le(int k) {      /* Z_(k)(G, L) <= k ? */
  GEN++;
  for (int i = startt[n][k]; i < startt[n][k + 1]; i++) if (lclose(ordt[n][i]) == full) return 1;
  build();
  signed char as[MAXS]; memset(as, -1, NS);
  return covered(k, as); }

static int lclose0(int S) {
  int ch = 1;
  while (ch && S != full) { ch = 0;
    for (int u = 0; u < n; u++) { int w = (adj[u] | ((L >> u & 1) << u)) & ~S; if (w && !(w & (w - 1))) { S |= w; ch = 1; } } }
  return S; }
static int lzle(int k) { for (int i = startt[n][k]; i < startt[n][k + 1]; i++) if (lclose0(ordt[n][i]) == full) return 1; return 0; }
static void eval(int m, const int *a, int *zh, int *zk) {
  n = m; full = (1 << n) - 1; memcpy(adj, a, sizeof(int) * n); prep(n);
  /* Zhat first, remembering a configuration that attains it */
  int c = 0, Lstar = 0;
  for (L = 0; L <= full; L++) while (!lzle(c)) { c++; Lstar = L; }
  /* lower bound: Zhat_(k) >= c - 1 if the configuration Lstar is not covered at c - 2 */
  int b = 0;
  if (c >= 2) { L = Lstar; if (!le(c - 2)) b = c - 1; }
  /* exact value by the monotone search, started at the lower bound */
  for (L = 0; L <= full; L++) while (!le(b)) b++;
  *zh = c; *zk = b; }

static int compmask(int m, const int *a, int S, int s) {
  int C = 1 << s, o; do { o = C; for (int u = 0; u < m; u++) if (C >> u & 1) C |= a[u] & S; } while (C != o); return C; }
static int induce(int m, const int *a, int S, int *out) {
  int idx[MAXN], k = 0; for (int u = 0; u < m; u++) if (S >> u & 1) idx[u] = k++;
  for (int u = 0, i = 0; u < m; u++) if (S >> u & 1) { out[i] = 0;
      for (int w = 0; w < m; w++) if ((S >> w & 1) && (a[u] >> w & 1)) out[i] |= 1 << idx[w]; i++; }
  return k; }
static int zk_mask(int m, const int *a, int S) {
  int t = 0; while (S) { int C = compmask(m, a, S, __builtin_ctz(S)); S &= ~C;
    int b[MAXN]; int k = induce(m, a, C, b); int zh, zk; eval(k, b, &zh, &zk); t += zk; } return t; }

int main(int argc, char **argv) {
  if (argc > 1) K = atoi(argv[1]);
  if (getenv("FREE")) FREE = 1;
  if (getenv("NOTAU")) NOTAU = 1;
  if (getenv("ANYU")) ANYU = 1;
  if (getenv("UC")) UC = 1;
  if (getenv("OC")) OC = 1;
  int nocut = argc > 2 && (!strcmp(argv[2], "nocut") || !strcmp(argv[2], "cutonly"));
  int cutonly = argc > 2 && !strcmp(argv[2], "cutonly");
  char line[512];
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\n")] = 0; if (!*line) continue;
    char *p = line; int m = *p++ - 63, k = 0, x = 0, a[MAXN] = {0};
    for (int j = 1; j < m; j++) for (int i = 0; i < j; i++) {
      if (k == 0) { x = *p++ - 63; k = 6; } k--;
      if (x >> k & 1) { a[i] |= 1 << j; a[j] |= 1 << i; } }
    int fm = (1 << m) - 1;
    if (cutonly) { int has = 0;
      for (int v = 0; v < m && !has; v++) { int S = fm & ~(1 << v); if (compmask(m, a, S, __builtin_ctz(S)) != S) has = 1; }
      if (!has) continue; }
    int zh, zk; eval(m, a, &zh, &zk);
    int cut = 0, flag = 0;
    for (int v = 0; v < m && !nocut; v++) {
      int S = fm & ~(1 << v);
      if (compmask(m, a, S, __builtin_ctz(S)) == S) continue;
      cut = 1;
      while (S) { int C = compmask(m, a, S, __builtin_ctz(S)); S &= ~C;
        int R2 = fm & ~C & ~(1 << v);
        int x1 = zk_mask(m, a, C | 1 << v) + zk_mask(m, a, R2 | 1 << v);
        int x2 = zk_mask(m, a, C) + zk_mask(m, a, R2);
        if ((x1 > x2 ? x1 : x2) - 1 != zk) flag = 1; } }
    printf("%s %d %d %d %d %d\n", line, m, zh, zk, cut, flag); fflush(stdout); }
  return 0; }
