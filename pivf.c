/* pivf.c -- (pivot game with cut vertex formula check; see piv.c)
   Output: g6 n Zhat PIV cut flag, flag = 1 if the cut vertex formula fails
   for PIV at some cut vertex and some split.

   piv.c -- loop zero forcing with Schur complement pivots (the pivot game).

   State: a loop graph (vertex set A, adjacency, loop set L).  The value
     P(state) = min{ Z(state),  min over looped y with deg(y) <= DEG of
                     max over resolutions R of P(state / y, R) }
   where state / y deletes y, joins every nonadjacent pair of neighbors of y
   (that entry of the Schur complement is -a_uy a_yw / a_yy, nonzero), and
   leaves free -- to be resolved by the adversary -- every edge between two
   neighbors of y and the loop at every neighbor of y.  For a real symmetric
   matrix with nonzero diagonal entry at y the Schur complement has the same
   nullity, so P is an upper bound for the nullity of every matrix with the
   given loop configuration; PIV(G) = max over loop configurations.

   Input graph6 (n <= 16).  Output: g6 n Zhat PIV.   Env DEG (default 2). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXN 16
#include "nauty.h"

static int N0, DEG = 2;
static int *ordtab[MAXN + 1], starttab[MAXN + 1][MAXN + 2];
static int *ordt; static int *startt;
static void prep(int n) {
  if (!ordtab[n]) { ordtab[n] = malloc(sizeof(int) << n); int c = 0;
    for (int q = 0; q <= n; q++) { starttab[n][q] = c; for (int B = 0; B < (1 << n); B++) if (__builtin_popcount(B) == q) ordtab[n][c++] = B; }
    starttab[n][n + 1] = c; }
  ordt = ordtab[n]; startt = starttab[n]; }

typedef struct { int A, L; int adj[MAXN]; } St;

static int lclose(const St *s, int S) {
  int ch = 1;
  while (ch && S != s->A) { ch = 0;
    for (int u = 0; u < N0; u++) if (s->A >> u & 1) {
      int w = (s->adj[u] | ((s->L >> u & 1) << u)) & ~S & s->A;
      if (w && !(w & (w - 1))) { S |= w; ch = 1; } } }
  return S; }
static int zle(const St *s, int k) {   /* loop forcing number <= k ? (seeds inside A) */
  int na = __builtin_popcount(s->A); if (k >= na) return 1; if (k < 0) return 0;
  for (int i = startt[k]; i < startt[k + 1]; i++) { int B = ordt[i];
    if (B & ~s->A) continue;
    if (lclose(s, B) == s->A) return 1; }
  return 0; }

/* memo: key = state, value = (lo, hi): P > lo known false?  store maxfalse, mintrue */
typedef struct { St s; int used, maxfalse, mintrue; } Ent;
#define HS (1 << 21)
static Ent *H; static int GEN = 1;
static uint64_t hsh(const St *s) {
  uint64_t h = 1469598103934665603ULL ^ (uint64_t)s->A * 31 ^ (uint64_t)s->L * 131;
  for (int u = 0; u < N0; u++) h = (h ^ (uint32_t)s->adj[u]) * 1099511628211ULL;
  return h; }
static Ent *look(const St *s) {
  for (uint64_t i = hsh(s) & (HS - 1);; i = (i + 1) & (HS - 1)) {
    Ent *e = &H[i];
    if (e->used != GEN) { e->used = GEN; e->s = *s; e->maxfalse = -1; e->mintrue = 99; return e; }
    if (!memcmp(&e->s, s, sizeof(St))) return e; } }
static long long nent = 0;

static int le(const St *s, int k);
/* enumerate resolutions recursively: free items list */
static int allres(const St *base, int *fu, int *fw, int nf, int idx, int k) {
  if (idx == nf) return le(base, k);
  St t = *base;
  /* option 0: item absent */
  if (fu[idx] == fw[idx]) t.L &= ~(1 << fu[idx]);
  else { t.adj[fu[idx]] &= ~(1 << fw[idx]); t.adj[fw[idx]] &= ~(1 << fu[idx]); }
  if (!allres(&t, fu, fw, nf, idx + 1, k)) return 0;
  t = *base;
  if (fu[idx] == fw[idx]) t.L |= 1 << fu[idx];
  else { t.adj[fu[idx]] |= 1 << fw[idx]; t.adj[fw[idx]] |= 1 << fu[idx]; }
  return allres(&t, fu, fw, nf, idx + 1, k); }

static int le(const St *s, int k) {
  if (k < 0) return 0;
  Ent *e = look(s);
  if (k >= e->mintrue) return 1;
  if (k <= e->maxfalse) return 0;
  int res = 0;
  if (zle(s, k)) res = 1;
  else {
    for (int y = 0; y < N0 && !res; y++) {
      if (!(s->A >> y & 1) || !(s->L >> y & 1)) continue;
      int nb = s->adj[y] & s->A, d = __builtin_popcount(nb);
      if (d > DEG) continue;
      St t = *s; t.A &= ~(1 << y); t.L &= ~(1 << y);
      for (int u = 0; u < N0; u++) t.adj[u] &= ~(1 << y);
      t.adj[y] = 0;
      int fu[64], fw[64], nf = 0, list[MAXN], m = 0;
      for (int u = 0; u < N0; u++) if (nb >> u & 1) list[m++] = u;
      for (int i = 0; i < m; i++) { fu[nf] = fw[nf] = list[i]; nf++; }
      for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) {
        int u = list[i], w = list[j];
        if (s->adj[u] >> w & 1) { fu[nf] = u; fw[nf] = w; nf++; }
        else { t.adj[u] |= 1 << w; t.adj[w] |= 1 << u; } }
      if (allres(&t, fu, fw, nf, 0, k)) res = 1; } }
  e = look(s);
  if (res) { if (k < e->mintrue) e->mintrue = k; } else { if (k > e->maxfalse) e->maxfalse = k; }
  return res; }


/* value of PIV (and Zhat) for a labeled graph on n <= 16 vertices */
static void pv_eval(int n, const int *adj, int *zh, int *pv) {
  St s; memset(&s, 0, sizeof s); N0 = n; s.A = (1 << n) - 1;
  for (int u = 0; u < n; u++) s.adj[u] = adj[u];
  prep(n); GEN++;
  int a = 0, b = 0;
  for (int L = 0; L < (1 << n); L++) { s.L = L; while (!zle(&s, a)) a++; }
  for (int L = 0; L < (1 << n); L++) { s.L = L; while (!le(&s, b)) b++; }
  *zh = a; *pv = b; }

/* PIV first, then Zhat by a monotone search started at PIV. */
static void pv_eval2(int n, const int *adj, int *zh, int *pv) {
  St s; memset(&s, 0, sizeof s); N0 = n; s.A = (1 << n) - 1;
  for (int u = 0; u < n; u++) s.adj[u] = adj[u];
  prep(n); GEN++;
  int b = 0;
  for (int L = 0; L < (1 << n); L++) { s.L = L; while (!le(&s, b)) b++; }
  int a = b;
  for (int L = 0; L < (1 << n); L++) { s.L = L; while (!zle(&s, a)) a++; }
  *zh = a; *pv = b; }

/* canonical memo for connected pieces */
typedef struct { int n, used; uint32_t row[MAXN]; int pv; } CE;
#define CS (1 << 20)
static CE *CH;
static void canon(int n, const int *adj, uint32_t *row) {
  graph g[MAXN], cg[MAXN]; int lab[MAXN], ptn[MAXN], orb[MAXN];
  static DEFAULTOPTIONS_GRAPH(opt); statsblk st; opt.getcanon = TRUE;
  EMPTYGRAPH(g, 1, n);
  for (int u = 0; u < n; u++) for (int w = 0; w < n; w++) if (adj[u] >> w & 1) ADDONEEDGE(g, u, w, 1);
  densenauty(g, lab, ptn, orb, &opt, &st, 1, n, cg);
  for (int u = 0; u < n; u++) { row[u] = 0; for (int w = 0; w < n; w++) if (ISELEMENT(GRAPHROW(cg, u, 1), w)) row[u] |= 1u << w; } }
static int pv_conn(int n, const int *adj) {
  if (n <= 1) return n;
  uint32_t row[MAXN]; canon(n, adj, row);
  uint64_t h = 1469598103934665603ULL ^ n;
  for (int u = 0; u < n; u++) h = (h ^ row[u]) * 1099511628211ULL;
  for (uint64_t i = h & (CS - 1);; i = (i + 1) & (CS - 1)) {
    CE *e = &CH[i];
    if (!e->used) { int zh, pv; pv_eval(n, adj, &zh, &pv);
      e->used = 1; e->n = n; memcpy(e->row, row, sizeof(uint32_t) * MAXN); e->pv = pv; return pv; }
    if (e->n == n && !memcmp(e->row, row, sizeof(uint32_t) * n)) return e->pv; } }
static int compmask(int n, const int *adj, int S, int st) {
  int C = 1 << st, o; do { o = C; for (int u = 0; u < n; u++) if (C >> u & 1) C |= adj[u] & S; } while (C != o); return C; }
static int induce(int n, const int *adj, int S, int *out) {
  int idx[MAXN], k = 0; for (int u = 0; u < n; u++) if (S >> u & 1) idx[u] = k++;
  for (int u = 0, i = 0; u < n; u++) if (S >> u & 1) { out[i] = 0;
      for (int w = 0; w < n; w++) if ((S >> w & 1) && (adj[u] >> w & 1)) out[i] |= 1 << idx[w]; i++; }
  return k; }
static int pv_mask(int n, const int *adj, int S) {
  int t = 0; while (S) { int C = compmask(n, adj, S, __builtin_ctz(S)); S &= ~C;
    int a[MAXN]; int k = induce(n, adj, C, a); t += pv_conn(k, a); } return t; }

int main(int argc, char **argv) {
  char *d = getenv("DEG"); if (d) DEG = atoi(d);
  int nocut = argc > 1 && !strcmp(argv[1], "nocut");
  int cutonly = argc > 1 && !strcmp(argv[1], "cutonly");
  H = calloc(HS, sizeof(Ent)); CH = calloc(CS, sizeof(CE));
  char line[512];
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\n")] = 0; if (!*line) continue;
    char *p = line; int n = *p++ - 63, k = 0, x = 0, adj[MAXN] = {0};
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
      if (k == 0) { x = *p++ - 63; k = 6; } k--;
      if (x >> k & 1) { adj[i] |= 1 << j; adj[j] |= 1 << i; } }
    int full = (1 << n) - 1;
    if (cutonly) { int has = 0;
      for (int v = 0; v < n && !has; v++) { int S = full & ~(1 << v); if (compmask(n, adj, S, __builtin_ctz(S)) != S) has = 1; }
      if (!has) continue; }
    int zh, pv; pv_eval2(n, adj, &zh, &pv);
    int cut = 0, flag = 0;
    for (int v = 0; v < n && !nocut; v++) {
      int S = full & ~(1 << v);
      if (compmask(n, adj, S, __builtin_ctz(S)) == S) continue;
      cut = 1;
      while (S) { int C = compmask(n, adj, S, __builtin_ctz(S)); S &= ~C;
        int R2 = full & ~C & ~(1 << v);
        int a = pv_mask(n, adj, C | 1 << v) + pv_mask(n, adj, R2 | 1 << v);
        int b = pv_mask(n, adj, C) + pv_mask(n, adj, R2);
        if ((a > b ? a : b) - 1 != pv) flag = 1; } }
    printf("%s %d %d %d %d %d\n", line, n, zh, pv, cut, flag); fflush(stdout); }
  return 0; }
