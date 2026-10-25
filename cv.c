/* cv.c -- block closure of Zhat and Z, and loop-restricted variants of Zhat.
   Reads graph6 lines (connected graphs, n <= 20) on stdin.

   For each graph G it prints one line
     g6 n Zhat Z Bhat BZ cons cl cu mm Rmin Rmax
   where
     Zhat, Z  : enhanced and standard zero forcing number of G;
     Bhat, BZ : block closure of Zhat (resp. Z): equal to the base parameter on
                2-connected graphs, K1 and K2 have value 1, additive over
                components, and at a cut vertex v with G = G1 (+)_v G2
                X(G) = max{X(G1)+X(G2), X(G1-v)+X(G2-v)} - 1;
     cons     : 1 if Bhat and BZ come out the same at every cut vertex of G and
                for every choice of which component of G-v forms G1;
     cl, cu   : max of Z(Ghat) over loop configurations with every cut vertex
                looped (cl), resp. unlooped (cu);
     mm       : max over loops away from cut vertices of the min over loops
                at cut vertices;
     Rmin,Rmax: least and largest value of R(G1,G2) for Zhat over all cut
                vertices of G (the formula of the cut vertex theorem).
   Mode "spread" (argv[1]) instead checks, for 2-connected input H, that
   Zhat(H) <= Bhat(H-v)+1 and Z(H) <= BZ(H-v)+1 for every v, printing
   "g6 ok_hat ok_z".
   Canonical forms by nauty (densenauty) are used only to memoize values. */
#define MAXN 20
#include "nauty.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>

/* ---------------------------------------------------------- subsets by size */
static int *ordt[MAXN + 1], startt[MAXN + 1][MAXN + 2];
static void prep(int n) {
  if (ordt[n]) return;
  ordt[n] = malloc(sizeof(int) << n); int c = 0;
  for (int s = 0; s <= n; s++) { startt[n][s] = c;
    for (int B = 0; B < (1 << n); B++) if (__builtin_popcount(B) == s) ordt[n][c++] = B; }
  startt[n][n + 1] = c; }

/* ---------------------------------------------------------- forcing */
static int lder(int n, const int *adj, int S, int L) {
  int full = (1 << n) - 1, ch = 1;
  while (ch && S != full) { ch = 0;
    for (int u = 0; u < n; u++) { int w = (adj[u] | ((L >> u & 1) << u)) & ~S;
      if (w && !(w & (w - 1))) { S |= w; ch = 1; } } }
  return S; }
static int sder(int n, const int *adj, int S) {
  int full = (1 << n) - 1, ch = 1;
  while (ch && S != full) { ch = 0;
    for (int u = 0; u < n; u++) if (S >> u & 1) { int w = adj[u] & ~S;
      if (w && !(w & (w - 1))) { S |= w; ch = 1; } } }
  return S; }
static int lz_from(int n, const int *adj, int L, int k) {   /* least size >= k */
  int full = (1 << n) - 1; prep(n); if (k < 0) k = 0;
  for (;; k++) for (int i = startt[n][k]; i < startt[n][k + 1]; i++)
    if (lder(n, adj, ordt[n][i], L) == full) return k; }
/* Z of every loop configuration; toggling one loop changes Z by at most 1 */
static void zall(int n, const int *adj, int *Zl) {
  Zl[0] = lz_from(n, adj, 0, 0);
  for (int L = 1; L < (1 << n); L++) Zl[L] = lz_from(n, adj, L, Zl[L & (L - 1)] - 1); }
static int zstd(int n, const int *adj) {
  int full = (1 << n) - 1; prep(n);
  for (int k = 0;; k++) for (int i = startt[n][k]; i < startt[n][k + 1]; i++)
    if (sder(n, adj, ordt[n][i]) == full) return k; }
static int zhat(int n, const int *adj) {   /* max over L, monotone search as in zz.c */
  int full = (1 << n) - 1, best = 0; prep(n);
  for (int L = 0; L <= full; L++) for (;;) { int ok = 0;
      for (int i = startt[n][best]; i < startt[n][best + 1] && !ok; i++)
        if (lder(n, adj, ordt[n][i], L) == full) ok = 1;
      if (ok) break; best++; }
  return best; }

/* ---------------------------------------------------------- graph helpers */
static int compmask(int n, const int *adj, int S, int start) {  /* component of start in S */
  int C = 1 << start, old;
  do { old = C; for (int u = 0; u < n; u++) if (C >> u & 1) C |= adj[u] & S; } while (C != old);
  return C; }
static int ncomp(int n, const int *adj, int S) {
  int c = 0; while (S) { int C = compmask(n, adj, S, __builtin_ctz(S)); S &= ~C; c++; } return c; }
static int cutverts(int n, const int *adj) {
  int full = (1 << n) - 1, cv = 0;
  for (int v = 0; v < n; v++) if (ncomp(n, adj, full & ~(1 << v)) > 1) cv |= 1 << v;
  return cv; }
static int induce(int n, const int *adj, int S, int *out) {  /* compact induced subgraph */
  int idx[MAXN], k = 0;
  for (int u = 0; u < n; u++) if (S >> u & 1) idx[u] = k++;
  for (int u = 0, i = 0; u < n; u++) if (S >> u & 1) { out[i] = 0;
      for (int w = 0; w < n; w++) if ((S >> w & 1) && (adj[u] >> w & 1)) out[i] |= 1 << idx[w];
      i++; }
  return k; }

/* ---------------------------------------------------------- canonical memo */
typedef struct { int n; uint32_t row[MAXN]; int zh, z, bh, bz; int used; } Entry;
#define HSZ (1 << 22)
static Entry *H;
static void canon(int n, const int *adj, uint32_t *row) {
  graph g[MAXN], cg[MAXN]; int lab[MAXN], ptn[MAXN], orbits[MAXN];
  static DEFAULTOPTIONS_GRAPH(opt); statsblk st; opt.getcanon = TRUE;
  EMPTYGRAPH(g, 1, n);
  for (int u = 0; u < n; u++) for (int w = 0; w < n; w++) if (adj[u] >> w & 1) ADDONEEDGE(g, u, w, 1);
  densenauty(g, lab, ptn, orbits, &opt, &st, 1, n, cg);
  for (int u = 0; u < n; u++) { row[u] = 0;
    for (int w = 0; w < n; w++) if (ISELEMENT(GRAPHROW(cg, u, 1), w)) row[u] |= 1 << w; } }
static Entry *lookup(int n, const int *adj) {
  uint32_t row[MAXN]; canon(n, adj, row);
  uint64_t h = 1469598103934665603ULL ^ n;
  for (int u = 0; u < n; u++) h = (h ^ row[u]) * 1099511628211ULL;
  for (uint64_t i = h & (HSZ - 1);; i = (i + 1) & (HSZ - 1)) {
    Entry *e = &H[i];
    if (!e->used) { e->used = 1; e->n = n; memcpy(e->row, row, sizeof row);
      e->zh = e->z = e->bh = e->bz = -1; return e; }
    if (e->n == n && !memcmp(e->row, row, n * sizeof(uint32_t))) return e; } }
static int base(int n, const int *adj, int which) {
  Entry *e = lookup(n, adj);
  if (which == 0) { if (e->zh < 0) e->zh = zhat(n, adj); return e->zh; }
  if (e->z < 0) e->z = zstd(n, adj); return e->z; }

/* ---------------------------------------------------------- block closure */
static int STAR = 0;
static int B(int n, const int *adj, int which);
static int Bmask(int n, const int *adj, int S, int which) {
  int a[MAXN]; int k = induce(n, adj, S, a); return B(k, a, which); }
/* value of the formula at cut vertex v with G1 = (component C of G-v) + v */
static int Bat(int n, const int *adj, int v, int C, int which) {
  int full = (1 << n) - 1, rest = full & ~C & ~(1 << v);
  int g1 = Bmask(n, adj, C | 1 << v, which), g2 = Bmask(n, adj, rest | 1 << v, which);
  int d1 = Bmask(n, adj, C, which), d2 = Bmask(n, adj, rest, which);
  int x = g1 + g2, y = d1 + d2; return (x > y ? x : y) - 1; }
static int B(int n, const int *adj, int which) {
  if (n == 0) return 0;
  int full = (1 << n) - 1;
  if (ncomp(n, adj, full) > 1) {
    int s = 0, S = full;
    while (S) { int C = compmask(n, adj, S, __builtin_ctz(S)); s += Bmask(n, adj, C, which); S &= ~C; }
    return s; }
  if (n <= 2) return 1;
  Entry *e = lookup(n, adj); int *slot = which == 0 ? &e->bh : &e->bz;
  if (*slot >= 0) return *slot;
  int cv = cutverts(n, adj), val;
  if (!cv) { val = base(n, adj, which);
    if (STAR) for (int u = 0; u < n; u++) { int t = Bmask(n, adj, full & ~(1 << u), which) + 1; if (t < val) val = t; } }
  else { int v = __builtin_ctz(cv);
    int C = compmask(n, adj, full & ~(1 << v), (v == 0) ? 1 : 0);
    val = Bat(n, adj, v, C, which); }
  e = lookup(n, adj); slot = which == 0 ? &e->bh : &e->bz; *slot = val;
  return val; }

/* ---------------------------------------------------------- main */
static int readg6(char *p, int *adj) {
  int n = *p++ - 63, k = 0, x = 0; memset(adj, 0, sizeof(int) * MAXN);
  for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
    if (k == 0) { x = *p++ - 63; k = 6; } k--;
    if (x >> k & 1) { adj[i] |= 1 << j; adj[j] |= 1 << i; } }
  return n; }

int main(int argc, char **argv) {
  int spread = argc > 1 && !strcmp(argv[1], "spread");
  int novar = argc > 1 && !strcmp(argv[1], "novar");
  H = calloc(HSZ, sizeof(Entry));
  { char *e = getenv("STAR"); if (e && *e == '1') STAR = 1; }
  char line[512]; int adj[MAXN]; static int Zl[1 << MAXN];
  while (fgets(line, 512, stdin)) {
    line[strcspn(line, "\n")] = 0; if (!*line) continue;
    int n = readg6(line, adj), full = (1 << n) - 1;
    if (spread) {
      int okh = 1, okz = 1, zh = base(n, adj, 0), z = base(n, adj, 1);
      for (int v = 0; v < n; v++) {
        if (zh > Bmask(n, adj, full & ~(1 << v), 0) + 1) okh = 0;
        if (z > Bmask(n, adj, full & ~(1 << v), 1) + 1) okz = 0; }
      printf("%s %d %d\n", line, okh, okz); fflush(stdout); continue; }
    int cv = cutverts(n, adj);
    int bh = B(n, adj, 0), bz = B(n, adj, 1), cons = 1;
    if (argc > 1 && !strcmp(argv[1], "bonly")) {
      for (int v = 0; v < n; v++) if (cv >> v & 1) { int S = full & ~(1 << v);
        while (S) { int C = compmask(n, adj, S, __builtin_ctz(S)); S &= ~C;
          if (Bat(n, adj, v, C, 0) != bh || Bat(n, adj, v, C, 1) != bz) cons = 0;
          printf("  v=%d C=%x Bhat=%d BZ=%d\n", v, C, Bat(n, adj, v, C, 0), Bat(n, adj, v, C, 1)); } }
      printf("%s %d %d %d %d\n", line, n, bh, bz, cons); fflush(stdout); continue; }
    int Rmin = 99, Rmax = -99;
    for (int v = 0; v < n; v++) if (cv >> v & 1) {
      int S = full & ~(1 << v);
      while (S) { int C = compmask(n, adj, S, __builtin_ctz(S)); S &= ~C;
        if (Bat(n, adj, v, C, 0) != bh || Bat(n, adj, v, C, 1) != bz) cons = 0;
        /* R for Zhat itself at this split */
        int rest = full & ~C & ~(1 << v), a[MAXN], k;
        k = induce(n, adj, C | 1 << v, a); int f1 = k ? base(k, a, 0) : 0;
        k = induce(n, adj, rest | 1 << v, a); int f2 = k ? base(k, a, 0) : 0;
        int w1 = 0, w2 = 0, T;
        for (T = C; T;) { int D = compmask(n, adj, T, __builtin_ctz(T)); T &= ~D; k = induce(n, adj, D, a); w1 += base(k, a, 0); }
        for (T = rest; T;) { int D = compmask(n, adj, T, __builtin_ctz(T)); T &= ~D; k = induce(n, adj, D, a); w2 += base(k, a, 0); }
        int R = (f1 + f2 > w1 + w2 ? f1 + f2 : w1 + w2) - 1;
        if (R < Rmin) Rmin = R; if (R > Rmax) Rmax = R; } }
    if (!cv) Rmin = Rmax = -1;
    int zh, z = zstd(n, adj), cl = -1, cu = -1, mm = -1;
    if (novar) zh = zhat(n, adj);
    else {
      zall(n, adj, Zl); zh = 0; cl = 0; cu = 0; mm = 0;
      for (int L = 0; L <= full; L++) { if (Zl[L] > zh) zh = Zl[L];
        if ((L & cv) == cv && Zl[L] > cl) cl = Zl[L];
        if (!(L & cv) && Zl[L] > cu) cu = Zl[L]; }
      for (int L = 0; L <= full; L++) if (!(L & cv)) {
        int m = 99;                       /* min over subsets T of cv */
        for (int T = cv;; T = (T - 1) & cv) { if (Zl[L | T] < m) m = Zl[L | T]; if (!T) break; }
        if (m > mm) mm = m; } }
    printf("%s %d %d %d %d %d %d %d %d %d %d %d\n", line, n, zh, z, bh, bz, cons, cl, cu, mm, Rmin, Rmax);
    fflush(stdout); }
  return 0; }
