/* z2.c -- enhanced zero forcing with 2x2 minor statuses (the parameter Zhat_2).

   A 2-configuration of G is a loop set L together with, for every edge uv
   with both ends looped, a status N ("the principal 2x2 block on {u,v} is
   nonsingular") or S ("it is singular").  For a blue set, the rules are
     (R1) loop rule: if Nh(u) has exactly one white vertex w, color w blue;
     (R2) status N on uv: if u, v are white and Nh(u) u Nh(v) has no other
          white vertex, color u and v blue;
     (R3) status S on uv: with D = (N(u) xor N(v)) - {u,v} and
          C = N(u) & N(v), if the white vertices of D u C are exactly {w}
          and w is in D, color w blue.
   Z_2(L,sigma) = least size of a set from which R1-R3 color everything, and
   Zhat_2(G) = max over 2-configurations.

   Exact algorithm.  For fixed L and k, "every sigma has a working seed of
   size k" is decided by a covering search: a seed is tested against a
   partial status assignment with undecided statuses resolved lazily (both
   ways) when one of their rules would fire; if no seed covers the partial
   assignment, split on a status that some seed queried.

   Input: graph6 lines (n <= 16).  Output: g6 n Zhat Zhat2 cut flag
   where cut = 1 if G has a cut vertex, and flag = 1 if at some cut vertex v
   and some component C of G-v, with G1 = G[C+v], G2 = G - C,
     Zhat2(G) != max{Zhat2(G1)+Zhat2(G2), Zhat2(G1-v)+Zhat2(G2-v)} - 1.
   Mode "nocut" skips the formula check.  Environment NORULE2 / NORULE3
   disable the corresponding rule.  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 16
static int RULE2 = 1, RULE3 = 1;
static int *ordt[MAXN + 1], startt[MAXN + 1][MAXN + 2];
static void prep(int n) {
  if (ordt[n]) return;
  ordt[n] = malloc(sizeof(int) << n); int c = 0;
  for (int s = 0; s <= n; s++) { startt[n][s] = c;
    for (int B = 0; B < (1 << n); B++) if (__builtin_popcount(B) == s) ordt[n][c++] = B; }
  startt[n][n + 1] = c; }

typedef struct { int n, full, adj[MAXN], ne, eu[MAXN * MAXN / 2], ev[MAXN * MAXN / 2];
                 unsigned long long Q[2]; } Gr;

static int loopclose(const Gr *g, int S, int L) {
  int ch = 1;
  while (ch && S != g->full) { ch = 0;
    for (int u = 0; u < g->n; u++) { int w = (g->adj[u] | ((L >> u & 1) << u)) & ~S;
      if (w && !(w & (w - 1))) { S |= w; ch = 1; } } }
  return S; }

static int fires(const Gr *g, int S, int e, int which) {
  int u = g->eu[e], v = g->ev[e], uv = (1 << u) | (1 << v);
  if (which == 0) return RULE2 && !(S & uv) && (((g->adj[u] | g->adj[v] | uv) & ~S) == uv);
  int D = (g->adj[u] ^ g->adj[v]) & ~uv, C = g->adj[u] & g->adj[v], w = (D | C) & ~S;
  return RULE3 && w && !(w & (w - 1)) && (w & D); }

#define BIT(m, e) (((m)[(e) >> 6] >> ((e) & 63)) & 1)
#define SETB(m, e) ((m)[(e) >> 6] |= 1ULL << ((e) & 63))

static int close3(const Gr *g, int S, int L, const unsigned long long *Nm, const unsigned long long *Sm) {
  int ch = 1;
  while (ch && S != g->full) { ch = 0;
    int T = loopclose(g, S, L); if (T != S) { S = T; ch = 1; }
    for (int e = 0; e < g->ne; e++) {
      int u = g->eu[e], v = g->ev[e], uv = (1 << u) | (1 << v);
      if (BIT(Nm, e) && fires(g, S, e, 0)) { S |= uv; ch = 1; }
      if (BIT(Sm, e) && fires(g, S, e, 1)) {
        int D = (g->adj[u] ^ g->adj[v]) & ~uv, C = g->adj[u] & g->adj[v];
        S |= (D | C) & ~S; ch = 1; } } }
  return S; }

static int works(Gr *g, int S, int L, const unsigned long long *Nm, const unsigned long long *Sm) {
  S = close3(g, S, L, Nm, Sm);
  if (S == g->full) return 1;
  for (int e = 0; e < g->ne; e++) {
    if (!((L >> g->eu[e]) & 1) || !((L >> g->ev[e]) & 1)) continue;
    if (BIT(Nm, e) || BIT(Sm, e)) continue;
    if (fires(g, S, e, 0) || fires(g, S, e, 1)) {
      SETB(g->Q, e);
      unsigned long long N2[2] = {Nm[0], Nm[1]}, S2[2] = {Sm[0], Sm[1]};
      SETB(N2, e); if (!works(g, S, L, N2, Sm)) return 0;
      SETB(S2, e); return works(g, S, L, Nm, S2); } }
  return 0; }

static int covered(Gr *g, int L, int k, const unsigned long long *Nm, const unsigned long long *Sm) {
  unsigned long long q[2] = {0, 0}; int n = g->n;
  for (int i = startt[n][k]; i < startt[n][k + 1]; i++) {
    g->Q[0] = g->Q[1] = 0;
    if (works(g, ordt[n][i], L, Nm, Sm)) return 1;
    q[0] |= g->Q[0]; q[1] |= g->Q[1]; }
  if (!q[0] && !q[1]) return 0;
  int e = q[0] ? __builtin_ctzll(q[0]) : 64 + __builtin_ctzll(q[1]);
  unsigned long long N2[2] = {Nm[0], Nm[1]}, S2[2] = {Sm[0], Sm[1]};
  SETB(N2, e); if (!covered(g, L, k, N2, Sm)) return 0;
  SETB(S2, e); return covered(g, L, k, Nm, S2); }

static int exists_k(Gr *g, int L, int k) {
  int n = g->n;
  for (int i = startt[n][k]; i < startt[n][k + 1]; i++) if (loopclose(g, ordt[n][i], L) == g->full) return 1;
  unsigned long long a[2] = {0, 0}, b[2] = {0, 0};
  return covered(g, L, k, a, b); }

static void build(Gr *g, int n, const int *adj) {
  g->n = n; g->full = (1 << n) - 1; memcpy(g->adj, adj, sizeof(int) * n); g->ne = 0;
  for (int j = 0; j < n; j++) for (int i = 0; i < j; i++) if (adj[i] >> j & 1) { g->eu[g->ne] = i; g->ev[g->ne] = j; g->ne++; }
  prep(n); }

static int zhat_of(Gr *g) {
  int best = 0, n = g->n;
  for (int L = 0; L <= g->full; L++) for (;;) { int ok = 0;
    for (int i = startt[n][best]; i < startt[n][best + 1] && !ok; i++) if (loopclose(g, ordt[n][i], L) == g->full) ok = 1;
    if (ok) break; best++; }
  return best; }
static int z2_of(Gr *g) {
  int best = 0;
  for (int L = 0; L <= g->full; L++) while (!exists_k(g, L, best)) best++;
  return best; }

/* ---- induced subgraphs, components, Zhat2 of possibly disconnected graphs ---- */
static int compmask(int n, const int *adj, int S, int s) {
  int C = 1 << s, o; do { o = C; for (int u = 0; u < n; u++) if (C >> u & 1) C |= adj[u] & S; } while (C != o); return C; }
static int induce(int n, const int *adj, int S, int *out) {
  int idx[MAXN], k = 0; for (int u = 0; u < n; u++) if (S >> u & 1) idx[u] = k++;
  for (int u = 0, i = 0; u < n; u++) if (S >> u & 1) { out[i] = 0;
      for (int w = 0; w < n; w++) if ((S >> w & 1) && (adj[u] >> w & 1)) out[i] |= 1 << idx[w]; i++; }
  return k; }
static int z2_mask(int n, const int *adj, int S) {   /* additive over components */
  int tot = 0;
  while (S) { int C = compmask(n, adj, S, __builtin_ctz(S)); S &= ~C;
    int a[MAXN]; int k = induce(n, adj, C, a); Gr h; build(&h, k, a); tot += z2_of(&h); }
  return tot; }

int main(int argc, char **argv) {
  if (getenv("NORULE2")) RULE2 = 0;
  if (getenv("NORULE3")) RULE3 = 0;
  int nocut = argc > 1 && !strcmp(argv[1], "nocut");
  char line[512];
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\n")] = 0; if (!*line) continue;
    char *p = line; int n = *p++ - 63, adj[MAXN] = {0}, k = 0, x = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
      if (k == 0) { x = *p++ - 63; k = 6; } k--;
      if (x >> k & 1) { adj[i] |= 1 << j; adj[j] |= 1 << i; } }
    Gr g; build(&g, n, adj);
    int zh = zhat_of(&g), z2 = z2_of(&g), full = g.full, cut = 0, flag = 0;
    for (int v = 0; v < n && !nocut; v++) {
      int S = full & ~(1 << v);
      if (compmask(n, adj, S, __builtin_ctz(S)) == S) continue;
      cut = 1;
      while (S) { int C = compmask(n, adj, S, __builtin_ctz(S)); S &= ~C;
        int R2 = full & ~C & ~(1 << v);
        int a = z2_mask(n, adj, C | 1 << v) + z2_mask(n, adj, R2 | 1 << v);
        int b = z2_mask(n, adj, C) + z2_mask(n, adj, R2);
        if ((a > b ? a : b) - 1 != z2) flag = 1; } }
    printf("%s %d %d %d %d %d\n", line, n, zh, z2, cut, flag); fflush(stdout); }
  return 0; }
