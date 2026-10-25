"""
zhat_sage.py -- bounds on the maximum nullity M(G) of a graph, for use in a Sage worksheet.
(Works in plain Python too: it uses Sage for planarity / isomorphism when available and
falls back to networkx otherwise.)

    load("zhat_sage.py")                 # keep mr_table.json and hyb.c next to this file or in the cwd
    G = graphs.PetersenGraph()           # Sage Graph, networkx graph, or a graph6 string
    bounds(G)                            # {'lo','hi','M','lo_src','hi_src'}
    bounds(G, depth=2, oddcycle=True, uniquecover=True)      # stronger forcing variants
    summary(G)                           # every bound separately, with sources

UPPER bounds on M      : Z, Zhat (loop forcing), Schur forcing of depth k (optionally with the
                         odd-cycle rule and/or the unique-cover rule), pivot game PIV, diameter
                         (M <= n - diam), non-complete (M <= n-2), induced P4/fish/dart/K333
                         (M <= n-3), cut vertex formula, 2-separation formula.
LOWER bounds on M      : explicit matrices (nullity of A-dI, L-dI, Q-dI; registered matrices and
                         Gram certificates), not a path (M>=2), not outerplanar (M>=3), not planar
                         (M>=4), edge-clique-cover number c (M >= n-c), no induced P4/fish/dart/
                         K333 (M >= n-2), trees (M=Z), complete graphs, cut vertex formula,
                         2-separation formula, and the exact table for connected graphs with
                         at most 8 vertices (mr_table.json).
When lo == hi, M(G) is established.

All bounds are combined over components and through the cut vertex formula
  M(G) = max{M(G1)+M(G2), M(G1-v)+M(G2-v)} - 1
and through the 2-separation formula (van der Holst / Hsieh), applied to every 2-separation of G
with interval arithmetic on both sides.
"""
import itertools, json, os, subprocess, sys, tempfile, hashlib
from fractions import Fraction
from functools import lru_cache

try:
    import sage.all as _sage                       # noqa: F401
    from sage.graphs.graph import Graph as _SageGraph
    _SAGE = True
except Exception:
    _SAGE = False

def _bits(x): return bin(x).count("1")

# =====================================================================================
#  input handling
# =====================================================================================
def _adj(G):
    """-> (n, [neighbor sets]) with vertices relabeled 0..n-1.  Accepts Sage / networkx / graph6."""
    if isinstance(G, str):
        return _from_g6(G)
    if hasattr(G, "graph6_string") and hasattr(G, "vertices"):          # Sage
        V = list(G.vertices(sort=False)); edges = G.edges(labels=False, sort=False)
    else:                                                               # networkx
        V = list(G.nodes()); edges = G.edges()
    idx = {v: i for i, v in enumerate(V)}
    nb = [set() for _ in V]
    for a, b in edges:
        if a != b: nb[idx[a]].add(idx[b]); nb[idx[b]].add(idx[a])
    return len(V), nb

def _from_g6(s):
    s = s.strip(); n = ord(s[0]) - 63; nb = [set() for _ in range(n)]
    bits = []
    for ch in s[1:]:
        x = ord(ch) - 63
        bits.extend((x >> i) & 1 for i in range(5, -1, -1))
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]: nb[i].add(j); nb[j].add(i)
            k += 1
    return n, nb

def _to_g6(n, nb):
    bits = [1 if j in nb[i] else 0 for j in range(1, n) for i in range(j)]
    while len(bits) % 6: bits.append(0)
    out = chr(63 + n)
    for k in range(0, len(bits), 6):
        v = 0
        for b in bits[k:k + 6]: v = 2 * v + b
        out += chr(63 + v)
    return out

def _key(n, nb): return (n, tuple(tuple(sorted(s)) for s in nb))

def _induced(n, nb, S):
    S = sorted(S); ix = {v: i for i, v in enumerate(S)}
    return len(S), [{ix[w] for w in nb[v] if w in ix} for v in S]

def _components(n, nb, S=None):
    S = set(range(n)) if S is None else set(S); out = []
    while S:
        st = [S.pop()]; C = set(st)
        while st:
            u = st.pop()
            for w in nb[u]:
                if w in S: S.discard(w); C.add(w); st.append(w)
        out.append(C)
    return out

def _cut_vertices(n, nb):
    return [v for v in range(n) if len(_components(n, nb, set(range(n)) - {v})) > 1]

def _iso(n1, nb1, n2, nb2):
    if n1 != n2: return False
    if _SAGE:
        return _SageGraph({i: list(nb1[i]) for i in range(n1)}).is_isomorphic(_SageGraph({i: list(nb2[i]) for i in range(n2)}))
    import networkx as nx
    g1 = nx.Graph(); g1.add_nodes_from(range(n1)); g1.add_edges_from((a, b) for a in range(n1) for b in nb1[a] if a < b)
    g2 = nx.Graph(); g2.add_nodes_from(range(n2)); g2.add_edges_from((a, b) for a in range(n2) for b in nb2[a] if a < b)
    return nx.is_isomorphic(g1, g2)

def _is_planar(n, nb):
    if n < 5: return True
    if _SAGE:
        return bool(_SageGraph({i: list(nb[i]) for i in range(n)}).is_planar())
    import networkx as nx
    g = nx.Graph(); g.add_nodes_from(range(n)); g.add_edges_from((a, b) for a in range(n) for b in nb[a] if a < b)
    return nx.check_planarity(g)[0]

def _is_outerplanar(n, nb):
    """outerplanar iff G plus a vertex joined to everything is planar"""
    nb2 = [set(s) | {n} for s in nb] + [set(range(n))]
    return _is_planar(n + 1, nb2)

# =====================================================================================
#  standard and loop zero forcing
# =====================================================================================
def _zf_closure(nb, S):
    S = set(S); ch = True
    while ch:
        ch = False
        for u in list(S):
            w = nb[u] - S
            if len(w) == 1: S |= w; ch = True
    return S

def _Z_conn(n, nb):
    for k in range(n + 1):
        for B in itertools.combinations(range(n), k):
            if len(_zf_closure(nb, B)) == n: return k

def _loop_le(n, nb, L, k):
    if k >= n: return True
    if k < 0: return False
    hood = [nb[u] | ({u} if u in L else set()) for u in range(n)]
    for B in itertools.combinations(range(n), k):
        S = set(B); ch = True
        while ch:
            ch = False
            for h in hood:
                w = h - S
                if len(w) == 1: S |= w; ch = True
        if len(S) == n: return True
    return False

def _Zhat_conn(n, nb):
    best = 0
    for r in range(n + 1):
        for L in itertools.combinations(range(n), r):
            L = set(L)
            while not _loop_le(n, nb, L, best): best += 1
    return best

def _sum_components(f, n, nb, *a):
    return sum(f(*_induced(n, nb, C), *a) for C in _components(n, nb))

def Z(G):
    """Standard zero forcing number."""
    n, nb = _adj(G); return _sum_components(_Z_conn, n, nb)

def Zhat(G):
    """Enhanced (loop) zero forcing number."""
    n, nb = _adj(G); return _sum_components(_Zhat_conn, n, nb)

# =====================================================================================
#  depth-k Schur forcing  (port of the project's hyb.c, readable Python)
# =====================================================================================
#  For a loop set L, A[U] nonsingular with U a connected set of looped vertices (|U| <= k),
#  and z in N(U)-U, the Schur row rho_{U,z} has entries: 0 on U; status nu(U+z) at z;
#  status pi(U;z,t) at t in N(U)-U-z; a_zt elsewhere.  A seed forces with ordinary rows
#  and every available Schur row: a row with exactly one white column carrying a nonzero
#  entry colors that column.  Statuses are decided lazily by the adversary.
#  Optional extra rules (hyb.c): oddcycle -- a white component that is an induced odd cycle
#  with no loops is colored; uniquecover -- a white component whose spanning covers by loops,
#  edges and cycles are unique (so det A[C] is a nonzero monomial) is colored.
class _Deep:
    def __init__(self, n, nb, k, oc, uc, anyU):
        self.n, self.k, self.oc, self.uc, self.anyU = n, k, oc, uc, anyU
        self.adj = [sum(1 << w for w in nb[u]) for u in range(n)]
        self.full = (1 << n) - 1
        self._seeds = {}
    def seeds(self, r):
        if r not in self._seeds:
            self._seeds[r] = [sum(1 << i for i in c) for c in itertools.combinations(range(self.n), r)]
        return self._seeds[r]
    def nbrs(self, S):
        m = 0
        for u in range(self.n):
            if S >> u & 1: m |= self.adj[u]
        return m & ~S
    # ---- unique cover / odd cycle ------------------------------------------------
    def isoddcycle(self, C):
        k = _bits(C)
        if k < 3 or not k & 1 or C & self.L: return False
        return all(_bits(self.adj[u] & C) == 2 for u in range(self.n) if C >> u & 1)
    def ccount(self, W):
        if W == 0: return 1
        if W in self._cc: return self._cc[W]
        adj, L, n = self.adj, self.L, self.n
        u = (W & -W).bit_length() - 1; r = 0
        if L >> u & 1: r += self.ccount(W & ~(1 << u))
        for v in range(n):
            if r >= 2: break
            if (adj[u] & W) >> v & 1: r += self.ccount(W & ~(1 << u) & ~(1 << v))
        if r < 2: r += self._cycles(u, W)
        r = min(r, 2); self._cc[W] = r; return r
    def _cycles(self, start, W):
        adj = self.adj; n = self.n; acc = [0]
        def dfs(last, path, length, second):
            if acc[0] >= 2: return
            for v in range(n):
                if not ((W >> v & 1) and (adj[last] >> v & 1)): continue
                if v == start and length >= 3 and last > second:
                    acc[0] += self.ccount(W & ~path)
                    if acc[0] >= 2: return
                    continue
                if path >> v & 1: continue
                if v < start: continue
                dfs(v, path | 1 << v, length + 1, v if length == 1 else second)
        dfs(start, 1 << start, 1, -1)
        return acc[0]
    def ucfire(self, S):
        Wt = self.full & ~S; T = S; adj = self.adj
        while Wt:
            C = Wt & -Wt
            while True:
                o = C
                for u in range(self.n):
                    if C >> u & 1: C |= adj[u] & Wt
                if C == o: break
            Wt &= ~C
            if (self.oc and self.isoddcycle(C)) or (self.uc and self.ccount(C) == 1): T |= C
        return T
    # ---- plain loop closure (with the optional rules) ----------------------------
    def lclose(self, S, rules=True):
        adj, L, full = self.adj, self.L, self.full; ch = True
        while ch and S != full:
            ch = False
            for u in range(self.n):
                w = (adj[u] | ((L >> u & 1) << u)) & ~S
                if w and not w & (w - 1): S |= w; ch = True
            if not ch and S != full and rules and (self.oc or self.uc):
                T = self.ucfire(S)
                if T != S: S = T; ch = True
        return S
    # ---- statuses and rows -------------------------------------------------------
    def build(self):
        n, L, adj, full = self.n, self.L, self.adj, self.full
        self.NS = 0; nucache = {}
        def nu(W):
            c = _bits(W)
            if c == 1: return -1 if L & W else -3
            if c == 2 and W & ~L: return -1
            if W not in nucache: nucache[W] = self.NS; self.NS += 1
            return nucache[W]
        allowed = full if self.anyU else L
        sets = [1 << u for u in range(n) if allowed >> u & 1] if self.k > 0 else []
        lo = 0
        for _ in range(self.k - 1):
            hi = len(sets); seen = set()
            for i in range(lo, hi):
                ext = self.nbrs(sets[i]) & allowed
                for u in range(n):
                    if ext >> u & 1:
                        W = sets[i] | 1 << u
                        if W not in seen: seen.add(W); sets.append(W)
            lo = hi
        rows = []     # (U, nuU, Dm, cols[(vertex, status)])
        for z in range(n): rows.append((0, -1, adj[z] | ((L >> z & 1) << z), []))
        for U in sets:
            nuU = nu(U); NU = self.nbrs(U)
            if nuU == -3: continue
            pi = {}
            for z in range(n):
                if not NU >> z & 1: continue
                Dm = adj[z] & ~NU & ~U; cols = []
                s = nu(U | 1 << z)
                if s == -1: Dm |= 1 << z
                elif s >= 0: cols.append((z, s))
                for t in range(n):
                    if NU >> t & 1 and t != z:
                        if _bits(U) == 1 and not adj[z] >> t & 1: Dm |= 1 << t; continue
                        key = (min(z, t), max(z, t))
                        if key not in pi: pi[key] = self.NS; self.NS += 1
                        cols.append((t, pi[key]))
                rows.append((U, nuU, Dm, cols))
        self.rows = rows
    def val(self, code, a):
        return 1 if code == -1 else 0 if code == -3 else a[code]
    def closeS(self, S, a):
        full = self.full; ch = True
        while ch and S != full:
            ch = False
            for U, nuU, Dm, cols in self.rows:
                if nuU != -1 and self.val(nuU, a) != 1: continue
                W = full & ~S & ~U
                nz = Dm & W; cnt = _bits(nz); und = 0; tgt = nz
                if cnt > 1: continue
                for (c, s) in cols:
                    if cnt > 1: break
                    if W >> c & 1:
                        v = a[s]
                        if v == 1: cnt += 1; tgt = 1 << c
                        elif v == -1: und += 1
                if cnt == 1 and not und: S |= tgt; ch = True
            if not ch and S != full and (self.oc or self.uc):
                T = self.ucfire(S)
                if T != S: S = T; ch = True
        return S
    def works(self, S, a):
        S = self.closeS(S, a)
        if S == self.full: return True
        br = -1
        for U, nuU, Dm, cols in self.rows:
            W = self.full & ~S & ~U; cnt = _bits(Dm & W); firstund = -1
            if cnt > 1: continue
            for (c, s) in cols:
                if W >> c & 1:
                    v = a[s]
                    if v == 1: cnt += 1
                    elif v == -1 and firstund < 0: firstund = s
            if cnt > 1: continue
            if nuU >= 0 and a[nuU] == -1:
                if cnt == 1 or firstund >= 0: br = nuU; break
                continue
            if nuU >= 0 and a[nuU] == 0: continue
            if firstund >= 0: br = firstund; break
        if br < 0: return False
        self.Q.add(br)
        a[br] = 1; ok = self.works(S, a)
        if ok: a[br] = 0; ok = self.works(S, a)
        a[br] = -1; return ok
    def covered(self, k, a):
        q = set()
        for S in self.seeds(k):
            self.Q = set()
            if self.works(S, a): return True
            q |= self.Q
        e = next((s for s in sorted(q) if a[s] == -1), None)
        if e is None: return False
        a[e] = 1; ok = self.covered(k, a)
        if ok: a[e] = 0; ok = self.covered(k, a)
        a[e] = -1; return ok
    def le(self, k):
        """is the depth-k forcing number of (G, L) <= k ?"""
        if k >= self.n: return True
        self._cc = {}
        for S in self.seeds(k):
            if self.lclose(S) == self.full: return True
        self.build()
        return self.covered(k, [-1] * self.NS)
    def value(self):
        best = 0
        for L in range(1 << self.n):
            self.L = L
            while not self.le(best): best += 1
        return best

def _deep_py(n, nb, k, oc, uc, anyU):
    if n == 0: return 0
    return _Deep(n, nb, k, oc, uc, anyU).value()

# ---- optional compiled backend ----------------------------------------------------
_CBIN = {}
def _find_c_source():
    dirs = [os.environ.get("ZHAT_C_DIR", ""), os.getcwd()]
    try: dirs.append(os.path.dirname(os.path.abspath(__file__)))
    except NameError: pass
    for d in dirs:
        if d and os.path.exists(os.path.join(d, "hyb.c")): return os.path.join(d, "hyb.c")
    return None

def c_backend():
    """Path of the compiled hyb binary (compiled on first use), or None."""
    if "bin" in _CBIN: return _CBIN["bin"]
    path = None
    src = _find_c_source()
    if src:
        h = hashlib.md5(open(src, "rb").read()).hexdigest()[:10]
        out = os.path.join(tempfile.gettempdir(), "zhat_hyb_" + h)
        if not os.path.exists(out):
            try: subprocess.run(["gcc", "-O2", "-o", out, src], check=True, capture_output=True)
            except Exception: out = None
        path = out
    _CBIN["bin"] = path
    return path

def _deep_c(n, nb, k, oc, uc, anyU):
    binp = c_backend()
    env = dict(os.environ)
    for name in ("UC", "OC", "ANYU", "FREE", "NOTAU"): env.pop(name, None)
    if oc: env["OC"] = "1"
    if uc: env["UC"] = "1"
    if anyU: env["ANYU"] = "1"
    r = subprocess.run([binp, str(k), "nocut"], input=_to_g6(n, nb) + "\n", env=env,
                       capture_output=True, text=True, check=True)
    return int(r.stdout.split()[3])

def _deep_conn(n, nb, k, oc, uc, anyU, backend):
    if n <= 1: return n
    use_c = backend == "c" or (backend == "auto" and n >= 7 and c_backend() is not None)
    if use_c:
        if c_backend() is None: raise RuntimeError("C backend requested but hyb.c / gcc not found")
        if n <= 16: return _deep_c(n, nb, k, oc, uc, anyU)
    return _deep_py(n, nb, k, oc, uc, anyU)

def ZhatS(G, depth=1, oddcycle=False, uniquecover=False, anyU=False, backend="auto"):
    """Schur forcing number of the given depth (depth=1 is the paper's Zhat_S; depth=0 is Zhat).
    oddcycle / uniquecover switch on the extra cover rules.  M(G) <= value.
    backend: 'auto' (compiled hyb.c when found and n >= 7), 'c', or 'python'."""
    n, nb = _adj(G)
    return _sum_components(_deep_conn, n, nb, depth, oddcycle, uniquecover, anyU, backend)

# =====================================================================================
#  pivot game
# =====================================================================================
def _PIV_conn(n, nb, deg=2):
    V = frozenset(range(n))
    E = frozenset((a, b) for a in range(n) for b in nb[a] if a < b)
    @lru_cache(maxsize=None)
    def le(V, E, L, k):
        if k < 0: return False
        nbm = {u: set() for u in V}
        for a, b in E: nbm[a].add(b); nbm[b].add(a)
        vl = sorted(V); idx = {u: i for i, u in enumerate(vl)}
        nb2 = [{idx[w] for w in nbm[u]} for u in vl]
        if _loop_le(len(vl), nb2, {idx[u] for u in L}, k): return True
        for y in sorted(L):
            nbr = sorted(nbm[y])
            if len(nbr) > deg: continue
            V2 = V - {y}; E2 = {e for e in E if y not in e}; L2 = L - {y}
            free = [('loop', u) for u in nbr]
            for u, w in itertools.combinations(nbr, 2):
                e = (u, w)
                if e in E: free.append(('edge', e))
                else: E2 = E2 | {e}
            ok = True
            for choice in itertools.product([0, 1], repeat=len(free)):
                Ec, Lc = set(E2), set(L2)
                for (kind, it), c in zip(free, choice):
                    if kind == 'loop': (Lc.add if c else Lc.discard)(it)
                    else: (Ec.add if c else Ec.discard)(it)
                if not le(V2, frozenset(Ec), frozenset(Lc), k): ok = False; break
            if ok: return True
        return False
    b = 0
    for r in range(n + 1):
        for L in itertools.combinations(range(n), r):
            while not le(V, E, frozenset(L), b): b += 1
    return b

def PIV(G, deg=2):
    """Pivot game value (pivots at looped vertices of degree <= deg).  M(G) <= PIV(G)."""
    n, nb = _adj(G); return _sum_components(_PIV_conn, n, nb, deg)

# =====================================================================================
#  exact matrix lower bounds
# =====================================================================================
def _rank(M):
    M = [[Fraction(x) for x in row] for row in M]; r = 0
    rows, cols = len(M), len(M[0]) if M else 0
    for c in range(cols):
        p = next((i for i in range(r, rows) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        for i in range(r + 1, rows):
            if M[i][c] != 0:
                f = M[i][c] / M[r][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    return r

def nullity(M): return len(M) - _rank(M)

def check_matrix(G, A):
    """Exact check that the symmetric matrix A has graph G (diagonal unrestricted); returns its nullity."""
    n, nb = _adj(G)
    A = [[A[i][j] for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(i):
            if A[i][j] != A[j][i]: raise ValueError("not symmetric")
            if (A[i][j] != 0) != (j in nb[i]): raise ValueError("pattern differs from G at (%d,%d)" % (i, j))
    return nullity(A)

_REG = {}
def register_matrix(G, A):
    """Verify that A has graph G and store its nullity as a lower bound for M(G)."""
    n, nb = _adj(G); k = check_matrix(G, A); key = _key(n, nb)
    if _REG.get(key, (-1,))[0] < k: _REG[key] = (k, "registered matrix")
    return k

def gram_matrix(V, D):
    V = [[int(x) for x in row] for row in V]; r, n = len(V), len(V[0])
    return [[sum(int(D[k]) * V[k][i] * V[k][j] for k in range(r)) for j in range(n)] for i in range(n)]

def register_gram(G, V, D=None):
    """Register the Gram matrix V^T diag(D) V (rank <= rows of V) after checking its graph is G."""
    return register_matrix(G, gram_matrix(V, D or [1] * len(V)))

def _spectral_lower(n, nb):
    deg = [len(s) for s in nb]
    A = [[1 if j in nb[i] else 0 for j in range(n)] for i in range(n)]
    mats = {'A': A,
            'L': [[(deg[i] if i == j else -A[i][j]) for j in range(n)] for i in range(n)],
            'Q': [[(deg[i] if i == j else A[i][j]) for j in range(n)] for i in range(n)]}
    best, src = 0, None
    for name, M in mats.items():
        for d in range(-n, n + 1):
            k = nullity([[M[i][j] - (d if i == j else 0) for j in range(n)] for i in range(n)])
            if k > best: best, src = k, "nullity of %s - %dI" % (name, d)
    return best, src

# =====================================================================================
#  graph-theoretic bounds from the literature
# =====================================================================================
_FORBIDDEN = None
def _forbidden_patterns():
    """induced subgraphs forcing mr >= 3 (M <= n-3): P4, dart, fish (atlas graphs 14, 34, 40 of the
    minimum-rank catalog) and K_{3,3,3}.  Given as edge lists."""
    global _FORBIDDEN
    if _FORBIDDEN is None:
        pats = [(4, [(0, 1), (0, 3), (1, 2)]),                                   # P4
                (5, [(0, 4), (1, 4), (2, 3), (2, 4), (3, 4)]),                   # atlas 34
                (5, [(0, 1), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4)])]           # atlas 40
        out = []
        for m, E in pats:
            nbp = [set() for _ in range(m)]
            for a, b in E: nbp[a].add(b); nbp[b].add(a)
            perms = set()
            for p in itertools.permutations(range(m)):
                perms.add(frozenset(frozenset((p[a], p[b])) for a, b in E))
            out.append((m, perms))
        _FORBIDDEN = out
    return _FORBIDDEN

def _has_forbidden(n, nb):
    for m, perms in _forbidden_patterns():
        if n < m: continue
        for S in itertools.combinations(range(n), m):
            es = frozenset(frozenset((i, j)) for i, j in itertools.combinations(range(m), 2) if S[j] in nb[S[i]])
            if es in perms: return True
    if n >= 9:                                      # K_{3,3,3}: complement of three disjoint triangles
        for S in itertools.combinations(range(n), 9):
            Ss = set(S)
            if all(len(nb[u] & Ss) == 6 for u in S):
                comp = {u: Ss - nb[u] - {u} for u in S}
                if all(comp[u] | {u} == comp[next(iter(comp[u]))] | {next(iter(comp[u]))} for u in S):
                    return True
    return False

def _edge_clique_cover_number(n, nb):
    """minimum number of cliques covering all edges (exact set cover over maximal cliques)"""
    edges = [(a, b) for a in range(n) for b in nb[a] if a < b]
    if not edges: return 0
    eid = {e: i for i, e in enumerate(edges)}
    cliques = []
    def bk(R, P, X):
        if not P and not X: cliques.append(sorted(R)); return
        piv = max(P | X, key=lambda u: len(nb[u] & P))
        for v in list(P - nb[piv]):
            bk(R | {v}, P & nb[v], X & nb[v]); P = P - {v}; X = X | {v}
    bk(set(), set(range(n)), set())
    masks = []
    for c in cliques:
        m = 0
        for a, b in itertools.combinations(c, 2): m |= 1 << eid[(a, b)]
        masks.append(m)
    full = (1 << len(edges)) - 1
    best = [len(masks)]
    def rec(cov, used):
        if used >= best[0]: return
        if cov == full: best[0] = used; return
        e = next(i for i in range(len(edges)) if not cov >> i & 1)
        for m in sorted((m for m in masks if m >> e & 1), key=lambda m: -bin(m & ~cov).count("1")):
            rec(cov | m, used + 1)
    rec(0, 0)
    return best[0]

def _diameter(n, nb):
    d = 0
    for s in range(n):
        dist = {s: 0}; fr = [s]
        while fr:
            nf = []
            for u in fr:
                for w in nb[u]:
                    if w not in dist: dist[w] = dist[u] + 1; nf.append(w)
            fr = nf
        d = max(d, max(dist.values()))
    return d

def _is_tree(n, nb): return sum(len(s) for s in nb) == 2 * (n - 1) and len(_components(n, nb)) == 1
def _is_path(n, nb): return _is_tree(n, nb) and all(len(s) <= 2 for s in nb)
def _is_complete(n, nb): return all(len(s) == n - 1 for s in nb)

# ---- exact table for connected graphs with <= 8 vertices ----------------------------
_TABLE = {}
def load_table(path=None):
    """Load mr_table.json (connected graphs on <= 8 vertices -> maximum nullity)."""
    if path is None:
        dirs = [os.environ.get("ZHAT_TABLE_DIR", ""), os.getcwd()]
        try: dirs.append(os.path.dirname(os.path.abspath(__file__)))
        except NameError: pass
        for d in dirs:
            if d and os.path.exists(os.path.join(d, "mr_table.json")): path = os.path.join(d, "mr_table.json"); break
    _TABLE.clear()
    if path is None: _TABLE["buckets"] = None; return False
    buckets = {}
    for g6, M in json.load(open(path)).items():
        n, nb = _from_g6(g6)
        buckets.setdefault(_inv(n, nb), []).append((n, nb, M))
    _TABLE["buckets"] = buckets
    return True

def _inv(n, nb):
    d = [len(s) for s in nb]
    return (n, sum(d), tuple(sorted(d)), tuple(sorted(tuple(sorted(d[w] for w in nb[u])) for u in range(n))))

def _table_lookup(n, nb):
    if n > 8: return None
    if "buckets" not in _TABLE: load_table()
    if _TABLE["buckets"] is None: return None
    for (m, nb2, M) in _TABLE["buckets"].get(_inv(n, nb), []):
        if _iso(n, nb, m, nb2): return M
    return None

# =====================================================================================
#  2-separation formula
# =====================================================================================
def _mr_interval(n, nb, opts, cache_only=False):
    """interval for the minimum rank mr = n - M of an arbitrary graph, from the M bounds"""
    lo, hi = _bounds(n, nb, opts, depth=1)[:2]
    return n - hi, n - lo

def _twosep(n, nb, opts):
    """Apply the 2-separation formula to every 2-separation {r1,r2} | A | B of G.  Returns the
    best M-interval (lo, hi, src) obtainable, or None.
       mr(G) = min{ mr(G1)+mr(G2), mr(H1)+mr(H2), mr(G1/r)+mr(G2/r)+2,
                    mr(G1-r1)+mr(G2-r1)+2, mr(G1-r2)+mr(G2-r2)+2, mr(G1-R)+mr(G2-R)+4 }
    where G1 = G[A+R] without the edge r1r2, G2 = G[B+R], H1 = G1+r1r2, H2 = G2 with the edge
    r1r2 present or absent when G has it (present when G lacks it), G_i/r merges r1,r2 and
    may delete any subset of the doubled edges."""
    best_lo, best_hi, src = -10**9, 10**9, None
    for r1, r2 in itertools.combinations(range(n), 2):
        rest = set(range(n)) - {r1, r2}
        comps = _components(n, nb, rest)
        if len(comps) < 2: continue
        has_edge = r2 in nb[r1]
        first = comps[0]
        for mask in range(1, 1 << (len(comps) - 1)):
            pass
        # all ordered bipartitions of the components into (A, B)
        for mask in range(1, (1 << len(comps)) - 1):
            A = set().union(*[comps[i] for i in range(len(comps)) if mask >> i & 1])
            B = rest - A
            lo_mr, hi_mr = _twosep_one(n, nb, opts, r1, r2, A, B, has_edge)
            lo, hi = n - hi_mr, n - lo_mr
            if lo > best_lo: best_lo = lo
            if hi < best_hi: best_hi = hi; src = "2-separation at {%d,%d}" % (r1, r2)
            if best_lo == best_hi: return best_lo, best_hi, src
    if src is None: return None
    return best_lo, best_hi, src

def _piece(n, nb, S, drop_edge=None, add_edge=None):
    """induced subgraph on the vertex set S (a sorted list) with an edge removed/added; returns (n', nb', index map)"""
    S = sorted(S); ix = {v: i for i, v in enumerate(S)}
    nb2 = [{ix[w] for w in nb[v] if w in ix} for v in S]
    return len(S), nb2, ix

def _mr_of(n, nb, opts):
    return _mr_interval(n, nb, opts)

def _twosep_one(n, nb, opts, r1, r2, A, B, has_edge):
    R = {r1, r2}
    def sub(S, edge):                      # edge in {None,'drop','add'}
        n2, nb2, ix = _piece(n, nb, sorted(S))
        a, b = ix[r1], ix[r2]
        if edge == 'drop': nb2[a].discard(b); nb2[b].discard(a)
        if edge == 'add': nb2[a].add(b); nb2[b].add(a)
        return n2, nb2, ix
    def mr(n2, nb2): return _mr_interval(n2, nb2, opts)
    def add(x, y, c=0): return (x[0] + y[0] + c, x[1] + y[1] + c)
    G1 = sub(A | R, 'drop'); G2 = sub(B | R, None)
    terms = []
    terms.append(add(mr(*G1[:2]), mr(*G2[:2])))
    H1 = sub(A | R, 'add')
    H2opts = [sub(B | R, 'add')] if not has_edge else [sub(B | R, None), sub(B | R, 'drop')]
    h2 = mr(*H2opts[0][:2])
    for h in H2opts[1:]:
        x = mr(*h[:2]); h2 = (min(h2[0], x[0]), min(h2[1], x[1]))
    terms.append(add(mr(*H1[:2]), h2))
    # merge r1 and r2
    def merged(S, edge):
        n2, nb2, ix = sub(S, edge)
        a, b = ix[r1], ix[r2]
        doubles = sorted((nb2[a] & nb2[b]) - {a, b})
        keep = [v for v in range(n2) if v != b]
        ixm = {v: i for i, v in enumerate(keep)}
        base = [set() for _ in keep]
        for v in keep:
            for w in nb2[v]:
                if w == b: w2 = a
                else: w2 = w
                if v == a or w2 == a or True:
                    pass
        # adjacency of the merged graph
        nbm = [set() for _ in keep]
        for v in range(n2):
            for w in nb2[v]:
                v2 = a if v == b else v; w2 = a if w == b else w
                if v2 != w2: nbm[ixm[v2]].add(ixm[w2]); nbm[ixm[w2]].add(ixm[v2])
        res = None
        dm = [ixm[d] for d in doubles]
        for sub_mask in range(1 << len(dm)):
            nbc = [set(s) for s in nbm]
            for i, d in enumerate(dm):
                if sub_mask >> i & 1: nbc[ixm[a]].discard(d); nbc[d].discard(ixm[a])
            x = mr(len(keep), nbc)
            res = x if res is None else (min(res[0], x[0]), min(res[1], x[1]))
        return res
    terms.append(add(merged(A | R, 'drop'), merged(B | R, None), 2))
    for r in (r1, r2):
        P1 = sub(A | R, 'drop'); P2 = sub(B | R, None)
        def minus(P, rr):
            n2, nb2, ix = P
            S = [v for v in range(n2) if v != ix[rr]]
            m, nbm, _ = _piece(n2, nb2, S)
            return mr(m, nbm)
        terms.append(add(minus(P1, r), minus(P2, r), 2))
    def minusR(S):
        m, nbm, _ = _piece(n, nb, sorted(S)); return mr(m, nbm)
    terms.append(add(minusR(A), minusR(B), 4))
    return min(t[0] for t in terms), min(t[1] for t in terms)

# =====================================================================================
#  combining everything
# =====================================================================================
_CACHE = {}
_REG_KEYS = None

def _opts(depth, oddcycle, uniquecover, anyU, backend, use, twosep, table):
    return (depth, bool(oddcycle), bool(uniquecover), bool(anyU), backend, tuple(sorted(use)), bool(twosep), bool(table))

def _bounds(n, nb, opts, depth=0, top_table=True):
    key = (_key(n, nb), opts, top_table)
    if key in _CACHE: return _CACHE[key]
    d, oc, uc, anyU, backend, use, twosep, table = opts
    comps = _components(n, nb)
    if n == 0:
        res = (0, 0, "empty", "empty")
    elif len(comps) > 1:
        parts = [_bounds(*_induced(n, nb, C), opts, depth + 1) for C in comps]
        res = (sum(p[0] for p in parts), sum(p[1] for p in parts), "sum over components", "sum over components")
    elif n <= 2:
        res = (1, 1, "K1/K2", "K1/K2")
    else:
        res = _bounds_conn(n, nb, opts, depth, top_table)
    _CACHE[key] = res
    return res

def _bounds_conn(n, nb, opts, depth, top_table):
    dk, oc, uc, anyU, backend, use, twosep, table = opts
    lo, lo_s, hi, hi_s = 0, "trivial", n - 1, "n-1"
    state = {'lo': lo, 'lo_s': lo_s, 'hi': hi, 'hi_s': hi_s}
    def up(v, s):
        if v < state['hi']: state['hi'], state['hi_s'] = v, s
    def dn(v, s):
        if v > state['lo']: state['lo'], state['lo_s'] = v, s
    def done(): return state['lo'] >= state['hi']
    def out(): return (state['lo'], state['hi'], state['lo_s'], state['hi_s'])
    # exact table
    if table and (top_table or depth > 0):
        M = _table_lookup(n, nb)
        if M is not None: return (M, M, "exact table (n<=8)", "exact table (n<=8)")
    if _is_complete(n, nb): return (n - 1, n - 1, "K_n", "K_n")
    if _is_path(n, nb): return (1, 1, "path", "path")
    z = _Z_conn(n, nb); up(z, "Z")
    if _is_tree(n, nb): return (z, z, "tree: M = Z", "tree: M = Z")
    up(n - 2, "not complete: M <= n-2")
    up(n - _diameter(n, nb), "diameter")
    dn(2, "not a path")
    reg = _REG.get(_key(n, nb))
    if reg: dn(*reg)
    if not done():
        if not _is_outerplanar(n, nb):
            dn(3, "not outerplanar")
            if not _is_planar(n, nb): dn(4, "not planar")
    if not done(): dn(n - _edge_clique_cover_number(n, nb), "edge clique cover")
    if not done():
        if _has_forbidden(n, nb): up(n - 3, "induced P4/fish/dart/K333")
        else: dn(n - 2, "no induced P4/fish/dart/K333")
    if not done():
        v, s = _spectral_lower(n, nb); dn(v, s)
    # cut vertex formula
    for v in _cut_vertices(n, nb):
        if done(): break
        rest = set(range(n)) - {v}
        C = _components(n, nb, rest)[0]; other = rest - C
        P = [_bounds(*_induced(n, nb, S), opts, depth + 1) for S in (C | {v}, other | {v}, C, other)]
        dn(max(P[0][0] + P[1][0], P[2][0] + P[3][0]) - 1, "cut vertex formula at %d" % v)
        up(max(P[0][1] + P[1][1], P[2][1] + P[3][1]) - 1, "cut vertex formula at %d" % v)
    if not done() and twosep:
        r = _twosep(n, nb, opts)
        if r:
            if r[0] > state['lo']: state['lo'], state['lo_s'] = r[0], r[2]
            if r[1] < state['hi']: state['hi'], state['hi_s'] = r[1], r[2]
    # forcing parameters, cheapest first
    for name in ("Zhat", "Schur", "PIV"):
        if done(): break
        if name not in use: continue
        if name == "Zhat": h = _Zhat_conn(n, nb); s = "Zhat"
        elif name == "Schur":
            h = _deep_conn(n, nb, dk, oc, uc, anyU, backend)
            s = "Schur depth %d%s%s" % (dk, " +odd cycle" if oc else "", " +unique cover" if uc else "")
        else: h = _PIV_conn(n, nb, 2); s = "PIV"
        up(h, s)
    return out()

def bounds(G, depth=1, oddcycle=False, uniquecover=False, anyU=False, backend="auto",
           use=("Zhat", "Schur", "PIV"), twosep=True, table=True):
    """lo <= M(G) <= hi.  'M' holds the value when lo == hi (else None).
    depth/oddcycle/uniquecover/anyU configure the Schur forcing bound; backend is 'auto', 'c' or 'python';
    use selects which forcing bounds to try; twosep switches the 2-separation formula; table switches
    the exact table for graphs with <= 8 vertices."""
    n, nb = _adj(G)
    lo, hi, ls, hs = _bounds(n, nb, _opts(depth, oddcycle, uniquecover, anyU, backend, use, twosep, table))
    return {'lo': lo, 'hi': hi, 'M': lo if lo == hi else None, 'lo_src': ls, 'hi_src': hs}

def summary(G, depth=1, oddcycle=False, uniquecover=False, anyU=False, backend="auto"):
    """Print each upper bound separately, then the combined result."""
    n, nb = _adj(G)
    print("n =", n)
    print("Z =", Z(G), " Zhat =", Zhat(G),
          " Schur(depth %d%s%s) =" % (depth, ",oddcycle" if oddcycle else "", ",uniquecover" if uniquecover else ""),
          ZhatS(G, depth, oddcycle, uniquecover, anyU, backend), " PIV =", PIV(G))
    print(bounds(G, depth, oddcycle, uniquecover, anyU, backend))

if __name__ == "__main__":
    for s in sys.argv[1:]: print(s, bounds(s))
