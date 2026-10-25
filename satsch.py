"""Depth-k Schur forcing by SAT.

For a graph G, loop set L, depth k and threshold b, decide whether some status
assignment makes every seed of size b fail; then the depth-k value at L is > b.

A seed B fails exactly when some nonempty set F of vertices outside B is a
*fort* of the configuration: every available row meets F in 0 or at least 2
of its support positions.  (The final white set of a failed closure is such a
set; conversely a fort disjoint from B can never lose its first vertex.)

Rows:  row z of A (support N(z) + loop);  for each connected pivot set U with
|U| <= k (U inside L unless anyU) and det A[U] possibly nonzero, and each
z in N(U) - U, the Schur row rho_{U,z}: zero on U; at z the status
nu(U+z); at t in N(U) - U - z the status pi(U;z,t) (definitely nonzero when
|U| = 1 and zt is not an edge); elsewhere a_zt.  Definite cases: nu of a
singleton is its loop; nu of a 2-set with an unlooped vertex is nonzero.
"""
import itertools, sys
import networkx as nx
from pysat.solvers import Cadical153

TRUE, FALSE = 'T', 'F'

def connected_sets(G, k, allowed):
    out = set(frozenset([u]) for u in allowed)
    frontier = set(out)
    for _ in range(k - 1):
        new = set()
        for S in frontier:
            for u in set().union(*(G[x] for x in S)) - S:
                if u in allowed: new.add(S | {u})
        new -= out; out |= new; frontier = new
    return out

import sympy as sp
_SYM = {}
def minor_class(G, L, R, C):
    """'0' if det A[R,C] vanishes for every matrix with graph G and loops L,
    '1' if it is a single monomial (so never zero), else None."""
    key = (frozenset(frozenset(e) for e in G.edges()), frozenset(L), tuple(R), tuple(C))
    if key in _SYM: return _SYM[key]
    def ent(i, j):
        if i == j: return sp.Symbol('d%s' % (i,)) if i in L else 0
        if not G.has_edge(i, j): return 0
        a, b = sorted((i, j), key=str); return sp.Symbol('e%s_%s' % (a, b))
    M = sp.Matrix([[ent(i, j) for j in C] for i in R])
    p = sp.expand(M.det(method='berkowitz'))
    res = '0' if p == 0 else ('1' if len(sp.Add.make_args(p)) == 1 else None)
    _SYM[key] = res; return res

_LAST = [None]
def build(G, L, k, anyU, dj=False, extra=None, symb=False):
    ck = (id(G), frozenset(L))
    if _LAST[0] != ck: _SYM.clear(); _LAST[0] = ck
    V = list(G); var = {}
    def v(key):
        if key not in var: var[key] = len(var) + 1
        return var[key]
    def nu(W):
        W = frozenset(W)
        if len(W) == 1: return TRUE if next(iter(W)) in L else FALSE
        if len(W) == 2 and not W <= L: return TRUE
        if symb:
            c = minor_class(G, L, sorted(W, key=str), sorted(W, key=str))
            if c == '0': return FALSE
            if c == '1': return TRUE
        return v(('nu', W))
    def pi(U, z, t):
        if symb:
            R = sorted(U, key=str) + [z]; C = sorted(U, key=str) + [t]
            c = minor_class(G, L, R, C)
            if c == '0': return FALSE
            if c == '1': return TRUE
        return v(('pi', U, frozenset((z, t))))
    rows = []   # (guard, {column: literal or TRUE})
    for z in V:
        sup = {t: TRUE for t in G[z]}
        if z in L: sup[z] = TRUE
        rows.append((TRUE, sup))
    allowed = set(V) if anyU else set(L)
    piv = {}
    for U in connected_sets(G, k, allowed):
        g = nu(U)
        if g == FALSE: continue
        NU = set().union(*(G[x] for x in U)) - U
        for z in NU:
            sup = {}
            e = nu(U | {z})
            if e != FALSE: sup[z] = e
            for t in NU - {z}:
                if len(U) == 1 and not G.has_edge(z, t): e2 = TRUE
                else: e2 = pi(U, z, t)
                piv[(U, frozenset((z, t)))] = e2
                if e2 != FALSE: sup[t] = e2
            for t in set(G[z]) - NU - U - {z}:
                sup[t] = TRUE
            rows.append((g, sup))
    if dj and extra is not None:
        # Desnanot-Jacobi: det[U] det[U+z+t] = det[U+z] det[U+t] - det[U+z,U+t]^2
        def lit(x): return x
        for (U, zt), E in piv.items():
            z, t = tuple(zt)
            X, Y, P, Q = nu(U), nu(U | {z, t}), nu(U | {z}), nu(U | {t})
            extra.extend(dj_clauses(X, Y, P, Q, E))
    return V, var, v, rows

def dj_clauses(X, Y, P, Q, E):
    """Clauses for x*y = p*q - e^2 over the reals, on zero/nonzero indicators.
    Literals are ints or TRUE/FALSE constants."""
    def neg(a): return FALSE if a == TRUE else TRUE if a == FALSE else -a
    out = []
    def add(cl):
        if TRUE in cl: return
        cl = [c for c in cl if c != FALSE]
        out.append(cl)
    # e and not(p and q)  ->  x and y
    for target in (X, Y):
        add([neg(E), P, target]); add([neg(E), Q, target])
    # not e -> (x and y <-> p and q)
    add([E, neg(X), neg(Y), P]); add([E, neg(X), neg(Y), Q])
    add([E, neg(P), neg(Q), X]); add([E, neg(P), neg(Q), Y])
    return out

def adversary_wins(G, L, k, b, anyU=False, dj=False, symb=False):
    extra = []
    V, var, v, rows = build(G, set(L), k, anyU, dj, extra, symb)
    n = len(V); clauses = list(extra)
    fort = {}
    def fv(F):
        if F not in fort:
            fort[F] = v(('fort', F))
            for g, sup in rows:
                cols = [c for c in F if c in sup]
                for c in cols:
                    cl = [-fort[F]]
                    if g != TRUE: cl.append(-g)
                    if sup[c] != TRUE: cl.append(-sup[c])
                    for c2 in cols:
                        if c2 == c: continue
                        if sup[c2] == TRUE: cl = None; break
                        cl.append(sup[c2])
                    if cl is not None: clauses.append(cl)
        return fort[F]
    for B in itertools.combinations(V, b):
        rest = [u for u in V if u not in B]
        lits = [fv(frozenset(F)) for r in range(1, len(rest) + 1) for F in itertools.combinations(rest, r)]
        clauses.append(lits)
    with Cadical153(bootstrap_with=clauses) as s:
        return s.solve()

def value_at(G, L, k, anyU=False, start=0, dj=False, symb=False):
    b = start
    while adversary_wins(G, L, k, b, anyU, dj, symb): b += 1
    return b

if __name__ == '__main__':
    s, k = sys.argv[1], int(sys.argv[2]); flags = sys.argv[3:]
    G = nx.from_graph6_bytes(s.encode())
    print(s, 'depth', k, flags, 'L=empty value', value_at(G, set(), k, 'any' in flags, dj='dj' in flags, symb='symb' in flags))
