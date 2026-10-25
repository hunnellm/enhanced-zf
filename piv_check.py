"""Independent check of the pivot game value (pure Python, no shared code with piv.c).

A state is (vertices, edges, loops) with frozensets.  value_le(state, k) decides
P(state) <= k, where P = min(Z_loop, min over looped y of degree <= 2 of max over
resolutions of P(state / y)).  Prints, for each loop configuration with
Z_loop = Zhat, the pivot used and the resolution values.
"""
import sys, itertools
from functools import lru_cache
import networkx as nx

def loop_closure(V, E, L, S):
    nb = {u: set() for u in V}
    for a, b in E: nb[a].add(b); nb[b].add(a)
    S = set(S); changed = True
    while changed:
        changed = False
        for u in V:
            Nh = nb[u] | ({u} if u in L else set())
            white = Nh - S
            if len(white) == 1:
                S |= white; changed = True
    return S

def zloop_le(V, E, L, k):
    if k >= len(V): return True
    if k < 0: return False
    for B in itertools.combinations(sorted(V), k):
        if loop_closure(V, E, L, B) == set(V): return True
    return False

@lru_cache(maxsize=None)
def le(V, E, L, k):
    if k < 0: return False
    if zloop_le(V, E, L, k): return True
    for y in sorted(L):
        nbr = sorted({b for a, b in E if a == y} | {a for a, b in E if b == y})
        if len(nbr) > 2: continue
        V2 = V - {y}
        E2 = {e for e in E if y not in e}
        L2 = L - {y}
        free = [('loop', u) for u in nbr]
        for u, w in itertools.combinations(nbr, 2):
            e = tuple(sorted((u, w)))
            if e in E: free.append(('edge', e))
            else: E2 = E2 | {e}
        ok = True
        for choice in itertools.product([0, 1], repeat=len(free)):
            Ec, Lc = set(E2), set(L2)
            for (kind, it), c in zip(free, choice):
                if kind == 'loop':
                    (Lc.add if c else Lc.discard)(it)
                else:
                    (Ec.add if c else Ec.discard)(it)
            if not le(frozenset(V2), frozenset(Ec), frozenset(Lc), k):
                ok = False; break
        if ok: return True
    return False

for s in sys.argv[1:]:
    G = nx.from_graph6_bytes(s.encode())
    V = frozenset(G.nodes()); E = frozenset(tuple(sorted(e)) for e in G.edges())
    zh = 0
    for r in range(len(V) + 1):
        for L in itertools.combinations(sorted(V), r):
            while not zloop_le(V, E, frozenset(L), zh): zh += 1
    pv = 0
    for r in range(len(V) + 1):
        for L in itertools.combinations(sorted(V), r):
            while not le(V, E, frozenset(L), pv): pv += 1
    print(s, 'Zhat', zh, 'PIV', pv, flush=True)
