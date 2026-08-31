"""Reference implementation: standard / PSD / loop zero forcing and Zhat.

Conventions (see prompt §1):
 - vertices 0..n-1, adjacency as bitmasks adj[v]
 - looping: bitmask `loops`, bit v set  <=>  loop at v  <=>  diagonal entry a_vv nonzero
 - loop color change rule: v forces u whenever u is the UNIQUE unfilled vertex of
   N_hat(v), where N_hat(v) = N(v) union ({v} if loop at v).  v need not be filled.
 - standard rule: filled v forces its unique unfilled neighbor.
 - PSD rule: delete filled vertices; a filled v with exactly one neighbor u in some
   component of the remainder forces u.
"""
from itertools import combinations

def parse_graph6(s):
    s = s.strip()
    data = [ord(c) - 63 for c in s]
    n = data[0]
    assert 0 <= n < 63
    bits = []
    for c in data[1:]:
        for k in range(5, -1, -1):
            bits.append((c >> k) & 1)
    adj = [0] * n
    idx = 0
    for j in range(1, n):
        for i in range(j):
            if bits[idx]:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            idx += 1
    return n, adj

def to_graph6(n, adj):
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if (adj[i] >> j) & 1 else 0)
    while len(bits) % 6:
        bits.append(0)
    out = [chr(n + 63)]
    for k in range(0, len(bits), 6):
        v = 0
        for b in bits[k:k+6]:
            v = (v << 1) | b
        out.append(chr(v + 63))
    return ''.join(out)

def closure_loop(n, adj, loops, filled):
    N = [adj[v] | (loops & (1 << v)) for v in range(n)]
    changed = True
    while changed:
        changed = False
        for v in range(n):
            m = N[v] & ~filled
            if m and (m & (m - 1)) == 0:
                filled |= m
                changed = True
    return filled

def closure_std(n, adj, filled):
    changed = True
    while changed:
        changed = False
        for v in range(n):
            if (filled >> v) & 1:
                m = adj[v] & ~filled
                if m and (m & (m - 1)) == 0:
                    filled |= m
                    changed = True
    return filled

def components(n, adj, mask):
    comps = []
    rem = mask
    while rem:
        start = rem & (-rem)
        comp = start
        frontier = start
        while frontier:
            new = 0
            f = frontier
            while f:
                b = f & (-f)
                v = b.bit_length() - 1
                new |= adj[v] & mask & ~comp
                f ^= b
            comp |= new
            frontier = new
        comps.append(comp)
        rem &= ~comp
    return comps

def closure_psd(n, adj, filled):
    full = (1 << n) - 1
    changed = True
    while changed:
        changed = False
        unf = full & ~filled
        if not unf:
            break
        comps = components(n, adj, unf)
        f = filled
        while f:
            b = f & (-f)
            v = b.bit_length() - 1
            for C in comps:
                m = adj[v] & C
                if m and (m & (m - 1)) == 0:
                    filled |= m
                    changed = True
            f ^= b
    return filled

def _min_forcing(n, closure_fn):
    full = (1 << n) - 1
    if n == 0:
        return 0
    verts = list(range(n))
    for k in range(0, n + 1):
        for S in combinations(verts, k):
            B = 0
            for v in S:
                B |= 1 << v
            if closure_fn(B) == full:
                return k
    return n

def Z(n, adj):
    return _min_forcing(n, lambda B: closure_std(n, adj, B))

def Zplus(n, adj):
    return _min_forcing(n, lambda B: closure_psd(n, adj, B))

def Z_loop(n, adj, loops):
    return _min_forcing(n, lambda B: closure_loop(n, adj, loops, B))

def Zhat(n, adj, verbose=False):
    """max over the 2^n loopings of Z_loop; returns (Zhat, witness_looping)."""
    best, wit = -1, 0
    z_upper = Z(n, adj)
    for loops in range(1 << n):
        z = Z_loop(n, adj, loops)
        if z > best:
            best, wit = z, loops
            if best == z_upper:
                break
    return best, wit

def has_forcing_set_of_size(n, adj, loops, k):
    full = (1 << n) - 1
    for S in combinations(range(n), k):
        B = 0
        for v in S:
            B |= 1 << v
        if closure_loop(n, adj, loops, B) == full:
            return True
    return False
