import sys, itertools, networkx as nx, time
from satsch import adversary_wins
def full_value(G, k, anyU=False, symb=False, dj=False, start=0, verbose=False):
    import satsch; satsch._SYM.clear()
    V=list(G); b=start; arg=None
    for r in range(len(V)+1):
        for L in itertools.combinations(V, r):
            while adversary_wins(G, set(L), k, b, anyU, dj, symb): b+=1; arg=L
    return b, arg
if __name__=='__main__':
    k=int(sys.argv[1]); flags=sys.argv[2].split(',')
    for s in sys.argv[3:]:
        t=time.time(); G=nx.from_graph6_bytes(s.encode())
        b,arg=full_value(G,k,'any' in flags,'symb' in flags,'dj' in flags)
        print(s,'depth',k,flags,'value',b,'last raised at L =',arg,'%.0fs'%(time.time()-t),flush=True)
