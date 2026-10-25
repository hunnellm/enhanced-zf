import random, itertools, networkx as nx, zhat_sage as z, sys
random.seed(1)
bad=0;cnt=0
combos=[(1,0,0,0),(2,0,0,0),(1,1,0,0),(1,0,1,0),(2,1,1,0),(1,0,0,1),(2,0,0,1)]
for t in range(60):
    n=random.choice([4,5,6,7]); p=random.choice([.3,.5,.7])
    g=nx.gnp_random_graph(n,p,seed=random.randint(0,10**6))
    if not nx.is_connected(g): continue
    nn,nb=z._adj(g)
    for k,oc,uc,au in combos:
        if k>=nn: continue
        a=z._deep_py(nn,nb,k,bool(oc),bool(uc),bool(au))
        c=z._deep_c(nn,nb,k,bool(oc),bool(uc),bool(au))
        cnt+=1
        if a!=c: bad+=1; print('MISMATCH',z._to_g6(nn,nb),k,oc,uc,au,a,c)
print(cnt,'comparisons',bad,'mismatches')
