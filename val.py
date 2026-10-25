import json, time, sys, zhat_sage as z
T=json.load(open('mr_table.json'))
use=tuple(sys.argv[1].split(',')) if len(sys.argv)>1 and sys.argv[1] else ()
nmax=int(sys.argv[2]) if len(sys.argv)>2 else 7
bad=[];det=0;tot=0;t=time.time()
for g6,M in T.items():
    n,nb=z._from_g6(g6)
    if n>nmax or n<3: continue
    z._CACHE.clear()
    opts=z._opts(1,False,False,False,'python',use,True,True)
    lo,hi,ls,hs=z._bounds(n,nb,opts,0,top_table=False)
    tot+=1; det+= lo==hi
    if not lo<=M<=hi: bad.append((g6,M,lo,hi,ls,hs))
print(tot,'graphs; determined',det,'; violations',len(bad),'; %.0fs'%(time.time()-t))
for b in bad[:15]: print(b)
