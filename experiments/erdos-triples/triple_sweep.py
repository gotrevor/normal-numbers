#!/usr/bin/env python3
import sys, time
sys.path.insert(0, '.')
from triple import decide
N = int(sys.argv[1]); cap = int(sys.argv[2])
t=time.time(); bad=[]; unk=[]; maxr=(0,None); cnt=0
for a in range(2, N):
    for b in range(2, N-a+1):
        r, sz = decide((4**a, 4**(a+b)), cap); cnt+=1
        if sz > maxr[0]: maxr=(sz,(a,b))
        if r is None: unk.append((a,b,sz))
        elif r: bad.append((a,b,sz))
print(f"sweep a>=2,b>=2,a+b<={N}: {cnt} triples, nonzero={bad}, unknown={unk}, max reachable={maxr}, {time.time()-t:.1f}s")
# 3-adic look-alikes of the gap-1 / a=1 exceptions
fam=[]
for j in range(1,6):
    for a in [1+3**j]:
        for b in list(range(2,12))+[1+3**i for i in range(1,5)]:
            r, sz = decide((4**a, 4**(a+b)), cap); fam.append((a,b,r,sz))
    for a in range(2,8):
        b = 1+3**j
        r, sz = decide((4**a, 4**(a+b)), cap); fam.append((a,b,r,sz))
print("look-alikes nonzero/unknown:", [f for f in fam if f[2] is not False])
print("look-alike max reachable:", max(f[3] for f in fam), "count", len(fam))
