# Orphan fraction (tail kills ignored): Good level-6(m+1) cells whose level-6m parent is not Good,
# weighted by their child mass descMass(6(m+1), a, 6(m+2)), vs all Good level-6(m+1) cells.
import sys; sys.argv=['x','none']; sys.path.insert(0,'.')
import tail5_measure as T
def desc1(k,a):
    t=0
    def go(kk,aa):
        nonlocal t
        if T.sft(kk,aa)==99: return
        if kk==k+6:
            if T.good(kk,aa): t+=T.weight(kk,aa)
            return
        go(kk+1,2*aa); go(kk+1,2*aa+1)
    go(k,a); return t
for m in (1,2):
    k=6*(m+1); tot=orph=0
    for a in range(2**k):
        if T.sft(k,a)==99 or not T.good(k,a): continue
        d=desc1(k,a); tot+=d
        if not T.good(k-6,a>>6): orph+=d
    print("m",m,"childMassTot(m+1)~",float(tot),"orphan",float(orph),"frac",float(orph/tot),flush=True)
