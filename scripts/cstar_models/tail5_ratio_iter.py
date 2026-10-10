# Iterated-descendant ratio probe: R_d = max over Good (k,a) of desc_{d+1}/desc_d (block = 6 levels).
import sys; sys.argv=['x','none']; sys.path.insert(0,'.')
import tail5_measure as T
def descs(k,a,D):
    out=[0]*(D+1)
    def go(kk,aa):
        if T.sft(kk,aa)==99: return
        if (kk-k)%6==0:
            d=(kk-k)//6
            if not T.good(kk,aa): return   # assume Good hereditary along block levels (prune)
            out[d]+=T.weight(kk,aa)
            if d==D: return
        go(kk+1,2*aa); go(kk+1,2*aa+1)
    go(k,a); return out
import sys as S
k=int(S.argv[-1]) if False else 12
best=[(0,None)]*3
for a in range(2**k):
    if T.sft(k,a)==99 or not T.good(k,a) or T.weight(k,a)==0: continue
    o=descs(k,a,2)
    for d in range(2):
        if o[d]>0:
            r=o[d+1]/o[d]
            if r>best[d][0]: best[d]=(r,a)
print("k",k,"R0 (desc1/w)",float(best[0][0]),best[0][1],"R1 (desc2/desc1)",float(best[1][0]),best[1][1],flush=True)
o=descs(18,191938,2); print("cell(18,191938) desc:",[float(x) for x in o], "ratios", float(o[1]/o[0]), float(o[2]/o[1]))
