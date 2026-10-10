# R_d = max over Good (k,a) of desc_{d+1}/desc_d, d=0..2, at k=6 (no heredity prune)
import sys; sys.argv=['x','none']; sys.path.insert(0,'.')
import tail5_measure as T
from tail5_ratio_lib import descs
for k in (6,12):
    D=3 if k==6 else 2
    best=[0]*D
    for a in range(2**k):
        if T.sft(k,a)==99 or not T.good(k,a) or T.weight(k,a)==0: continue
        o=descs(k,a,D)
        for d in range(D):
            if o[d]>0: best[d]=max(best[d],o[d+1]/o[d])
    print("k",k,"R_d",[float(x) for x in best],flush=True)
