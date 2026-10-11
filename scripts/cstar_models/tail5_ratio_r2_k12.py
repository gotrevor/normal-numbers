# R2 = desc3/desc2 at level 12 on the R1-worst cells and a random sample (SAMPLED)
import sys, random; sys.argv=['x','none']; sys.path.insert(0,'.')
import tail5_measure as T
from tail5_ratio_lib import descs
random.seed(1)
G=[a for a in range(2**12) if T.sft(12,a)!=99 and T.good(12,a) and T.weight(12,a)>0]
S=[3343,1163,701]+random.sample(G,25)
best=0
for a in S:
    o=descs(12,a,3)
    r1=o[2]/o[1]; r2=o[3]/o[2]
    best=max(best,r2)
    print(a,"R1",round(float(r1),2),"R2",round(float(r2),2),flush=True)
print("max R2",float(best))
