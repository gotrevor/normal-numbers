# Step (1): before/after failure fractions on IDENTICAL parent IDs (q3 % 5000 < 15, the post-update pricing slice).
import sys
NB3, NB5, S = 128*24, 64*13, 25
W3 = [int(l) for l in open('W181.txt')]
PHI1 = [int(l) for l in open('costlap/U/phi.0.txt')]
EX = {}
for l in open('costlap/U/ex.0.txt'):
    q5, r3, e = map(int, l.split()); EX[(q5, r3)] = e
par = [q3 for q3 in range(S*NB3) if q3 % 5000 < 15 and W3[q3] > 0]
pset = set(par)
before = {}
for l in open('costlap/ZX.rec'):
    q3, q5, v, t = map(int, l.split())
    if q3 in pset: before[(q3, q5)] = (v, t)
after = {}
import glob
for f in glob.glob('costlap/T2/pass1/u*.txt'):
    L = open(f).read().split('\n')
    for l in L[2:]:
        p = l.split()
        if len(p) == 4: after[(int(p[0]), int(p[1]))] = (int(p[2]), int(p[3]))
pt0 = pt1 = 0
for q3 in par:
    s = q3 // NB3
    for r5 in range(NB5):
        q5 = s*NB5 + r5
        pt0 += 1
        t = W3[q3]*PHI1[q5]; e = EX.get((q5, q3 % NB3))
        if e is not None and e < t: t = e
        if t > 0: pt1 += 1
f0, f1 = len(before), len(after)
newf = [k for k in after if k not in before]
both = [k for k in after if k in before]
fixed = [k for k in before if k not in after]
print(f"parents {len(par)}; before: ptgt {pt0} fail {f0} frac {f0/pt0:.4f}; after: ptgt {pt1} fail {f1} frac {f1/pt1:.4f}")
print(f"newly failing {len(newf)}, failing both {len(both)}, fixed (fail->pass or target 0) {len(fixed)}")
from collections import Counter
cs = Counter(k[0]//NB3 for k in newf); print("newly failing by state", sorted(cs.items()))
# how was the target changed for newly failing pairs
own = sum(1 for k in newf if (k[1], k[0]%NB3) in EX); low = sum(1 for k in newf if PHI1[k[1]] < (1<<20))
print("newly failing with own exception", own, "with lowered PHI", low)
