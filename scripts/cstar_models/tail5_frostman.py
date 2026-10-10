# Frostman exponent of the weighted Good counting measure at level K (root): max over x of
# mu([x, x+h]) / mu(total) vs h = 2^-t.  alpha_eff(t) = log(maxfrac) / log(h).
import sys, math, bisect; sys.argv=['x','none']; sys.path.insert(0,'.')
import tail5_measure as T
K=int(__import__('os').environ.get('KLEV','20'))
cells=[]
def dfs(k,a):
    if T.sft(k,a)==99: return
    if k==K:
        if T.good(k,a):
            w=T.weight(k,a)
            if w>0: cells.append((a,float(w)))
        return
    dfs(k+1,2*a); dfs(k+1,2*a+1)
dfs(0,0); cells.sort()
pos=[a for a,_ in cells]; pre=[0.0]
for _,w in cells: pre.append(pre[-1]+w)
tot=pre[-1]
for t in range(2,K-1):
    L=2**(K-t)  # interval length in level-K cell units
    best=0.0; j=0
    for i in range(len(pos)):
        while j<len(pos) and pos[j]<pos[i]+L: j+=1
        best=max(best,pre[j]-pre[i])
    f=best/tot; print(t, "maxfrac", f, "alpha_eff", math.log(f)/math.log(2.0**-t), flush=True)
