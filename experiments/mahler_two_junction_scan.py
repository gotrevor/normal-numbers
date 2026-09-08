"""Two-junction closure over background 1/D, D=(p+3)/2, for primes NOT covered by family I.
A junction at residue c with excess j: T0 = c/D + j/(pD), landing residue c' = (cp+j) mod D,
digit J = (cp+j) div D.  Weight = max safe M of the junction (max_M of mahler_junction_cert).
Cosets of H=<p> in (Z/D)^* are contracted (moves within a coset are free); we look for the
bottleneck cycle (max over cycles of min junction weight) using >=1 junction."""
import sys
sys.path.insert(0,'experiments')
from mahler_junction_cert import max_M, orbit
from mahler_burst_tower import primes
from math import gcd

def coset_id(p,D):
    ids={}
    for c in range(1,D):
        if gcd(c,D)!=1 or c in ids: continue
        for x in orbit(p,D,c): ids[x]=c
    return ids

def bottleneck(p, jmax, cap):
    Q=(p-1)//2; D=Q+2
    ids=coset_id(p,D)
    edges=[]  # (w, cosetfrom, cosetto, c, j)
    for c in range(1,D):
        if gcd(c,D)!=1: continue
        for j in range(1,jmax+1):
            v=c*p+j; J=v//D; ck=v%D
            if gcd(ck,D)!=1: continue
            M=max_M(p,D,c,ck,1,J,cap)
            if M>0: edges.append((M,ids[c],ids[ck],c,j))
    edges.sort(reverse=True)
    # threshold sweep: add edges in decreasing weight, detect a cycle (directed) among cosets
    adj={}
    def has_cycle():
        seen={}
        def dfs(u):
            seen[u]=1
            for v in adj.get(u,[]):
                if seen.get(v)==1: return True
                if seen.get(v) is None and dfs(v): return True
            seen[u]=2; return False
        return any(seen.get(u) is None and dfs(u) for u in list(adj))
    for w,a,b,c,j in edges:
        adj.setdefault(a,[]).append(b)
        if has_cycle(): return w, (c,j,a,b), len(set(ids.values()))
    return None

if __name__=="__main__":
    for p in primes(int(sys.argv[1]) if len(sys.argv)>1 else 120):
        if p<17: continue
        Q=(p-1)//2; D=Q+2
        fam1 = (D-1) in orbit(p,D,1)
        cap=Q*Q
        r=bottleneck(p, min(p,40), cap)
        print(p, "famI" if fam1 else "    ", "Q^2=",cap, "bottleneck:", r, "ratio %.3f"%(r[0]/cap if r else 0), flush=True)
