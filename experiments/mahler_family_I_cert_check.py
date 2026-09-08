"""Exact evaluator of the Lean certificate in src/NormalNumbers/MahlerFamilyI.lean
(states F_c, N_-1, N_0; uniform slack 4/(p^3 D); carries floor(m*lo)).
Prints, for each odd p with p^k = -1 mod D=(p+3)/2: validity at M = Q^2-2 (True)
and the first failing clause at M = Q^2-1 (the N_-1 -> N_0 edge at m = Q^2-1)."""
from fractions import Fraction as F
def cert(p,k):
    Q=(p-1)//2; D=Q+2; cm1=pow(p,2*k-1,D); cm2=pow(p,2*k-2,D); n=D+2
    def a(s): return s*p//D if s<D else (cm1*p//D if s==D else 1)
    def nxt(s):
        if s<D: return [s*p%D]+([D] if s==cm2 else [])
        return [D+1] if s==D else [D-1]
    def lo(s): return F(s,D) if s<D else (F(cm1*p*p+2,p*p*D) if s==D else F(p+2,p*D))
    def hi(s): return lo(s)+F(4,p**3*D)
    def c(s,m): return (m*lo(s)).__floor__()
    return n,a,nxt,lo,hi,c
def valid(p,k,M):
    n,a,nxt,lo,hi,c=cert(p,k)
    for s in range(n):
        if not a(s)<p: return ("a",s)
        if not (0<=lo(s)<=hi(s)<=1): return ("int",s)
        for t in nxt(s):
            if not (lo(s)<=(a(s)+lo(t))/p and (a(s)+hi(t))/p<=hi(s)): return ("edge",s,t)
    for m in range(0,M+1):
        for s in range(n):
            if not (c(s,m)<=m*lo(s) and m*hi(s)<=c(s,m)+1): return ("carry",s,m)
            for t in nxt(s):
                if c(s,m)!=(m*a(s)+c(t,m))//p: return ("rec",s,t,m)
                if m>=1 and (m*a(s)+c(t,m))%p==p-1: return ("block",s,t,m)
    return True
def findk(p):
    D=(p+3)//2
    for k in range(1,2*D):
        if pow(p,k,D)==D-1: return k
for p in range(17,260,2):
    k=findk(p)
    if k is None: continue
    Q=(p-1)//2
    print(p,k,valid(p,k,Q*Q-2),valid(p,k,Q*Q-1))
