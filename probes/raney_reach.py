import itertools, sys
from collections import deque

def mul(M,N):
    a,b,c,d = M; e,f,g,h = N
    return (a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h)

def det(M):
    a,b,c,d = M
    return a*d-b*c

def nonneg(M): return all(x>=0 for x in M)

def balanced(M):
    a,b,c,d = M
    return nonneg(M) and ((c<a and b<d) or (a<c and d<b))

def reduce(N):
    # strip L or R from the left greedily.  L = [[1,0],[1,1]], R=[[1,1],[0,1]]
    # L^{-1} N = [[a,b],[c-a,d-b]] ; R^{-1} N = [[a-c,b-d],[c,d]]
    w = []
    while True:
        a,b,c,d = N
        if c>=a and d>=b and not (c==a and d==b):
            N = (a,b,c-a,d-b); w.append('L')
        elif a>=c and b>=d and not (a==c and b==d):
            N = (a-c,b-d,c,d); w.append('R')
        else:
            break
    return tuple(N), w

def states(D):
    S=[]
    for a in range(D+1):
        for b in range(D+1):
            for c in range(D+1):
                for d in range(D+1):
                    M=(a,b,c,d)
                    if balanced(M) and abs(det(M))==D:
                        S.append(M)
    return S

def Bm(j): return (0,1,1,j)

def analyse(D, JMAX=40):
    S = states(D)
    idx = {M:i for i,M in enumerate(S)}
    # transitions
    trans = {}
    bad = []
    for M in S:
        for j in range(1, JMAX+1):
            N = mul(M, Bm(j))
            R, w = reduce(N)
            if R not in idx:
                bad.append((M,j,R))
            trans[(M,j)] = R
    # reachability
    reach_to = {}   # for each target z, the set of states that reach it
    # BFS backwards
    succ = {M:set(trans[(M,j)] for j in range(1,JMAX+1)) for M in S}
    pred = {M:set() for M in S}
    for M in S:
        for N in succ[M]:
            pred[N].add(M)
    common = []
    for z in S:
        seen={z}; dq=deque([z])
        while dq:
            u=dq.popleft()
            for p in pred[u]:
                if p not in seen: seen.add(p); dq.append(p)
        if len(seen)==len(S):
            selfloop = any(trans[(z,j)]==z for j in range(1,JMAX+1))
            common.append((z, selfloop))
    return S, trans, common, bad

for D in [2,3,5,7,11,13,4,6,9]:
    S, trans, common, bad = analyse(D)
    print(f"D={D}: |S|={len(S)}  bad={len(bad)}  #common-targets={len(common)}  "
          f"#with-selfloop={sum(1 for _,s in common if s)}")
    if common:
        print("   e.g.", common[:3])

print("=== uniform-length common reach ===")
def uniform(D, JMAX=60, LMAX=30):
    S, trans, common, bad = analyse(D, JMAX)
    succ = {M:set(trans[(M,j)] for j in range(1,JMAX+1)) for M in S}
    best=[]
    for z,_ in common:
        # R_l = states reaching z in exactly l steps
        R = {z}
        for l in range(1, LMAX+1):
            R = {M for M in S if succ[M] & R}
            if len(R)==len(S):
                best.append((z,l)); break
    return S, best

for D in [2,3,5,7,11,13]:
    S,best = uniform(D)
    if best:
        m = min(l for _,l in best)
        print(f"D={D}: |S|={len(S)} minimal uniform length = {m}; targets achieving it: "
              f"{[z for z,l in best if l==m][:4]}")
    else:
        print(f"D={D}: none within LMAX")
