"""Does the joint (window, state) frequency FACTORIZE for the Raney transducer?

`VandeheyOut.mobiusUniformFreq_of_transducer` assumes `JointStateFreq`:
   (1/n) #{i<n : window_i = q, state_i = t}  ->  nu(t) * gamma(I_q)
with a SINGLE nu independent of q.  For a group-like automaton (every digit acting
bijectively, uniform stationary law) that is automatic.  The Raney automaton's digit
steps are NOT injective, so the stationary law is not uniform and the state at time i
is correlated with the digits just before i -- which are adjacent to the window at i.

This probe measures rho(q,t)/gamma(I_q) for several q and checks whether it is
q-independent.
"""
import random, math
from math import log2

def mul(M,N):
    a,b,c,d = M; e,f,g,h = N
    return (a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h)
def det(M):
    a,b,c,d = M; return a*d-b*c
def nonneg(M): return all(x>=0 for x in M)
def balanced(M):
    a,b,c,d = M
    return nonneg(M) and ((c<a and b<d) or (a<c and d<b))
def reduce(N):
    while True:
        a,b,c,d = N
        if c>=a and d>=b and not (c==a and d==b): N=(a,b,c-a,d-b)
        elif a>=c and b>=d and not (a==c and b==d): N=(a-c,b-d,c,d)
        else: return N
def states(D):
    return [ (a,b,c,d) for a in range(D+1) for b in range(D+1) for c in range(D+1)
             for d in range(D+1) if balanced((a,b,c,d)) and abs(det((a,b,c,d)))==D ]
def Bm(j): return (0,1,1,j)

def cf_digits(nbits, rng):
    """CF digits of a random rational -- exact Euclid, Gauss-distributed statistics."""
    M = 1 << nbits
    N = rng.randrange(1, M)
    out = []
    while N:
        M, N = N, M % N
        out.append(M // N if N else None)
    # redo properly
    return out

def cf_digits2(nbits, rng):
    M = 1 << nbits
    N = rng.randrange(1, M)
    ds = []
    a, b = N, M          # value a/b in (0,1); digit = floor(b/a)
    while a > 0:
        q = b // a
        ds.append(q)
        a, b = b - q*a, a
    return ds[:-1] if ds else ds

def gamma_cyl(q):
    """Gauss measure of the CF cylinder of the word q."""
    # I_q = interval between p/qd and (p+p')/(qd+qd') ; compute endpoints by continuants
    p0,q0,p1,q1 = 1,0,0,1
    for a in q:
        p0,q0,p1,q1 = p1,q1,a*p1+p0,a*q1+q0
    x1 = p1/q1
    x2 = (p1+p0)/(q1+q0)
    lo, hi = min(x1,x2), max(x1,x2)
    return (log2(1+hi) - log2(1+lo))

def run(D, nsamples=40, nbits=200000, seed=1):
    rng = random.Random(seed)
    S = states(D)
    idx = {M:i for i,M in enumerate(S)}
    start = (D,0,0,1)
    trans = {}
    def step(M,j):
        key=(M,j)
        if key not in trans: trans[key]=reduce(mul(M,Bm(j)))
        return trans[key]
    qs = [[1],[2],[3],[4],[1,1],[1,2],[2,1]]
    joint = {tuple(q): {M:0 for M in S} for q in qs}
    statec = {M:0 for M in S}
    total = 0
    for _ in range(nsamples):
        ds = cf_digits2(nbits, rng)
        M = start
        n = len(ds)
        for i in range(n-3):
            statec[M]+=1; total+=1
            for q in qs:
                if all(ds[i+k]==q[k] for k in range(len(q))):
                    joint[tuple(q)][M]+=1
            M = step(M, ds[i])
    print(f"D={D}  digits={total}  |S|={len(S)}")
    print("state marginal nu(t):", {M: round(statec[M]/total,5) for M in S})
    print()
    hdr = "state".ljust(16) + "".join(f"{str(q):>12}" for q in qs)
    print(hdr)
    for M in S:
        row = str(M).ljust(16)
        for q in qs:
            r = joint[tuple(q)][M]/total/gamma_cyl(q)
            row += f"{r:12.5f}"
        print(row)
    print("\ngamma(I_q):", {str(q): round(gamma_cyl(q),5) for q in qs})

run(3, nsamples=30, nbits=120000, seed=7)
run(2, nsamples=60, nbits=120000, seed=11)
