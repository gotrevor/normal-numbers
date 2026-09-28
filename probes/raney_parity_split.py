"""Is the lrDelta joint law's non-factorization exactly a PARITY effect?

Lap 5.  The kernel proves (`classEquidistribution_rplusDelta`) that the PHASE-CORRECTED
automaton `P+_i = iota^i M_i` has a FACTORIZED joint (window, state) frequency
`nu(T) * gamma(I_q)`.  `det (M . B_j) = -det M`, so `1[M_i = t]` is supported on ONE parity
of `i`, hence

    joint_lrDelta(q, t) = joint_{parity p}(q, iota^p t)
                        = 1/2 joint_plus(q, iota^p t)  +  (-1)^p/2 * signed(q, iota^p t),
    signed(q,T) = sum_i (-1)^i 1[w_i = q] 1[P+_i = T].

So EITHER the signed density vanishes -- and then lrDelta's law factorizes after all, i.e.
lap 4's finding F2 was a finite-sample artifact -- OR it does not, and `hjs` for lrDelta is a
PARITY-RESTRICTED equidistribution (the CF analogue of "normal to base b => normal to base
b^2"), which the common-reach machinery does NOT supply.

This probe measures all three: the plus-law ratio (must be q-independent), the parity-split
ratios, and the resulting lrDelta ratio.
"""
import random
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
def iota(M):
    a,b,c,d = M; return (c,d,a,b)
def states(D):
    return [ (a,b,c,d) for a in range(D+1) for b in range(D+1) for c in range(D+1)
             for d in range(D+1) if balanced((a,b,c,d)) and abs(det((a,b,c,d)))==D ]
def Bm(j): return (0,1,1,j)

def cf_digits(nbits, rng):
    M = 1 << nbits
    N = rng.randrange(1, M)
    ds = []
    a, b = N, M
    while a > 0:
        q = b // a
        ds.append(q)
        a, b = b - q*a, a
    return ds[:-1] if ds else ds

def gamma_cyl(q):
    p0,q0,p1,q1 = 1,0,0,1
    for a in q:
        p0,q0,p1,q1 = p1,q1,a*p1+p0,a*q1+q0
    x1 = p1/q1; x2 = (p1+p0)/(q1+q0)
    lo, hi = min(x1,x2), max(x1,x2)
    return (log2(1+hi) - log2(1+lo))

def run(D, nsamples, nbits, seed):
    rng = random.Random(seed)
    S = states(D)
    Splus = [M for M in S if det(M) == D]
    start = (D,0,0,1)
    trans = {}
    def step(M,j):
        key=(M,j)
        if key not in trans: trans[key]=reduce(mul(M,Bm(j)))
        return trans[key]
    qs = [[1],[2],[3],[4],[1,1],[1,2],[2,1]]
    keys = [tuple(q) for q in qs]
    jplus = {k: {M:0 for M in Splus} for k in keys}     # unsigned, P+ state
    jsign = {k: {M:0 for M in Splus} for k in keys}     # signed by (-1)^i
    jlr   = {k: {M:0 for M in S} for k in keys}         # lrDelta state
    total = 0
    for _ in range(nsamples):
        ds = cf_digits(nbits, rng)
        M = start
        n = len(ds)
        for i in range(n-3):
            P = M if i % 2 == 0 else iota(M)   # P+_i = iota^i M_i
            sgn = 1 if i % 2 == 0 else -1
            total += 1
            for q,k in zip(qs,keys):
                if all(ds[i+r]==q[r] for r in range(len(q))):
                    jplus[k][P] += 1
                    jsign[k][P] += sgn
                    jlr[k][M]  += 1
            M = step(M, ds[i])
    print(f"=== D={D}  positions={total}  |S|={len(S)}  |S+|={len(Splus)}")
    hdr = "state".ljust(15) + "".join(f"{str(q):>10}" for q in qs)
    print("  PLUS-law ratio  joint+(q,T)/(n*gamma(q))   [kernel: must be q-independent]")
    print(hdr)
    for M in Splus:
        print(str(M).ljust(15) + "".join(
            f"{jplus[k][M]/total/gamma_cyl(q):10.4f}" for q,k in zip(qs,keys)))
    print("  SIGNED density  signed(q,T)/(n*gamma(q))   [0 <=> lrDelta factorizes]")
    print(hdr)
    for M in Splus:
        print(str(M).ljust(15) + "".join(
            f"{jsign[k][M]/total/gamma_cyl(q):10.4f}" for q,k in zip(qs,keys)))
    print("  lrDelta ratio   joint(q,t)/(n*gamma(q))")
    print(hdr)
    for M in S:
        print(str(M).ljust(15) + "".join(
            f"{jlr[k][M]/total/gamma_cyl(q):10.4f}" for q,k in zip(qs,keys)))

run(3, nsamples=40, nbits=150000, seed=7)
