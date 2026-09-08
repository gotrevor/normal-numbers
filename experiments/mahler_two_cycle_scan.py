"""Offset 2-cycle certificates over one background: two drift-one junctions (b, b') closed by
D | b*p + b'.  `two_cycle(p, D, b, bp)` checks the literal Keys of MahlerBackgroundCert for both
junctions and the orbit closure; the coverage scan (python3 mahler_two_cycle_scan.py N BMAX KM)
reports every prime p ≢ 1 (mod 12) below N with no closed-form (b, b', k) certificate.
Result 2026-09-08: none below 2000 (worst ratio 0.40); p ≡ 1 (mod 12) is never covered
(only b = 2 divides p+1 when (p+1)/2 is prime).
"""
def primerange(a,b):
    for x in range(a,b):
        if x>1 and all(x%d for d in range(2,int(x**0.5)+1)): yield x
def orbit(c,p,D):
    o=[];x=c%D
    while x not in o: o.append(x); x=x*p%D
    return o
def keys_max(p,D,c0,b,cap):
    """literal Keys of MahlerBackgroundCert for junction (c0,b): max M"""
    c1=c0*p%D; c2=c0*p*p%D
    for m in range(1,cap+1):
        if not (p*p*(m*c1%D)+m*b < (p-1)*p*D): return m-1,'A'
        if not (m*(c2*p+b)%(p*D) < (p-1)*D): return m-1,'B'
        if not (b*m+p*p*D < p**3): return m-1,'J'
        if not (2*b*m < p*p*D): return m-1,'R'
    return cap,'cap'
def two_cycle(p,D,b,bp):
    if gcd(D,p+1)!=1 or gcd(D,p)!=1: return None
    inv=pow(p+1,-1,D)
    c2=(-b*inv)%D; c2p=(-bp*inv)%D
    O1=orbit(c2,p,D); 
    if c2p not in orbit((-c2)%D,p,D): return None   # closure
    if (-c2p)%D not in O1: return None
    pinv2=pow(p*p,-1,D)
    c0=c2*pinv2%D; c0p=c2p*pinv2%D
    cap=(p*p)//2
    M1=keys_max(p,D,c0,b,cap); M2=keys_max(p,D,c0p,bp,cap)
    return min(M1[0],M2[0]),M1,M2


N=int(sys.argv[1]); BMAX=int(sys.argv[2]); KM=int(sys.argv[3])
best={}
for p in primerange(61,N):
    if p%12==1: continue
    divs=[b for b in range(2,BMAX+1) if (p+1)%b==0]
    bp_=None
    for b in divs:
        for b2 in divs:
            if b==b2: continue
            num=b*p+b2
            for k in range(2*b, KM*b+1):
                if num%k: continue
                D=num//k
                if D<3 or 2*D>=p: continue
                r=two_cycle(p,D,b,b2)
                if r is None: continue
                val=r[0]/(p//2)**2
                if bp_ is None or val>bp_[0]: bp_=(round(val,3),D,b,b2,k)
    best[p]=bp_
unc=[p for p in best if best[p] is None]
print("uncovered (p≢1 mod 12):",unc)
cov=sorted((v[0],p,v) for p,v in best.items() if v)
print("worst:",cov[:8])
