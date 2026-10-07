# log_3 ord_{q'}(2)/l, q' = odd part of 3^l - 1 (small-period redesign needs > .369)
import math, random, sys
def isprime(n):
    if n<2: return False
    for p in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if n%p==0: return n==p
    d=n-1;s=0
    while d%2==0: d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,n)
        if x in(1,n-1): continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def rho(n):
    if n%2==0: return 2
    while True:
        c=random.randrange(1,n);f=lambda x:(x*x+c)%n
        x=y=random.randrange(2,n);d=1
        while d==1: x=f(x);y=f(f(y));d=math.gcd(abs(x-y),n)
        if d!=n: return d
def factor(n,out):
    if n==1: return
    if isprime(n): out[n]=out.get(n,0)+1; return
    d=rho(n); factor(d,out); factor(n//d,out)
def order(a,n,fac):
    # lambda-ish: order mod n from prime-power factors
    e=1
    for p,k in fac.items():
        pk=p**k; phi=pk-pk//p
        f={};factor(phi,f) if phi>1 else None
        o=phi
        for r in f:
            while o%r==0 and pow(a,o//r,pk)==1: o//=r
        e=e*o//math.gcd(e,o)
    return e
for l in range(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])):
    q=3**l-1
    while q%2==0: q//=2
    fac={};factor(q,fac)
    e=order(2,q,fac)
    print(l, round(math.log(e,3)/l,3), flush=True)
