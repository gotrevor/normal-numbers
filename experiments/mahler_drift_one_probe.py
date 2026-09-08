from math import gcd
import sys
def primerange(a,b):
    for x in range(a,b):
        if all(x%d for d in range(2,int(x**0.5)+1)): yield x
def minus1(p,D):
    c=p%D;t=1
    while c!=1:
        if c==D-1: return t
        c=c*p%D;t+=1
    return 0
N=int(sys.argv[1])
fails3=[]; worst=[]
for p in primerange(17,N):
    ok=False; bestD=0
    for D in range((p+1)//2-1, p//6, -1):   # descending: largest D first
        if D%2==0 or gcd(D,p+1)!=1: continue
        if minus1(p,D):
            bestD=D
            if 3*D>p: ok=True
            break
    if not ok: fails3.append((p,bestD))
    worst.append((bestD/p,p,bestD))
worst.sort()
print("fail (p/3,p/2):",fails3)
print("worst D/p:",worst[:8])

# --qnr : the classical form (`exists_prime_nonresidue`): a prime q in (p/3, p/2),
# q not dividing p+1, with p a quadratic non-residue mod q.  Fails only at p = 71 below 6000.
if len(sys.argv) > 2 and sys.argv[2] == '--qnr':
    def legendre(a, q): return pow(a, (q - 1) // 2, q)
    fails = []
    for p in primerange(73, N):
        if not any(legendre(p, q) == q - 1 and (p + 1) % q
                   for q in primerange(p // 3 + 1, (p + 1) // 2)):
            fails.append(p)
    print("qnr fails:", fails)
