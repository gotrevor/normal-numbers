# max over c (q/gcd large) of N^-1 sum_{m<N} cycProd_A(c t^m mod q), q=3^A-1, N=4A
import math,sys
def cyc(A,e):
    q=3**A-1;p=1.0
    for i in range(A): p*=abs(math.cos(2*math.pi*((e*pow(3,i,q))%q)/q))
    return p
t=int(sys.argv[1])
for A in (6,8,10):
    q=3**A-1;N=4*A;best=(0,0)
    for c in range(1,q):
        if math.gcd(c,q)*1>q**0.5: continue
        v=sum(cyc(A,c*pow(t,m,q)%q) for m in range(N))/N
        best=max(best,(v,c))
    print(A,round(best[0],3),best[1])
