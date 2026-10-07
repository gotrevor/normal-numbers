# Copy-zone pair sum: R = N^-2 sum_{n,m<N} prod_{i<A} |cos(2 pi eta 3^i / q)|, eta = b^n - b^m mod q,
# q = 3^A - 1, N = c*A (c copies).  This is E_W |sum_m e(b^m W/q)|^2 / N^2 bound (Riesz form).
import math, sys
def R(b,A,c):
    q=3**A-1; N=c*A
    pw=[pow(b,n,q) for n in range(N)]
    tot=0.0
    for n in range(N):
        for m in range(N):
            e=(pw[n]-pw[m])%q; p=1.0
            for i in range(A):
                p*=abs(math.cos(2*math.pi*((e*pow(3,i,q))%q)/q))
            tot+=p
    return tot/N**2
for b in map(int,sys.argv[1].split(',')):
    print(b,[round(R(b,A,int(sys.argv[2])),4) for A in (8,12,16,20,24)])
