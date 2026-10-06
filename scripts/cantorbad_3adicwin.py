"""ThreeAdicWindowAvg probe: mean over m<N (log3 b^m >= j+1) of prod_{p<M}|cos(2pi h b^m/3^(j-M+p+1))|, exact mod 3^j."""
import math
def avg(b,N,j,h=1):
    M=int(math.log(N,3))//2; Q=3**j; s=0; n=0
    for m in range(N):
        if m*math.log(b,3) < j+1: continue
        r=(h*pow(b,m,Q))%Q; x=1.0
        for p in range(M): x*=abs(math.cos(2*math.pi*r/3**(j-M+p+1)))
        s+=x; n+=1
    return M, s/max(n,1)
for b in (2,5,7,3):
    print(b,[ (j,round(avg(b,3**8,j)[1],4)) for j in (4,8,16,32,64)])
