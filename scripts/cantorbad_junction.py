"""Window Riesz products of X at depth S=floor(n log3 b)+off, length M: X=b^m-b^n (diff) vs X=b^m (single)."""
import math,sys
def W(X,S,M):
    x=1.0
    for i in range(S+1,S+M+1):
        r=(X%3**i)/3**i; x*=abs(math.cos(2*math.pi*r))
    return x
b=int(sys.argv[1]); N=int(sys.argv[2]); M=int(sys.argv[3])
for off in (-3,0,3,8):
    d=s=0;c=0
    for m in range(N):
        for n in range(m):
            S=int(n*math.log(b,3))+off
            if S<0: continue
            d+=W(b**m-b**n,S,M); s+=W(b**m,S,M); c+=1
    print(b,off,round(d/c,4),round(s/c,4))
