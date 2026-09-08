import sys
sys.path.insert(0,'experiments')
from mahler_junction_cert import max_M, orbit
p=int(sys.argv[1]); Q=(p-1)//2; D=Q+2; cap=Q*Q
A=orbit(p,D,1); B=orbit(p,D,D-1)
for k in (2,3):
  for c0 in sorted(B):
    for ck in sorted(A):
        for J in range(p**k):
            M=max_M(p,D,c0,ck,k,J,cap)
            if M>=cap-8: print(p,D,"k",k,c0,ck,[ (J//p**i)%p for i in range(k)][::-1],M,flush=True)
  print("done k",k,flush=True)
