import sys
sys.path.insert(0,'experiments')
from mahler_junction_cert import max_M
for p in [29,53,59,61,67,71,73]:
    Q=(p-1)//2; cap=Q*Q
    for D in (Q-1,Q,Q+1):
        res=[]
        for c0 in range(1,D):
            for ck in range(1,D):
                for J in range(p):
                    M=max_M(p,D,c0,ck,1,J,cap)
                    if M>=cap-8: res.append((M,c0,ck,J))
        res.sort(reverse=True)
        print(p,Q,"D=",D,res[:6],flush=True)
