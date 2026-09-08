import sys
sys.path.insert(0,'experiments')
from mahler_junction_cert import max_M
for p in [int(a) for a in sys.argv[1:]]:
    Q=(p-1)//2; cap=Q*Q
    res=[]
    for c0 in range(1,Q):
        for ck in range(1,Q):
            for J in range(p*p):
                M=max_M(p,Q,c0,ck,2,J,cap)
                if M>=cap-8: res.append((M,c0,ck,[J//p,J%p]))
    res.sort(reverse=True)
    print(p,Q,cap,res[:12],flush=True)
