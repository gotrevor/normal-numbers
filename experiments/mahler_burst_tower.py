"""Incremental digit-by-digit construction of the burst B.

Condition (background a=2, target digit p-1):  for all 1<=m<=M, adding the
constant background digit b=2*(m mod Q) to the base-p digits of N=m*B with
carries never produces the digit p-1.
Digit i of m*B depends only on B mod p^(i+1), and the carry into position i
only on digits < i -- so we can build B's digits low-to-high with exact pruning.
"""
import sys

def primes(n):
    s=[True]*(n+1); s[0]=s[1]=False
    for i in range(2,int(n**.5)+1):
        if s[i]:
            for j in range(i*i,n+1,i): s[j]=False
    return [i for i in range(n+1) if s[i]]

def finish(p, Q, B, M):
    """full check of B (all positions)"""
    for m in range(1, M+1):
        b = 2*(m % Q); N = m*B; c = 0
        while N > 0 or c > 0:
            n = N % p; N //= p
            t = b + n + c
            if t % p == p-1: return False
            c = t // p
    return True

def search(p, M, Kmax=8, cap=40000):
    Q = (p-1)//2
    # node: (Bmod, tuple carries for m=1..M)
    frontier = [(0, tuple([0]*(M+1)))]
    sols = []
    for K in range(Kmax):
        pk = p**K; pk1 = p**(K+1)
        nxt = []
        for (Bm, car) in frontier:
            for d in range(p):
                Bn = Bm + d*pk
                if Bn == 0: 
                    newc = car
                    nxt.append((Bn, newc)); continue
                ok = True; nc = [0]*(M+1)
                for m in range(1, M+1):
                    n = ((m*Bn) % pk1)//pk
                    t = 2*(m % Q) + n + car[m]
                    if t % p == p-1: ok = False; break
                    nc[m] = t//p
                if ok: nxt.append((Bn, tuple(nc)))
            if len(nxt) > cap: break
        frontier = nxt[:cap]
        # try to stop at this level
        for (Bn, car) in frontier:
            if Bn > 0 and finish(p, Q, Bn, M):
                sols.append(Bn)
        if sols: return K+1, sols
        if not frontier: return None, []
    return None, []

def digs(n,p):
    d=[]
    while n: d.append(n%p); n//=p
    return d

if __name__ == "__main__":
    for p in [7,11,13,17,19,23,29,31,37,41]:
        Q=(p-1)//2; M=Q*Q-2
        K, sols = search(p, M)
        if sols:
            sols=sorted(sols)[:3]
            print(f"p={p:3d} Q={Q:3d} M={M:5d}=Q^2-2  len={K}  B={sols}  digits={[digs(B,p) for B in sols]}")
        else:
            print(f"p={p:3d} Q={Q:3d} M={M:5d}  NO SOLUTION up to length 8")
        sys.stdout.flush()
