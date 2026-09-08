"""Direct max-M for the classic family: background a=2 (=1/Q), burst B, target digit p-1."""
def max_M(p, B, cap):
    Q = (p-1)//2
    for m in range(1, cap+1):
        r = m % Q
        b = 2*r
        N = m*B
        carry = 0
        while N > 0 or carry > 0:
            n = N % p; N //= p
            t = b + n + carry
            if t % p == p-1: return m-1
            carry = t // p
        # remaining positions: constant b (safe, b<=p-3)
    return cap

def lam_of(p, B, j):
    """B = (p^j * lam + mu)/Q  with mu = 2  ->  lam = (B*Q - 2)/p^j (if integral)"""
    Q=(p-1)//2; x = B*Q-2
    return x // p**j if x % p**j == 0 else None

if __name__ == "__main__":
    import sys
    for p in [7,11,13,17,19,23,29,31]:
        Q=(p-1)//2; cap = Q*Q+4*p
        best=[]; 
        for B in range(1, min(60000, 6*p**3)):
            M = max_M(p,B,cap)
            if M >= Q*Q - 3*p: best.append((M,B))
        best.sort(reverse=True)
        out=[]
        for M,B in best[:4]:
            js=[j for j in range(0,5) if (B*Q-2)%p**j==0]
            j=max(js); lam=(B*Q-2)//p**j
            out.append((M,B,j,lam%p))
        print(f"p={p} Q^2={Q*Q}  (M,B,j,lam mod p): {out}")
        sys.stdout.flush()
