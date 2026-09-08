"""Junction search with a GENERAL background denominator D < p.

alpha = [ block of the periodic expansion of c/D ] [k junction digits] [ block ] ...
Tails:   T_{-j} = c_{-j}/D + Delta/p^j   (j>=1),  c_{-j} = c_0 * p^{-j} mod D
         T_n    = frac(p^n T_0),  n=0..k-1,   T_0 = (J*D + c_k)/(D p^k)
         Delta  = T_0 - c_0/D  > 0  required
Safety:  frac(m*T) < 1 - 1/p  for every tail T and every 1<=m<=M.
Background tails alone are safe for any D < p since (D-1)/D < 1-1/p.
"""
import sys

def max_M(p, D, c0, ck, k, J, cap):
    Dk = D * p**k
    num0 = J * D + ck                    # T0 = num0/Dk
    dnum = num0 - c0 * p**k              # Delta = dnum/Dk
    if dnum <= 0: return -1
    Jm = 1
    # need cap*Delta/p^Jm < 1/D - 1/p = (p-D)/(pD)
    while cap * dnum * p >= (p - D) * p**(k + Jm):
        Jm += 1
        if Jm > 10: return -1
    Dq = D * p**(k + Jm)
    thr = Dq - Dq // p
    nums = []
    n0 = num0 * p**Jm
    for n in range(k):
        nums.append((n0 * p**n) % Dq)
    # c_{-j}: c_0 * p^{-j} mod D  -> iterate: c_{-j-1} = c_{-j} * pinv mod D
    try: pinv = pow(p, -1, D)
    except ValueError: return -1
    c = c0
    for j in range(1, Jm + 1):
        c = (c * pinv) % D
        nums.append((c * p**(k + Jm) + dnum * p**(Jm - j)) % Dq)
    for m in range(1, cap + 1):
        for nu in nums:
            if (m * nu) % Dq >= thr: return m - 1
    return cap

def orbit(p, D, c0):
    o, c = set(), c0
    while c not in o:
        o.add(c); c = (c * p) % D
    return o

def scan(p, kmax, cap=None, top=6, Dmin=2):
    if cap is None: cap = ((p-1)//2)**2 + 8*p
    best = []
    for D in range(Dmin, p):
        for c0 in range(D):
            orb = orbit(p, D, c0)
            for ck in orb:
                for k in range(1, kmax+1):
                    for J in range(p**k):
                        M = max_M(p, D, c0, ck, k, J, cap)
                        if M > 0: best.append((M, D, c0, ck, k, J))
    best.sort(reverse=True)
    return best[:top]

CENSUS = {5:6,7:9,11:25,13:35,17:64,19:80,23:120}
if __name__ == "__main__":
    for p, kmax in [(5,4),(7,4),(11,3),(13,3)]:
        b = scan(p, kmax)
        print(f"p={p} maxbad(census)={CENSUS[p]-1}  best={b[:4]}")
        sys.stdout.flush()
