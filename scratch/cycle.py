"""Two-shadow cycles: x = rho1 + p^-L1 (rho2 - rho1 [+B1]) + p^-(L1+L2) (rho1 - rho2 + B2) + ...
Digits of m*x checked up to depth ~ (L1+L2)*reps + margin, exact rational arithmetic."""
import sys
from fractions import Fraction as Fr
from math import gcd
sys.path.insert(0,'experiments')
from mahler_burst_tower import primes

def digits_bad(p, y, depth, W):
    # y rational in [0,inf): check digits 1..depth of frac(y)
    y = y - (y.numerator // y.denominator)
    for _ in range(depth):
        y *= p
        d = y.numerator // y.denominator
        if d == W: return True
        y -= d
    return False

def maxM(p, jumps, reps, cap, W):
    # jumps: list of (L, delta) applied cyclically; x = rho0 + sum p^-(cumL) * delta
    rho0 = jumps_rho0
    # build x truncated after reps cycles
    x = rho0; cum = 0
    for _ in range(reps):
        for (L, delta) in jumps:
            cum += L; x += Fr(delta) / Fr(p)**cum
    depth = cum + 40
    for m in range(1, cap+1):
        if digits_bad(p, m*x, depth, W): return m-1
    return cap

if __name__ == "__main__":
    for p in primes(int(sys.argv[1])):
        if p < 7: continue
        Q = (p-1)//2; cap = Q*Q; W = p-1
        r1 = Fr(1, Q); r2 = Fr(1, Q-1)
        jumps_rho0 = r1
        best = []
        for L in range(2, 9):
            for B in range(0, 4):
                jumps = [(L, r2 - r1), (L, r1 - r2 + B)]
                M = maxM(p, jumps, 3, cap, W)
                best.append((M, L, B))
        best.sort(reverse=True)
        print(p, Q, cap, best[:4], flush=True)
