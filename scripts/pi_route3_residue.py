# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Route 3 probe: diskResidue n = diskCount(4^n) mod 8^n vs fract(2^n pi).
Target: |phase - fract(2^n pi)| <= 5/2^n (proved bound) for every n.
Control: square count (2R+1)^2 phases tend to 0 mod 1 scaled the same way."""
from math import isqrt
from fractions import Fraction as F
def arctan_inv(x, P):
    s, t, k, sign = 0, P // x, 1, 1
    while t:
        s += sign * (t // k); t //= x*x; k += 2; sign = -sign
    return s
P = 10**80; PI = F(4*(4*arctan_inv(5, P) - arctan_inv(239, P)), P)
def disk(R): return 1 + 4*R + 4*sum(isqrt(R*R-j*j) for j in range(1, R+1))
for n in range(0, 12):
    R = 4**n; D = disk(R); m = 8**n
    ph = F(D % m, m); t = 2**n*PI; tf = t - (t.numerator // t.denominator)
    sq = F(((2*R+1)**2) % m, m)
    err = abs(F(D, m) - t)*2**n
    assert err <= 5, (n, err)
    print(n, float(ph), float(tf), float(err), float(sq))
