# /// script
# dependencies = []
# ///
"""Lane 1 probe: n_k = first n >= k with ||(2^n - 3) x|| < 2^-k, k = 1..K.

Must reach: n_k <= C*4^k for a small C (premise `PiQuantitativeTripleReturn`); heuristic n_k ~ 2^k.
Controls: x = 1/3 (rational; 3x ≡ 0 and 2^n/3 ≡ 1/3 or 2/3, so NO return for k >= 2 —
known answer), x = sqrt 2 (irrational surrogate).  Exact integer arithmetic (Machin, isqrt)."""
import sys
from math import isqrt

K = int(sys.argv[1]) if len(sys.argv) > 1 else 14
NSCAN = 8 * 4 ** K
B = NSCAN + 128  # fractional bits kept

def arctan_inv(m, bits):  # arctan(1/m) * 2^bits, truncated
    one = 1 << (bits + 32)
    s, t, k, sign = 0, one // m, 1, 1
    m2 = m * m
    while t:
        s += sign * (t // k)
        t //= m2; k += 2; sign = -sign
    return s >> 32

def pi_frac():
    p = 16 * arctan_inv(5, B) - 4 * arctan_inv(239, B)
    return p % (1 << B)

def sqrt2_frac():
    return isqrt(2 << (2 * B)) % (1 << B)

def probe(name, X):
    M = (1 << B) - 1
    t3 = (3 * X) & M
    print(name, flush=True)
    for k in range(1, K + 1):
        found = None
        thr = 1 << (B - k)
        v = (X << k) & M
        for n in range(k, NSCAN + 1):
            d = (v - t3) & M
            if d < thr or (1 << B) - d < thr:
                found = n; break
            v = (v << 1) & M
        print(f"  k={k:2d} n_k={found}  2^k={2**k}  4^k={4**k}", flush=True)

probe("1/3 (control: expect None for k>=2)", ((1 << B) - 1) // 3)
probe("sqrt2", sqrt2_frac())
probe("pi", pi_frac())
