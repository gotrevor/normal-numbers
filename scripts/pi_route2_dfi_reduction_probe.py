#!/usr/bin/env -S uv run --script
# /// script
# dependencies = ["sympy"]
# ///
"""Host check for ON-LINE-FINDINGS-2026-10-26-dfi-restricted.md: for primes p = 120t+1 < 4.8e6,
(1) Gauss: 2 is a cube mod p  <=>  3 | b in p = a^2+3b^2;  (2) the cutoff-six exit numerator
2^(20t+6) is a root of x^2+64x+4096 when 2 is not a cube;  (3) ||exit||_Z agrees with
||32*inv(a mod b)/b||_Z up to 32/(b*sqrt p), for one of the two roots."""
from sympy import isprime
from math import isqrt
def rep(p):  # p = a^2 + 3 b^2, a,b>0
    for b in range(1, isqrt(p//3)+1):
        r = p - 3*b*b; a = isqrt(r)
        if a*a == r: return a, b
def dZ(x): x %= 1; return min(x, 1-x)
n = bad1 = bad2 = 0; maxerr = 0; far = 0
for t in range(1, 40000):
    p = 120*t + 1
    if not isprime(p): continue
    a, b = rep(p)
    cube = pow(2, 20*t, p) == 1
    if cube != (b % 3 == 0): bad1 += 1           # Gauss: 2 cube <=> p = x^2+27y^2 <=> 3|b
    if cube: continue
    n += 1
    nu = pow(2, 20*t + 6, p)
    if (nu*nu + 64*nu + 4096) % p: bad2 += 1      # exit numerator is a root
    approx = -32*pow(a, -1, b)/b if b > 1 else 0.0
    err = min(dZ(nu/p - approx), dZ(nu/p + approx + 64/p)); maxerr = max(maxerr, err*b*p**0.5/32)
    far += dZ(nu/p) >= 0.25
print(f"primes with 2 not a cube: {n}; Gauss-criterion mismatches {bad1}; non-root exits {bad2}; "
      f"max err*(b*sqrt p/32) = {maxerr:.3f}; far (>=1/4) {far} ({far/n:.3f})")
