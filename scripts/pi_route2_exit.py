# /// script
# requires-python = ">=3.10"
# ///
"""Route 2 probe: exit transfer exit_n mod 1 vs 64/(4n+1).  Target: exact equality of
residues (c*16^(n+1-j) mod p) == 64 mod p for every prime p = 4n+1, n <= 5000.
Control: same with base 3 in place of 16 (no Euler-criterion collapse expected)."""
import math
def isprime(m): return m > 1 and all(m % d for d in range(2, math.isqrt(m) + 1))
def run(base):
    hits = tot = 0
    for n in range(1, 5001):
        p = 4 * n + 1
        if not isprime(p): continue
        r = p % 8; j = (p - r) // 8; c = 4 if r == 1 else -1
        tot += 1; hits += (c * pow(base, n + 1 - j, p) - 64) % p == 0
    return hits, tot
print("base16", run(16)); print("control base3", run(3))
