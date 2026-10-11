# Optimistic budget for self-good rationals with joint small orders (c* gate 3).
# A modulus q | G = gcd(2^a - 1, 3^b - 1) has ord(2) | a, ord(3) | b.  Square-root coset model:
# expected self-good count <= q * exp(-k2*a - k3*b), k_b = -ln(1 - 2 b^-c)/2 (bases >= 5 ignored:
# optimistic).  Report, per scale A, the best log G - k2 a - k3 b over a, b <= A.
import math, sys
c = float(sys.argv[1]); A = int(sys.argv[2])
k2 = -math.log(1 - 2 * 2 ** -c) / 2; k3 = -math.log(1 - 2 * 3 ** -c) / 2
P2 = [0] + [2 ** a - 1 for a in range(1, A + 1)]; P3 = [0] + [3 ** b - 1 for b in range(1, A + 1)]
best = {}
for a in range(1, A + 1):
    for b in range(1, A + 1):
        g = math.gcd(P2[a], P3[b])
        if g < 2: continue
        v = math.log(g) - k2 * a - k3 * b
        s = max(a, b).bit_length()
        if s not in best or v > best[s][0]: best[s] = (v, a, b, round(math.log(g), 1))
for s in sorted(best): print(f"max(a,b) in [{2**(s-1)},{2**s}): best margin {best[s][0]:.1f} at a={best[s][1]} b={best[s][2]} logG={best[s][3]}")
