"""Probe: is the two-point correlation table G(p,q,N) ASYNCHRONOUS across pairs?

Lap 1 (src/NormalNumbers/TwoPointWorry.lean) showed the TwoPointWeightedAvg quantifier
shape does not entail per-pair decorrelation, PROVIDED different pairs reach their
near-extremal correlation at different N.  This probe asks whether the real arithmetic
table has that asynchrony, or is synchronised (which would kill the room).

G(p,q,N) = | (1/N) sum_{n<N} zeta^{omega(p n+1) - omega(q n+1)} |,  zeta = e(m/b).
Unweighted (peelWeight omitted): the asynchrony question is about the two-point factor.

stdlib only.
"""
import cmath, math, sys

M = int(sys.argv[1]) if len(sys.argv) > 1 else 2_000_000   # max n
B = int(sys.argv[2]) if len(sys.argv) > 2 else 3
MM = 1
PRIMES = [2, 3, 5, 7, 11, 13]

TOP = max(PRIMES) * M + 2

def omega_sieve(top):
    om = bytearray(top + 1)
    for p in range(2, top + 1):
        if om[p] == 0:                     # p is prime
            for k in range(p, top + 1, p):
                om[k] += 1
    return om

om = omega_sieve(TOP)

# --- known-answer checks (hand-computed) ---
assert om[1] == 0 and om[2] == 1 and om[12] == 2 and om[30] == 3 and om[64] == 1
assert sum(om[1:11]) == 11, sum(om[1:11])
print("known-answer checks OK")

zeta = [cmath.exp(2j * math.pi * MM * r / B) for r in range(B)]

GRID = [10**k for k in range(3, 1 + int(math.log10(M)))]
GRID += [M]

pairs = [(p, q) for p in PRIMES for q in PRIMES if p != q]
acc = {pq: 0j for pq in pairs}
rows = {pq: [] for pq in pairs}
gi = 0
for n in range(M):
    for pq in pairs:
        p, q = pq
        acc[pq] += zeta[(om[p * n + 1] - om[q * n + 1]) % B]
    if gi < len(GRID) and n + 1 == GRID[gi]:
        for pq in pairs:
            rows[pq].append(abs(acc[pq]) / (n + 1))
        gi += 1

print(f"b={B} m={MM}  |mean| of zeta^(omega(pn+1)-omega(qn+1))")
print("pair      " + "".join(f"{g:>12d}" for g in GRID))
for pq in pairs:
    print(f"{pq[0]:>3},{pq[1]:<4}  " + "".join(f"{v:12.5f}" for v in rows[pq]))

# synchrony diagnostic: at the largest grid point, spread of sqrt(N)*|mean|
last = {pq: rows[pq][-1] * math.sqrt(M) for pq in pairs}
print("\nsqrt(N)*|mean| at N=%d:" % M)
for pq in sorted(pairs, key=lambda x: -last[x]):
    print(f"  {pq}: {last[pq]:.3f}   (p-q mod b = {(pq[0]-pq[1]) % B})")
