# Local density of self-good numerators near a previous level (c* gate 3, rationalTower_four probe).
# Level Q -> Q' = Q*M (M coprime to Q, Carmichael chain).  For a self-good x = a/Q, count e in
# [-T, T] with y = x + e/M = (a*M + e*Q)/Q' self-good at exponent c (all bases b < Q', all n).
# Usage: tower_local.py c L1 L2 T [nx]
import math, sys, random
sys.path.insert(0, 'scripts')
from uniformbad_carmichael_density import primes_dividing_L_plus, selfgood
c, L1, L2, T = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
nx = int(sys.argv[5]) if len(sys.argv) > 5 else 3
P1 = primes_dividing_L_plus(L1); P2 = primes_dividing_L_plus(L2)
assert set(P1) <= set(P2)
Q = math.prod(P1); Qp = math.prod(P2); M = Qp // Q
b1 = int(Q ** (1 / c)) + 1; b2 = int(Qp ** (1 / c)) + 1
xs = [a for a in range(1, Q // 2) if math.gcd(a, Q) == 1 and selfgood(a, Q, c, b1)]
print(f"c={c} Q={Q} -> Q'={Qp} (M={M}); self-good at level 1: {len(xs)}; global density control below")
random.seed(2)
glob = sum(selfgood(p, Qp, c, b2) for p in (random.randrange(1, Qp) for _ in range(4000)) if math.gcd(p, Qp) == 1)
print(f"  random numerators mod Q': {glob}/4000")
for a in random.sample(xs, min(nx, len(xs))):
    hits = [e for e in range(-T, T + 1) if e and math.gcd(a * M + e * Q, Qp) == 1
            and selfgood(a * M + e * Q, Qp, c, b2)]
    print(f"  x={a}/{Q}: {len(hits)}/{2*T} local e, smallest |e| {min(map(abs, hits)) if hits else None}")
