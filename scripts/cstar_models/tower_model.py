# Random-coset model vs measured self-good density along the Carmichael chain Q_L (c* gate 3).
# Model: a numerator p mod Q survives base b iff its orbit p*<b> (|orbit| = ord) avoids the window
# of relative width w_b = 2 b^-c; independent model density prod_b (1 - w_b)^ord_Q(b).
# Usage: tower_model.py c L [samples]
import math, sys, random
sys.path.insert(0, 'scripts')
from uniformbad_carmichael_density import primes_dividing_L_plus, selfgood
c, L = float(sys.argv[1]), int(sys.argv[2]); S = int(sys.argv[3]) if len(sys.argv) > 3 else 3000
ps = primes_dividing_L_plus(L); Q = math.prod(ps); bmax = int(Q ** (1 / c)) + 1
logd = 0.0
for b in range(2, bmax + 1):
    r, seen = 1, set()   # orbit of the unit part: length of eventual cycle of b^n mod Q
    x = 1
    for _ in range(64): x = x * b % Q
    y = x; o = 0
    while True:
        y = y * b % Q; o += 1
        if y == x: break
    logd += o * math.log(1 - 2 * b ** -c)
random.seed(1)
hits = sum(1 for _ in range(S) if selfgood(random.randrange(1, Q), Q, c, bmax))
print(f"c={c} L={L} logQ={math.log(Q):.1f}: measured {hits}/{S} = {hits/S:.2e}, model {math.exp(logd):.2e}, "
      f"model count Q*d = {Q*math.exp(logd):.2e}")
