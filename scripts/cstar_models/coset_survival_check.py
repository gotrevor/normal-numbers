# Control for CosetSurvival (UniformBadTower): for each denominator q (gcd(q,6)=1) carrying a
# rational good for bases 2,3 at c (joint_rationals.js output on stdin), report
# max over q of kappa*(ord_q 2 + ord_q 3) - log q, i.e. log of the least C that works.
import sys, math
def order(b, q):
    x, k = b % q, 1
    while x != 1: x, k = x * b % q, k + 1
    return k
qs = [int(l.split()[0]) for l in sys.stdin if l[0].isdigit()]
for kap in [0.005, 0.0125, 0.02, 0.04, 0.067]:
    worst = max((kap * (order(2, q) + order(3, q)) - math.log(q), q) for q in qs)
    print(f"kappa={kap}: log C needed = {worst[0]:.2f} (q={worst[1]}), {len(qs)} denominators")
