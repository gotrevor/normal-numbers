"""deadMix decay probe (CantorBadNormal.NearObstaclePhaseMixing evidence).

R(g) = E_{w_s} |E[D_t | w_s]| / E|D_t|, s = t - g, D_t = e(xi W_t/3^{L_t}) * deadErr(xi, W_t)
(the constant factor muK(xi/3^{L_t+10}) dropped), xi = b^m with b^m >= 3^{L_t + 3}.
Inner conditional mean by Monte Carlo (I continuations), noise floor ~ 1/sqrt(I).
law: 'nu' (resLaw), 'first' (resLaw outer prefix, uniform continuation = obstMix, the first-order term), 'mu' (uniform paths, control), 'dyad2' (known-biased, base 2).
usage: python3 cantorbad_deadmix.py law b seed outer inner tstages
"""
import sys, random, cmath, math, importlib.util
spec = importlib.util.spec_from_file_location("lb", __file__.replace("cantorbad_deadmix", "cantorbad_localbias_lib"))
lb = importlib.util.module_from_spec(spec); spec.loader.exec_module(lb)

def main():
    law, b = sys.argv[1], int(sys.argv[2])
    seed, outer, inner, ts = map(int, sys.argv[3:7])
    rng = random.Random(seed)
    Lt = 10 * ts
    xi = 1
    while xi < 3 ** (Lt + 3):
        xi *= b
    dl = law if law == 'dyad2' else 'q'
    if law == 'first': pass
    P = 3 ** (Lt + 10)
    rho = sum(lb.e(xi * J, P) for J in lb.KID) / 1024
    cache = {}
    def dead(W, L):
        k = (W, L)
        if k not in cache:
            cache[k] = lb.dead_children(W, L, dl)
        return cache[k]
    def step(W, L, unif=False):
        D = dead(W, L)
        while True:
            J = lb.KID[rng.randrange(1024)]
            if law == 'mu' or unif or J not in D:
                return W * 3 ** 10 + J
    def Dt(W):
        D = dead(W, Lt)
        if not D:
            return 0j
        de = sum(lb.e(xi * J, P) - rho for J in D) / (1024 - len(D))
        return lb.e(xi * W, 3 ** Lt) * de
    for g in range(0, ts - 3):
        s = ts - g
        num = 0.0; den = 0.0
        for o in range(outer):
            W = 0
            for r in range(s):
                W = step(W, 10 * r)
            if g == 0:
                v = Dt(W); num += abs(v); den += abs(v); continue
            acc = 0j; accabs = 0.0
            for i in range(inner):
                V = W
                for r in range(s, ts):
                    V = step(V, 10 * r, law == 'first')
                d = Dt(V); acc += d; accabs += abs(d)
            num += abs(acc / inner); den += accabs / inner
        print(f"law={law} b={b} g={g} R={num/max(den,1e-300):.4f} floor~{1/math.sqrt(inner):.4f}")
        sys.stdout.flush()
main()
