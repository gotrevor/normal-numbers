"""Controls for CoefmassRandomLambertMoment skeleton statements (steps 1,3,4,6).  Exact enumeration."""
import itertools, math, cmath, random
rng = random.Random(3)
e = lambda x: cmath.exp(2j * math.pi * x)
def bern(d, th): return abs((1 - d) + d * e(th))
def tsign(k, i): return 1 if i < k else -1
def tphase(b, h, k, p, n): return h * sum(tsign(k, i) * (b ** n[i] % (b ** p - 1)) / (b ** p - 1) for i in range(2 * k))
# note: b^n mod (b^p-1) reduction is legitimate only inside e(.) / bernMod (integer shift) - matches step 2

# step 3: prefix_tuple_mean_le
worst = -1; red = 0
for _ in range(300):
    Q = rng.randint(1, 7); d = rng.randint(1, 3); N = rng.randint(1, 20)
    G = {r: rng.random() for r in itertools.product(range(Q), repeat=d)}
    if rng.random() < .3: G = {r: float(all(x < Q // 2 + 1 for x in r)) for r in G}
    lhs = sum(G[tuple(x % Q for x in n)] for n in itertools.product(range(N), repeat=d)) / N ** d
    per = sum(G.values()) / Q ** d
    worst = max(worst, (lhs - per) / (d * Q / N)); red += lhs > per + 1e-12
print(f"step3 prefix: max (lhs-period)/(dQ/N) = {worst:.3f} (<=1 required); red 'no error term' fails in {red}/300")

# step 4: crt_tuple_prod_mean (q = 3,4,5 pairwise coprime; non-coprime red 2,4)
def crt(qs, d):
    gs = [{r: rng.random() for r in itertools.product(range(q), repeat=d)} for q in qs]
    Q = math.prod(qs)
    lhs = sum(math.prod(g[tuple(x % q for x in n)] for g, q in zip(gs, qs)) for n in itertools.product(range(Q), repeat=d)) / Q ** d
    rhs = math.prod(sum(g.values()) / q ** d for g, q in zip(gs, qs))
    return abs(lhs - rhs)
print(f"step4 crt: coprime (3,4,5),d=1: {crt([3,4,5],1):.1e}; (3,5),d=2: {crt([3,5],2):.1e};  RED non-coprime (2,4),d=1: {crt([2,4],1):.1e}")

# step 6: residueTuple_mean_sq exact identity
mx = 0
for b, h, k, p, dl in [(2, 1, 1, 5, .3), (2, 3, 2, 5, .7), (3, -2, 1, 7, .5), (2, 1, 2, 3, .2)]:
    lhs = sum(bern(dl, tphase(b, h, k, p, r)) ** 2 for r in itertools.product(range(p), repeat=2 * k)) / p ** (2 * k)
    f = sum(e(h * (b ** r) / (b ** p - 1)) for r in range(p)) / p
    rhs = 1 - 2 * dl * (1 - dl) * (1 - abs(f) ** (2 * k))
    mx = max(mx, abs(lhs - rhs))
print(f"step6 second moment identity: max err {mx:.1e}")

# step 1: moment_le_tupleAvg, exact expectation with finitely supported delta
def weyl(b, h, x, N): return sum(e(h * b ** n * x) for n in range(N)) / N
mxr = 0; viol = 0
for b, h, k, N, Fsel in [(2, 1, 1, 6, [3, 5]), (2, 1, 2, 5, [5]), (3, 2, 1, 7, [2, 3]), (2, 3, 1, 8, [3, 5, 7])]:
    P = [2, 3, 5, 7]; dl = {p: rng.uniform(.1, .9) for p in P}; c = rng.random(); s = rng.choice([1, -1])
    E = 0
    for bits in itertools.product([0, 1], repeat=len(P)):
        pr = math.prod(dl[p] if x else 1 - dl[p] for p, x in zip(P, bits))
        Y = sum(x / (b ** p - 1) for p, x in zip(P, bits))
        E += pr * abs(weyl(b, h, c + s * Y, N)) ** (2 * k)
    bound = sum(math.prod(bern(dl[p], tphase(b, h, k, p, n)) for p in Fsel) for n in itertools.product(range(N), repeat=2 * k)) / N ** (2 * k)
    viol += E > bound + 1e-12; mxr = max(mxr, E / bound)
print(f"step1 moment<=tupleAvg: violations {viol}/4, max E/bound {mxr:.3f}")
