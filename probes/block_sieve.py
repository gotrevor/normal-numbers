#!/usr/bin/env -S uv run --quiet python3
"""Self-checking probe for Lemma B of papers/ROUND2-multicutoff-fable.md
(the graded block-Bonferroni lower sieve, Astra's construction).

Every expected value below was worked out BY HAND in the paper's notation before this
file was run; nothing here is captured from the code under test.  Exit status is
nonzero on any failure.

Checks
  1. Bonferroni pair identities, exhaustively for block size b <= 12, even r <= 10:
       U(b,r) = sum_{i<=r} (-1)^i C(b,i) = (-1)^r C(b-1,r) >= 0   (b >= 1),  U(0,r) = 1
       U - D <= [b = 0]   with D = C(b, r+1).
  2. Telescoping minorant L = prod U - sum_l D_l prod_{b != l} U_b <= prod I on every hit
     pattern, for several block configurations; and the coefficient rule
     (lambda in {-1,0,1}, disjoint supports) reproduces L on every pattern.
  3. Product-model defect, two blocks of 4 primes, r = 2, g = 1/10 on each prime:
       E[U] = 1 - 0.4 + 0.06 = 0.66,   E[D] = 4 * 0.001 = 0.004,
       E[L] = 0.66^2 - 2 * 0.004 * 0.66 = 0.43032,   prod V = 0.9^8 = 0.43046721,
       relative defect = 1 - E[L]/prod V = 3.4e-4 <= bound (sum Dbar) e^{sum Dbar}
       with Dbar = 0.004/0.6561.
  4. Arithmetic instance, one block {7,11,13,17}, classes {1,2} (d = 2), r = 2, over a full
     period M = 17017: exact sifted count 5*9*11*15 = 7425; sieve minorant
     17017 - 2*6288 + 4*838 - 8*48 = 7409 <= 7425 (the omitted 4-set term is 16).
  5. Arithmetic instance with GRADED classes: band {7,11} with d = 2, band {13,17} with
     d = 1, r = 2 each (no defect terms), M = 17017: exact count 5*9*12*16 = 8640 and the
     sieve sum equals it exactly (full inclusion-exclusion), checked by brute force.
"""
from itertools import combinations, product
from math import comb, exp

fails = 0


def check(name, cond, detail=""):
    global fails
    if cond:
        print(f"  ok   {name}")
    else:
        fails += 1
        print(f"  FAIL {name}  {detail}")


def U(b, r):
    return sum((-1) ** i * comb(b, i) for i in range(r + 1))


def D(b, r):
    return comb(b, r + 1)


# ---------------------------------------------------------------- 1. Bonferroni pair
print("1. Bonferroni pair identities")
ok = True
for b in range(0, 13):
    for r in range(0, 11, 2):
        u = U(b, r)
        expect = 1 if b == 0 else (-1) ** r * comb(b - 1, r)
        if u != expect or u < 0 or (u - D(b, r)) > (1 if b == 0 else 0):
            ok = False
            print(f"    b={b} r={r}: U={u} expect={expect} U-D={u - D(b, r)}")
check("U = (-1)^r C(b-1,r) >= 0 and U - D <= [b=0], b<=12, even r<=10", ok)

# ---------------------------------------------------------------- 2. telescoping minorant
print("2. Telescoping minorant on all hit patterns, plus the coefficient rule")


def L_of_pattern(bs, rs):
    us = [U(b, r) for b, r in zip(bs, rs)]
    ds = [D(b, r) for b, r in zip(bs, rs)]
    prod_u = 1
    for u in us:
        prod_u *= u
    tot = prod_u
    for l in range(len(bs)):
        rest = 1
        for m in range(len(bs)):
            if m != l:
                rest *= us[m]
        tot -= ds[l] * rest
    return tot


def lam(sizes_in_E, rs):
    """Coefficient rule: sizes_in_E[l] = |E cap block l|."""
    over = [l for l, (sz, r) in enumerate(zip(sizes_in_E, rs)) if sz > r]
    total = sum(sizes_in_E)
    if not over:
        return (-1) ** total
    if len(over) == 1 and sizes_in_E[over[0]] == rs[over[0]] + 1:
        l = over[0]
        return -((-1) ** (total - rs[l] - 1))
    return 0


def L_from_coefficients(bs, rs):
    """sum over E subset of the hit set B (|B cap block l| = bs[l]) of lambda(E)."""
    tot = 0
    for sizes in product(*[range(b + 1) for b in bs]):
        mult = 1
        for b, s in zip(bs, sizes):
            mult *= comb(b, s)
        tot += mult * lam(list(sizes), rs)
    return tot


for blocks, rs in [((4, 4), (2, 2)), ((4, 3, 5), (2, 4, 2)), ((6, 5), (2, 2)), ((5, 5, 5), (4, 2, 2))]:
    ok_min = True
    ok_coef = True
    for bs in product(*[range(n + 1) for n in blocks]):
        I = 1 if all(b == 0 for b in bs) else 0
        Lval = L_of_pattern(bs, rs)
        if Lval > I:
            ok_min = False
        if L_from_coefficients(bs, rs) != Lval:
            ok_coef = False
    check(f"L <= prod I, blocks={blocks} r={rs}", ok_min)
    check(f"coefficient rule reproduces L, blocks={blocks} r={rs}", ok_coef)

# ---------------------------------------------------------------- 3. model defect, hand numbers
print("3. Product-model defect, two blocks of 4 primes, r=2, g=1/10")
g = 0.1
EU = sum((-1) ** i * comb(4, i) * g ** i for i in range(3))
ED = comb(4, 3) * g ** 3
EL = EU ** 2 - 2 * ED * EU
V = (1 - g) ** 8
check("E[U] = 0.66", abs(EU - 0.66) < 1e-12, f"{EU}")
check("E[D] = 0.004", abs(ED - 0.004) < 1e-12, f"{ED}")
check("E[L] = 0.43032", abs(EL - 0.43032) < 1e-12, f"{EL}")
check("prod V = 0.43046721", abs(V - 0.43046721) < 1e-12, f"{V}")
defect = 1 - EL / V
Dbar = ED / (1 - g) ** 4
bound = 2 * Dbar * exp(2 * Dbar)
check("E[L] <= prod V (minorant in expectation)", EL <= V)
check(f"relative defect {defect:.2e} <= paper bound {bound:.2e}", defect <= bound)
# the hand value: 1 - 0.43032/0.43046721 = 0.000342...
check("relative defect = 3.42e-4 (hand)", abs(defect - 3.42e-4) < 1e-6, f"{defect}")

# ---------------------------------------------------------------- 4. arithmetic, one block
print("4. Arithmetic instance: block {7,11,13,17}, classes {1,2}, r=2, full period")
P = [7, 11, 13, 17]
M = 7 * 11 * 13 * 17
check("M = 17017", M == 17017)


def hits(n, p, d):
    return any((n + i) % p == 0 for i in range(1, d + 1))


exact = sum(1 for n in range(M) if not any(hits(n, p, 2) for p in P))
check("exact sifted count = 7425", exact == 7425, f"{exact}")
r = 2
sieve = 0
for size in range(0, 5):
    for E in combinations(P, size):
        sizes = [size]
        lam_E = lam(sizes, [r])
        if lam_E == 0:
            continue
        cnt = sum(1 for n in range(M) if all(hits(n, p, 2) for p in E))
        sieve += lam_E * cnt
check("sieve minorant = 7409", sieve == 7409, f"{sieve}")
check("7409 <= 7425", sieve <= exact)
# the CRT main terms by hand: 17017 - 2*6288 + 4*838 - 8*48
check("hand CRT arithmetic 17017 - 12576 + 3352 - 384 = 7409", 17017 - 12576 + 3352 - 384 == 7409)

# ---------------------------------------------------------------- 5. graded classes, two bands
print("5. Graded classes: band {7,11} d=2, band {13,17} d=1, r=2 each, full period")
bands = [([7, 11], 2), ([13, 17], 1)]
exact2 = sum(1 for n in range(M)
             if not any(hits(n, p, d) for ps, d in bands for p in ps))
check("exact sifted count = 8640", exact2 == 8640, f"{exact2}")
sieve2 = 0
all_primes = [(p, d) for ps, d in bands for p in ps]
for size in range(0, 5):
    for E in combinations(all_primes, size):
        sizes = [sum(1 for (p, d) in E if p in bands[0][0]),
                 sum(1 for (p, d) in E if p in bands[1][0])]
        lam_E = lam(sizes, [2, 2])
        if lam_E == 0:
            continue
        cnt = sum(1 for n in range(M) if all(hits(n, p, d) for (p, d) in E))
        sieve2 += lam_E * cnt
check("graded sieve sum = 8640 (exact, no defect terms)", sieve2 == 8640, f"{sieve2}")
# model main term with per-prime class counts: M * (5/7)(9/11)(12/13)(16/17) = 5*9*12*16
check("model main term 5*9*12*16 = 8640", 5 * 9 * 12 * 16 == 8640)

print()
if fails:
    print(f"{fails} FAILURE(S)")
    raise SystemExit(1)
print("all checks passed")
