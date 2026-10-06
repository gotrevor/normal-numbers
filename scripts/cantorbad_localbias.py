"""Local dead-bias probe for resLaw (CantorBadNormal.LocalDeadBias evidence).

At each stage (prefix W of L = 10 s ternary digits, selectors in {0,2}) the dead children are the
10-digit children whose cylinder meets an obstacle B(p/q, 2c/q^2), 3^{L-5} <= q^2 < 3^{L+5}
(CantorBadNormal.Alive, c = 1/(4 3^16)).  For each dead child f we record
  Z_f = sum_{n in window} (<e_n>_{Wf} - <e_n>_W),
where <e_n>_v = E_{mu_K tail}[e(b^n x) | x in cyl v] and the window is 3^L <= b^{n+2}, b^n < 3^{L+15}.
Under resLaw the conditional character of e(b^n x) given W is <e_n>_W - (1/|A|) sum_f (...), so
mean(Z) != 0 (coherent, "additive") would be a floor: resLaw not b-normal.  Also recorded:
A = sum_{b^{n+2} <= 3^L} e(b^n W/3^L) (the frozen past Weyl sum), for the inflation ratio
E[|D| |A|^2 / n0] / (E[|D|] E[|A|^2 / n0]) and the cross-term coherence of conj(A) Z.

law: 'nu' (resLaw: uniform on alive children), 'mu' (control: uniform on all children, dead set
still computed), 'dyad' (known-false sibling: obstacles p/2^m, 3^{L-10} <= 2^m < 3^L, radius
2^{-m-35}; Alive2; base 2 only).
usage: python3 cantorbad_localbias.py law seed paths stages
"""
import sys, random, cmath, math
sys.setrecursionlimit(100000)

def simplest_open(a, b, c, d):
    """Fraction (p, q) with least q in the open interval (a/b, c/d), b, d > 0, a/b < c/d."""
    fl = a // b
    if (fl + 1) * d < c:
        return (fl + 1, 1)
    a1 = a - fl * b
    c1 = c - fl * d
    if a1 == 0:
        k = d // c1 + 1
        return (fl * k + 1, k)
    p1, q1 = simplest_open(d, c1, b, a1)
    return (fl * p1 + q1, p1)

def enum(a, b, c, d, Q, out):
    p, q = simplest_open(a, b, c, d)
    if q > Q:
        return
    out.append((p, q))
    enum(a, b, p, q, Q, out)
    enum(p, q, c, d, Q, out)

KID = []  # J values of the 1024 children (ternary digits in {0,2}, 10 digits)
for m in range(1024):
    J = 0
    for i in range(10):
        J = 3 * J + (2 if (m >> (9 - i)) & 1 else 0)
    KID.append(J)
KSET = set(KID)

def dead_children(W, L, law):
    """Set of child indices J (in KSET) that are dead for prefix integer W of length L."""
    D = set()
    P3 = 3 ** L
    if law == 'dyad2':
        # known-false control with a detectable bias: kill the child containing a dyadic p/2^m,
        # m = floor((L+5) log2 3) (about 4 dead children per stage)
        m = math.floor((L + 5) * math.log2(3))
        M = 2 ** m
        for p in range((W * M) // P3, ((W + 1) * M) // P3 + 1):
            t = (p * P3 - W * M) * 3 ** 10 / M
            J = math.floor(t)
            if J in KSET and 0 <= t <= 3 ** 10:
                D.add(J)
        return D
    if law == 'dyad':
        # obstacles p/2^m, 3^{L-10} <= 2^m < 3^L, radius 2*2^{-m-36}
        m = 0
        while 2 ** m < P3:
            if 2 ** m * 3 ** 10 >= P3:
                M = 2 ** m
                # p/M in [W/P3 - eps, (W+1)/P3 + eps]
                plo = (W * M) // P3 - 1
                phi = ((W + 1) * M) // P3 + 1
                for p in range(plo, phi + 1):
                    # t = (p/M - W/P3) * 3^{L+10} ; radius in child units = 3^{L+10} * 2^{-m-35}
                    t = (p * P3 - W * M) * 3 ** 10 / M
                    rho = 3 ** (L + 10) / (2 ** (m + 35))
                    for J in range(math.floor(t - rho) - 1, math.floor(t + rho) + 2):
                        if J in KSET and J <= t + rho and J + 1 >= t - rho:
                            D.add(J)
            m += 1
        return D
    Q = math.isqrt(3 ** (L + 5) - 1)
    qmin2 = 3 ** (L - 5) if L >= 5 else 0
    out = []
    # the 8 depth-(L+3) K-subcylinders, expanded by the max radius (< 3^{-L-11})
    for m3 in range(8):
        J3 = 0
        for i in range(3):
            J3 = 3 * J3 + (2 if (m3 >> (2 - i)) & 1 else 0)
        den = 3 ** (L + 12)
        lo = (W * 27 + J3) * 3 ** 9 - 1
        hi = (W * 27 + J3 + 1) * 3 ** 9 + 1
        enum(lo, den, hi, den, Q, out)
    for p, q in out:
        if q * q < qmin2:
            continue
        t = (p * P3 - W * q) * 3 ** 10 / q
        rho = 3 ** (L + 10) / (2 * 3 ** 16 * q * q)
        for J in range(math.floor(t - rho) - 1, math.floor(t + rho) + 2):
            if J in KSET and J <= t + rho and J + 1 >= t - rho:
                D.add(J)
    return D

TWO_PI_I = 2j * math.pi

def e(num, den):
    return cmath.exp(TWO_PI_I * ((num % den) / den))

def tailchar(Bn, Lp):
    """mu_K tail character E e(Bn t / 3^{Lp}), t = sum_{j>=1} d_j 3^{-j}, d_j in {0,2}."""
    z = 1 + 0j
    j = 1
    top = Bn.bit_length() * math.log(2) / math.log(3)
    while True:
        den = 3 ** (Lp + j)
        z *= (1 + e(2 * Bn, den)) / 2
        if j > top - Lp + 25:
            break
        j += 1
    return z

def cond_char(Bn, V, Lp):
    return e(Bn * V, 3 ** Lp) * tailchar(Bn, Lp)

def main():
    law = sys.argv[1]
    seed = int(sys.argv[2]); paths = int(sys.argv[3]); stages = int(sys.argv[4])
    bases = [2] if law in ('dyad', 'dyad2') else [2, 5, 7]
    rng = random.Random(seed)
    # accumulators per base
    acc = {b: dict(nZ=0, sZ=0j, sabsZ=0.0, sZ2=0.0, sX=0j, sabsX=0.0,
                   wA=0.0, w=0.0, uA=0.0, u=0, ndead=0, nst=0) for b in bases}
    for path in range(paths):
        W = 0
        for s in range(stages):
            L = 10 * s
            D = dead_children(W, L, law if law in ('dyad', 'dyad2') else 'q')
            P3 = 3 ** L
            for b in (bases if s >= 4 else []):
                a = acc[b]
                # past Weyl sum A
                A = 0j; n0 = 0; Bn = 1; x = W % P3
                while Bn * b * b <= P3:
                    A += e(x, P3)
                    x = (x * b) % P3
                    Bn *= b; n0 += 1
                a['nst'] += 1
                if n0 > 0:
                    a['uA'] += abs(A) ** 2 / n0; a['u'] += 1
                if D:
                    if n0 > 0:
                        a['wA'] += len(D) * abs(A) ** 2 / n0; a['w'] += len(D)
                    # window n0 <= n, b^n < 3^{L+15}
                    win = []
                    n = n0; B = Bn
                    while B < 3 ** (L + 15):
                        win.append(B); B *= b; n += 1
                    par = [cond_char(B, W, L) for B in win]
                    for J in D:
                        Vc = W * 3 ** 10 + J
                        Z = sum(cond_char(B, Vc, L + 10) - pc for B, pc in zip(win, par))
                        a['nZ'] += 1; a['sZ'] += Z; a['sabsZ'] += abs(Z); a['sZ2'] += abs(Z) ** 2
                        X = A.conjugate() * Z
                        a['sX'] += X; a['sabsX'] += abs(X)
                    a['ndead'] += len(D)
            # choose the next block
            while True:
                J = KID[rng.randrange(1024)]
                if law in ('mu', 'mud2') or J not in D:
                    break
            W = W * 3 ** 10 + J
    for b in bases:
        a = acc[b]
        nZ = max(a['nZ'], 1)
        mZ = a['sZ'] / nZ
        sd = math.sqrt(max(a['sZ2'] / nZ - abs(mZ) ** 2, 0))
        print(f"law={law} b={b} stages={a['nst']} deadchildren={a['ndead']} "
              f"meanZ={mZ.real:+.4f}{mZ.imag:+.4f}i |meanZ|/mean|Z|={abs(mZ)/max(a['sabsZ']/nZ,1e-12):.4f} "
              f"se(|meanZ|)~{sd/math.sqrt(nZ):.4f} mean|Z|={a['sabsZ']/nZ:.4f} "
              f"crossRe/abs={a['sX'].real/max(a['sabsX'],1e-12):+.4f} "
              f"inflation={(a['wA']/max(a['w'],1e-12))/max(a['uA']/max(a['u'],1),1e-12):.4f}")
        sys.stdout.flush()

main()
