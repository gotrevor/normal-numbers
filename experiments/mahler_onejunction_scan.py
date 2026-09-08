"""One-junction numerator certificates over an arbitrary background 1/D.

Framework (matches `NumCert.Good` in src/NormalNumbers/MahlerNumCert.lean exactly):

    E = p^(K+L) * D,  slack sigma,  K >= 1, L >= 0, K+L >= 3.
    far state  F_c  (c in the <p>-orbit of c0 mod D):  num = c * p^(K+L)
    near chain t = 0..K-1:  num = (c0*p^(t+1) mod D) * p^(K+L) + b * p^(t+L)
    jump       F_{c0} -> near(0),  delta = b * p^L   (needs delta + sigma < sigma*p)
    landing    near(K-1) -> F_{(c0*p^(K+1) + b) mod D}   (must lie in the orbit)

Validity to channel M is `NumCert.Good M`:  for every state num, every m <= M,
    (res)    (m*num mod E) + sigma*m < E
    (digit)  p*(m*num mod E) + m*delta < (p-1)*E   for each outgoing delta.

Far states with delta = 0 are free whenever D < p and sigma*m < p^(K+L)
(proved in the module docstring of MahlerFamilyI); only the K near states and the
jump edge out of F_{c0} are checked here.  `--full` re-checks every far state.

Family I is D=(p+3)/2, K=2, L=1, b=2, sigma=4, c0=p^(k-2) mod D, and needs
-1 in <p> mod D.  Freeing b removes that hypothesis: b ranges over a full
residue system mod D, so the landing can be put back into the orbit of c0
for EVERY p.
"""
import sys


def primerange(a, b):
    for x in range(max(2, a), b):
        if all(x % d for d in range(2, int(x ** 0.5) + 1)):
            yield x


def orbit(c0, p, D):
    orb, c, seen = [], c0 % D, set()
    while c not in seen:
        seen.add(c)
        orb.append(c)
        c = c * p % D
    return orb


def max_channel(p, D, K, L, sigma, c0, b, cap):
    """Largest M with `Good M`, checking the near chain and the jump edge."""
    E = p ** (K + L) * D
    lim = (p - 1) * E
    PKL = p ** (K + L)
    nums = []
    for t in range(K):
        c = c0 * pow(p, t + 1, D) % D
        nums.append(c * PKL + b * p ** (t + L))
    jump_num = (c0 % D) * PKL
    delta = b * p ** L
    for m in range(1, cap + 1):
        r = (m * jump_num) % E
        if p * r + m * delta >= lim or r + sigma * m >= E:
            return m - 1
        for num in nums:
            r = (m * num) % E
            if r + sigma * m >= E or p * r >= lim:
                return m - 1
    return cap


def check_full(p, D, K, L, sigma, c0, b, M):
    """Literal NumCert.Good check over every state (soundness cross-check)."""
    E = p ** (K + L) * D
    PKL = p ** (K + L)
    orb = orbit(c0, p, D)
    states = [(c * PKL, b * p ** L if c == c0 % D else 0) for c in orb]
    for t in range(K):
        c = c0 * pow(p, t + 1, D) % D
        states.append((c * PKL + b * p ** (t + L), 0))
    if b * p ** L + sigma >= sigma * p:
        return False
    for num, d in states:
        if num + sigma > E:
            return False
    for m in range(1, M + 1):
        for num, d in states:
            r = (m * num) % E
            if r + sigma * m >= E:
                return False
            if p * r + m * d >= (p - 1) * E:
                return False
    return True


def scan_prime(p, Ds=None, Ks=(1, 2, 3, 4), Ls=(0, 1, 2), sigmas=(1, 2, 4, 8), cap=None):
    n = (p - 1) // 2
    if cap is None:
        cap = n * n + 2 * p
    best = (0, None)
    if Ds is None:
        Ds = [D for D in range(3, p) if p % D]
    for D in Ds:
        for K in Ks:
            for L in Ls:
                if K + L < 3:
                    continue
                for sigma in sigmas:
                    bmax = min((sigma * (p - 1) - 1) // p ** L, 2 * D)
                    if bmax < 1:
                        continue
                    for c0 in range(1, D):
                        pk1 = pow(p, K + 1, D)
                        orb = set(orbit(c0, p, D))
                        for b in range(1, bmax + 1):
                            if (c0 * pk1 + b) % D not in orb:
                                continue
                            M = max_channel(p, D, K, L, sigma, c0, b, cap)
                            if M > best[0]:
                                best = (M, (D, K, L, sigma, c0, b))
    return best


if __name__ == "__main__":
    lo, hi = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (17, 60)
    for p in primerange(lo, hi):
        n = (p - 1) // 2
        M, par = scan_prime(p)
        ok = check_full(p, *par, M) if par else False
        print(f"p={p:4d} n^2={n*n:6d} M={M:6d} M/n^2={M/(n*n):.3f} "
              f"(D,K,L,sig,c0,b)={par} full={ok}", flush=True)
