#!/usr/bin/env -S uv run --quiet python3
"""B4b: PRICE Leaf B.  How fast does the large-prime tail forget the class mod Q?

Companion to `swingc3_b4_class_dependence.py` (which showed the decoupling is real but slow).
Here we measure the Fourier defect directly, which is what an Erdos-Turan/Weyl proof of Leaf B
would have to bound:

    D_h(r, N) = | (1/N_r) sum_{n<N, n=r (Q)} e(h y_n)  -  (1/N) sum_{n<N} e(h y_n) |

with y_n = tailLarge P b n mod 1.  Leaf B needs max_r D_h(r,N) -> 0 for every h != 0.
Fitting log D against log log N gives the exponent a in D ~ (log N)^{-a}, which is the
"Selberg-Delange grade" the PENDING_WORK pricing note predicted.

KNOWN-ANSWER CHECK: omega_{>3}(m) for m=1..8 is 0,0,0,0,1,0,1,0, so the b=4 head of
tailLarge(3,4,0) is 4^-5 + 4^-7 = 17/16384; asserted before anything else runs.
"""

import cmath
import math

TRUNC = 26
HS = [1, 2, 3]


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i in range(n + 1) if sieve[i]]


def omega_large(limit, P):
    out = bytearray(limit + 1)
    for p in primes_upto(limit):
        if p <= P:
            continue
        for m in range(p, limit + 1, p):
            out[m] += 1
    return out


def tail_values(N, om, b):
    y = [0.0] * N
    for i in range(1, TRUNC + 1):
        w = float(b) ** (-i)
        seg = om[i : i + N]
        y = [a + c * w for a, c in zip(y, seg)]
    return [t - int(t) for t in y]


def known_answer_check():
    om = omega_large(64, 3)
    assert list(om[1:9]) == [0, 0, 0, 0, 1, 0, 1, 0], list(om[1:9])
    s = sum(int(om[i]) * 4.0 ** (-i) for i in range(1, 9))
    assert abs(s - 17 / 16384) < 1e-15, s
    print("known-answer check OK: tailLarge(3,4,0) head = 17/16384")


def run(b, P, NS):
    Q = 1
    for p in primes_upto(P):
        Q *= int(p)
    print(f"\n=== b={b}  P={P}  Q={Q} ===")
    rows = {h: [] for h in HS}
    for N in NS:
        om = omega_large(N + TRUNC + 1, P)
        y = tail_values(N, om, b)
        for h in HS:
            tau = 2j * math.pi * h
            acc = [0j] * Q
            cnt = [0] * Q
            gsum = 0j
            for n, t in enumerate(y):
                v = cmath.exp(tau * t)
                r = n % Q
                acc[r] += v
                cnt[r] += 1
                gsum += v
            gm = gsum / N
            worst = 0.0
            for r in range(Q):
                worst = max(worst, abs(acc[r] / cnt[r] - gm))
            rows[h].append((N, worst))
            print(f"  N={N:>9}  h={h}  max_r D_h = {worst:.5f}"
                  f"   (|global mean| = {abs(gm):.5f})")
    for h in HS:
        pts = rows[h]
        (n1, d1), (n2, d2) = pts[0], pts[-1]
        a = math.log(d1 / d2) / math.log(math.log(n2) / math.log(n1))
        print(f"  h={h}: fit D ~ (log N)^-a  =>  a = {a:.2f}")
    return rows


def main():
    known_answer_check()
    NS = [10**5, 6 * 10**5, 36 * 10**5]
    run(4, 3, NS)
    run(3, 2, NS)


if __name__ == "__main__":
    main()
