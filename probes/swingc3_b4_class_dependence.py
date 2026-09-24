#!/usr/bin/env -S uv run --quiet python3
"""B4 (attack list, PENDING_WORK.md): does the large-prime tail of G_b SEE the residue
class mod Q?

Leaf B of the rotation route (`tailLargeDecouple_holds`, SwingC3Rotation.lean) says: with
Q = prod_{p<=P} p, the empirical law of

    y_n = fract( tailLarge P b n ),   tailLarge P b n = sum_{i>=1} omega_{>P}(n+i) b^{-i}

restricted to n = r (mod Q) is 1/Q of the global law, for every r.  SwingC3B5.lean showed the
dynamics alone cannot give this, so the statement is pure arithmetic and could be FALSE.  A
visible, N-persistent class dependence would REFUTE the whole rotation route.

Test: bin y_n into `BINS` arcs, tabulate per class r mod Q, and compare the class-r profile
(normalised to a probability vector) against the global profile.  Report total-variation
distance per class, against the sqrt-noise floor sqrt(BINS/(N/Q)) that a genuinely decoupled
sequence would show.

KNOWN-ANSWER CHECK (hand-computed, runs first): for b=4, P=3 (so Q=6) and the tail truncated
at i<=TRUNC, omega_{>3}(m) counts primes > 3 dividing m.  Take n = 0:
  m = 1,2,3,4,5,6,7,8,...  -> omega_{>3} = 0,0,0,0,1,0,1,0,...
so tailLarge 3 4 0 = 5*4^-5 ... no: slot i uses m = n+i, so slots i=1..8 give
  0,0,0,0,1,0,1,0  ->  tailLarge = 4^-5 + 4^-7 = 1/1024 + 1/16384 = 17/16384.
The probe asserts this exactly.
"""

from math import gcd

B = 4
P = 3
TRUNC = 26          # 4^-26 ~ 2e-16, below double precision
BINS = 16
NS = [10**5, 10**6, 4 * 10**6]


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i in range(n + 1) if sieve[i]]


def omega_large(limit, P):
    """omega_{>P}(m) for m = 0..limit."""
    out = bytearray(limit + 1)
    for p in primes_upto(limit):
        if p <= P:
            continue
        for m in range(p, limit + 1, p):
            out[m] += 1
    return out


def tail_values(N, om):
    """y_n = fract(sum_{i=1..TRUNC} om[n+i] b^-i) for n < N."""
    w = [B ** (-i) for i in range(1, TRUNC + 1)]
    ys = []
    for n in range(N):
        s = 0.0
        for i in range(1, TRUNC + 1):
            c = om[n + i]
            if c:
                s += c * w[i - 1]
        ys.append(s - int(s))
    return ys


def known_answer_check():
    om = omega_large(64, P)
    assert list(om[1:9]) == [0, 0, 0, 0, 1, 0, 1, 0], list(om[1:9])
    s = sum(om[0 + i] * B ** (-i) for i in range(1, 9))
    expected = 17 / 16384
    assert abs(s - expected) < 1e-15, (s, expected)
    print(f"known-answer check OK: tailLarge(3,4,0) head = {s} = 17/16384")


def main():
    known_answer_check()
    Q = 1
    for p in primes_upto(P):
        Q *= p
    print(f"b={B} P={P} Q={Q} bins={BINS} trunc={TRUNC}")
    for N in NS:
        om = omega_large(N + TRUNC + 1, P)
        ys = tail_values(N, om)
        glob = [0] * BINS
        cls = [[0] * BINS for _ in range(Q)]
        for n, y in enumerate(ys):
            j = min(int(y * BINS), BINS - 1)
            glob[j] += 1
            cls[n % Q][j] += 1
        gtot = sum(glob)
        gp = [c / gtot for c in glob]
        floor = (BINS / (N / Q)) ** 0.5
        print(f"  N={N:>9}  noise floor ~ {floor:.4f}")
        worst = 0.0
        for r in range(Q):
            tot = sum(cls[r])
            cp = [c / tot for c in cls[r]]
            tv = 0.5 * sum(abs(a - b) for a, b in zip(cp, gp))
            worst = max(worst, tv)
            print(f"    r={r}  n_r={tot:>8}  TV(class, global) = {tv:.5f}"
                  f"   ratio-to-floor {tv / floor:5.2f}")
        print(f"    worst TV {worst:.5f}   worst/floor {worst / floor:5.2f}")


if __name__ == "__main__":
    main()
