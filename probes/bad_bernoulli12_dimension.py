#!/usr/bin/env -S uv run --quiet python3
"""Dimension of the Bernoulli(1/2) measure on E_{1,2} (CF digits in {1,2}).

Tripwire for the Jordan-Sahlsten cross-check in `NormalNumbers.BadNormal`
(`Literature.SahlstenStevensBernoulli12` docstring): JS Thm 1.3(2) needs dim mu > 1/2.

dim mu = h / lambda with h = log 2 and lambda = 2 * gamma, gamma = E log(a + x),
a uniform in {1,2} independent of x ~ mu (q_{n+1}/q_n = a_{n+1} + q_{n-1}/q_n, and
q_{n-1}/q_n = [0; a_n, ..., a_1] has the law of mu for i.i.d. digits).

RIGOROUS bracket: x lies in the closed CF cylinder of its first D digits, whose
endpoints are [0; w] and [0; w, 1]; log(a + x) is increasing in x, so averaging
log(a + lo(w)) and log(a + hi(w)) over the 2^D words brackets gamma.
dim > 1/2  <=>  lambda < 2 log 2.
"""
import math

def endpoints(word):
    # value of [0; word] and [0; word, 1]
    def val(ws):
        v = 0.0
        for a in reversed(ws):
            v = 1.0 / (a + v)
        return v
    u, w = val(word), val(word + [1])
    return min(u, w), max(u, w)

def bracket(D):
    lo_sum = hi_sum = 0.0
    for m in range(2 ** D):
        word = [1 + ((m >> i) & 1) for i in range(D)]
        lo, hi = endpoints(word)
        lo_sum += 0.5 * (math.log(1 + lo) + math.log(2 + lo))
        hi_sum += 0.5 * (math.log(1 + hi) + math.log(2 + hi))
    n = 2 ** D
    return 2 * lo_sum / n, 2 * hi_sum / n

if __name__ == "__main__":
    for D in (4, 8, 12, 16):
        lam_lo, lam_hi = bracket(D)
        print(f"D={D:2d}  lambda in [{lam_lo:.6f}, {lam_hi:.6f}]  "
              f"dim in [{math.log(2)/lam_hi:.6f}, {math.log(2)/lam_lo:.6f}]")
    lam_lo, lam_hi = bracket(16)
    assert lam_hi < 2 * math.log(2), "dimension bound > 1/2 FAILED"
    print("OK: dim mu > 1/2 (lambda upper bound < 2 log 2 =", 2 * math.log(2), ")")
