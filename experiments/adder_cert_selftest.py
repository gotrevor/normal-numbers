#!/usr/bin/env -S uv run --quiet --with numpy --with scipy --with mpmath python3
"""Shadowing self-test for the adder certificate conventions (BRIEF-adder-disjunction).

Anchors the emitter's automaton (adder_certificate_emit.py) against the TRUE
binary digits of ln 2 / ln 3:

  1. digit anchor: ln 2 = 0.10110001011100100001..._2, so digitOf-position 4
     is the first occurrence of `00` (digits at indices 4,5).
  2. true carries: T_i(m) = floor(2^m z) - a*floor(2^m X) - b*floor(2^m Y)
     stay in [0, a+b-1] for every channel over the tested range.
  3. column identity: a*x_m + b*y_m + T(m) = d_m(z) + 2*T(m-1).
  4. shadowing: whenever no channel word occurs at position m, the true state
     S(m) steps to S(m+1) under pred with input (x_{m+1}, y_{m+1}); whenever a
     word DOES occur at position m, pred declares that step illegal.
  5. each channel's word occurs at least once in the tested range (so the
     word test does fire — guards against an inverted legality convention).
  6. the hand-checkable survivor x = y = (10)^inf (X = Y = 2/3) walks a live
     period-2 cycle of the main certificate forever.
"""

import json
from pathlib import Path

import mpmath as mp
import numpy as np

from adder_certificate_emit import FAMILIES, Family

PREC_BITS = 4000
DEPTH = 3500  # digit positions tested (< PREC_BITS with margin)


def true_bits(x: mp.mpf, n: int) -> list[int]:
    """digitOf 2 (fract x) i for i in range(n), via exact floor arithmetic."""
    fr = x - mp.floor(x)
    return [int(mp.floor(fr * mp.mpf(2) ** (i + 1))) % 2 for i in range(n)]


def true_carry(z, X, Y, a, b, m):
    return int(mp.floor(z * 2 ** m) - a * mp.floor(X * 2 ** m) - b * mp.floor(Y * 2 ** m))


def main():
    mp.mp.prec = PREC_BITS + 64
    X, Y = mp.log(2), mp.log(3)
    xb, yb = true_bits(X, DEPTH + 8), true_bits(Y, DEPTH + 8)

    # 1. digit anchor
    lead = "".join(map(str, xb[:20]))
    assert lead == "10110001011100100001", lead
    first00 = next(i for i in range(len(xb) - 1) if xb[i] == 0 and xb[i + 1] == 0)
    assert first00 == 4, first00
    print("anchor OK: ln 2 leads 10110001011100100001, first 00 at position 4")

    fam = Family(FAMILIES["main"])
    channels = FAMILIES["main"]
    zs = [X * a + Y * b for a, b, _ in channels]
    zbits = [true_bits(z, DEPTH + 8) for z in zs]

    # 2+3. carries in range, column identity  (floor index m = digit index i+1)
    for (a, b, w), z, zb in zip(channels, zs, zbits):
        for m in range(1, DEPTH):
            T_m = true_carry(z, X, Y, a, b, m)
            assert 0 <= T_m <= max(a + b - 1, 0), (a, b, m, T_m)
            T_prev = true_carry(z, X, Y, a, b, m - 1)
            d_m = zb[m - 1]  # digitOf index m-1 = floor index m
            assert a * xb[m - 1] + b * yb[m - 1] + T_m == d_m + 2 * T_prev, (a, b, m)
    print(f"carry bounds + column identity OK over floor positions 1..{DEPTH - 1}")

    # 4+5. shadowing against pred
    preds = fam.pred_tables()

    def state_at(m: int) -> int:
        """Encode the true state at digit position m (floor index m)."""
        s, mult = 0, 1
        for (a, b, w), zb, wsz, n in zip(channels, zbits, fam.win_sizes, fam.sizes):
            c = true_carry(X * a + Y * b, X, Y, a, b, m)
            # window bit j = d_{m+1+j} (floor index) = digit index m+j
            wcode = sum(zb[m + j] << j for j in range(len(w) - 1))
            s += (c * wsz + wcode) * mult
            mult *= n
        return s

    def occurs_at(m: int) -> bool:
        """Some channel word occurs at OccursAt-position m (digit indices m..m+l-1)."""
        for (a, b, w), zb in zip(channels, zbits):
            if all(zb[m + j] == int(w[j]) for j in range(len(w))):
                return True
        return False

    occ_per_channel = [0] * len(channels)
    legal_steps = illegal_steps = 0
    for m in range(0, DEPTH - 8):
        sigma = xb[m] + 2 * yb[m]  # input (x_{m+1}, y_{m+1}) = digit index m
        s, s2 = state_at(m), state_at(m + 1)
        p = int(preds[sigma][s2])
        if occurs_at(m):
            assert p == -1 or p != s, f"word occurred at {m} but step legal"
            # the step must be ILLEGAL precisely because of the word test:
            assert p == -1, f"pos {m}: word occurred but pred gave {p} (state {s})"
            illegal_steps += 1
        else:
            assert p == s, f"pos {m}: shadowing failed pred={p} truth={s}"
            legal_steps += 1
        for i, ((a, b, w), zb) in enumerate(zip(channels, zbits)):
            if all(zb[m + j] == int(w[j]) for j in range(len(w))):
                occ_per_channel[i] += 1
    print(f"shadowing OK over positions 0..{DEPTH - 9}: "
          f"{legal_steps} legal steps, {illegal_steps} word-occurrence breaks")
    assert all(c > 0 for c in occ_per_channel), occ_per_channel
    print(f"every channel word occurs (counts: {occ_per_channel})")

    # 6. survivor x = y = (10)^inf  ==> X = Y = 2/3
    cert = json.loads((Path(__file__).parent / "certs" / "adder_cert_main.json").read_text())
    live = cert["live"]
    Xs = Ys = mp.mpf(2) / 3
    xb2, yb2 = true_bits(Xs, 64), true_bits(Ys, 64)

    def state_at2(m):
        s, mult = 0, 1
        for (a, b, w), wsz, n in zip(channels, fam.win_sizes, fam.sizes):
            z = Xs * a + Ys * b
            c = true_carry(z, Xs, Ys, a, b, m)
            zb = true_bits(z, 64)
            wcode = sum(zb[m + j] << j for j in range(len(w) - 1))
            s += (c * wsz + wcode) * mult
            mult *= n
        return s

    s0, s1_, s2_ = state_at2(3), state_at2(4), state_at2(5)
    assert s0 == s2_ and s0 != s1_, (s0, s1_, s2_)
    assert live[s0] and live[s1_]
    sig0 = xb2[3] + 2 * yb2[3]
    sig1 = xb2[4] + 2 * yb2[4]
    assert int(preds[sig0][s1_]) == s0 and int(preds[sig1][s2_]) == s1_
    print(f"survivor (10)^inf OK: live period-2 cycle states {s0} <-> {s1_}")
    print("ALL SELF-TESTS PASS")


if __name__ == "__main__":
    main()
