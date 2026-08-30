#!/usr/bin/env python3
"""Shadowing self-test for the SIGNED adder conventions (pure stdlib).

Anchors adder_signed_emit.py's automaton against the TRUE binary digits of
the family instance constants (a·ln2 + b·ln3), computed by
integer atanh series (no mpmath on this box):

  1. digit anchor: ln 2 = 0.10110001011100100001..._2.
  2. true carries stay in the SIGNED window [-(a-+b-), a++b+-1].
  3. column identity a*x_m + b*y_m + T(m) = d_m(z) + 2*T(m-1) over Z.
  4. shadowing: the true encoded state walks pred exactly, breaking
     precisely at word occurrences.
  5. every channel word occurs in the tested range.
  6. a NEGATIVE carry (an actual borrow) is exercised.
"""

from adder_signed_emit import FAMILIES, Family

PREC = 3700          # working precision (bits)
GUARD = 80
DEPTH = 3500


def atanh_inv(q: int, prec: int) -> int:
    """round(atanh(1/q) * 2^prec) up to a few ulps."""
    one = 1 << prec
    total = 0
    k = 0
    while True:
        term = one // ((2 * k + 1) * q ** (2 * k + 1))
        if term == 0:
            break
        total += term
        k += 1
    return total


def main(famname="musical"):
    P = PREC + GUARD
    ln2 = 2 * atanh_inv(3, P)            # ln 2 = 2 atanh(1/3)
    ln3 = 2 * (atanh_inv(3, P) + atanh_inv(5, P))  # ln 3 = 2(atanh 1/3 + atanh 1/5)
    # sanity: ln3 - ln2 = ln(3/2) = 2 atanh(1/5) by construction

    channels = FAMILIES[famname]
    fam = Family(channels)
    Zs = [a * ln2 + b * ln3 for a, b, _ in channels]
    for z, (a, b, _) in zip(Zs, channels):
        assert z > 0, (a, b, "constant not positive")

    def bit(Z: int, i: int) -> int:
        """digitOf 2 (fract z) i  (floor index i+1)."""
        return (Z >> (P - (i + 1))) & 1

    def floor_at(Z: int, m: int) -> int:
        return Z >> (P - m) if m <= P else Z << (m - P)

    # 1. digit anchor
    lead = "".join(str(bit(ln2, i)) for i in range(20))
    assert lead == "10110001011100100001", lead
    print("anchor OK: ln 2 leads", lead)

    xb = [bit(ln2, i) for i in range(DEPTH + 8)]
    yb = [bit(ln3, i) for i in range(DEPTH + 8)]
    zbits = [[bit(Z, i) for i in range(DEPTH + 8)] for Z in Zs]

    def true_carry(Z, a, b, m):
        return floor_at(Z, m) - a * floor_at(ln2, m) - b * floor_at(ln3, m)

    # 2+3. signed carry window + column identity
    min_carry_seen = {}
    for (a, b, w), Z, zb in zip(channels, Zs, zbits):
        off = max(-a, 0) + max(-b, 0)
        pos_sum = max(a, 0) + max(b, 0)
        mc = 10 ** 9
        for m in range(1, DEPTH):
            T_m = true_carry(Z, a, b, m)
            assert -off <= T_m <= pos_sum - 1, (a, b, m, T_m)
            mc = min(mc, T_m)
            T_prev = true_carry(Z, a, b, m - 1)
            d_m = zb[m - 1]
            assert a * xb[m - 1] + b * yb[m - 1] + T_m == d_m + 2 * T_prev, \
                (a, b, m)
        min_carry_seen[(a, b)] = mc
    print(f"signed carry window + column identity OK over 1..{DEPTH - 1}; "
          f"min carries: {min_carry_seen}")

    # 6. an actual borrow fires (signed families only)
    if any(o > 0 for o in fam.offs):
        assert any(v < 0 for v in min_carry_seen.values()), min_carry_seen
        print("negative-carry (borrow) positions exercised:",
              {k: v for k, v in min_carry_seen.items() if v < 0})
    else:
        print("all-nonnegative family: no borrow expected")

    # 4+5. shadowing against pred
    def state_at(m: int) -> int:
        s, mult = 0, 1
        for (a, b, w), Z, zb, wsz, n, off in zip(
                channels, Zs, zbits, fam.win_sizes, fam.sizes, fam.offs):
            c = true_carry(Z, a, b, m) + off      # offset encoding
            wcode = sum(zb[m + j] << j for j in range(len(w) - 1))
            s += (c * wsz + wcode) * mult
            mult *= n
        return s

    def occurs_at(m: int) -> bool:
        return any(all(zb[m + j] == int(w[j]) for j in range(len(w)))
                   for (a, b, w), zb in zip(channels, zbits))

    occ = [0] * len(channels)
    legal = illegal = 0
    for m in range(0, DEPTH - 8):
        sigma = xb[m] + 2 * yb[m]
        s, s2 = state_at(m), state_at(m + 1)
        p = fam.pred(sigma, s2)
        if occurs_at(m):
            assert p == -1, f"pos {m}: word occurred but pred gave {p}"
            illegal += 1
        else:
            assert p == s, f"pos {m}: shadowing failed pred={p} truth={s}"
            legal += 1
        for i, ((a, b, w), zb) in enumerate(zip(channels, zbits)):
            if all(zb[m + j] == int(w[j]) for j in range(len(w))):
                occ[i] += 1
    print(f"shadowing OK over 0..{DEPTH - 9}: {legal} legal steps, "
          f"{illegal} word-occurrence breaks")
    assert all(c > 0 for c in occ), occ
    print(f"every channel word occurs (counts: {occ})")
    print("ALL SIGNED SELF-TESTS PASS")


if __name__ == "__main__":
    import sys
    main(sys.argv[1] if len(sys.argv) > 1 else "musical")
