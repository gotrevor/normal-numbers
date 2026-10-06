import math

from stretch_farey_perr import (farey_set, per_r_pairs, solutions, threshold, window_set,
                                worst_exponent)


def test_solutions_hand():
    # b=2, q=2: 2*8 = 16 = 9 + 7, so P q = 7 mod 9 has the single solution P = 8
    assert solutions(2, 7, 2) == [8]
    # q=3, r=6 mod 9: 3P = 6 mod 9 iff P = 2 mod 3 -> P in {2, 5, 8}
    assert sorted(solutions(3, 6, 2)) == [2, 5, 8]


def test_window_hand():
    # b=2, m=0: q=1 has bound 9, so every nonzero Cantor numerator 2, 6, 8 is a hit (r = P or
    # P - 9); P=0 only has r=0.  q=2 adds nothing new.
    assert window_set(2, 0, 2.3) == {2, 6, 8}


def test_farey_hand():
    # b=2, m=0: rationals 0, 1/2, 1; 8/9 is exactly 1/9 from 1 (not < 1/9): empty
    assert farey_set(2, 0) == set()
    # b=2, m=1 (q < 9): 2/9 vs 1/4 (|8-9|/36 = 1/36), 6/9 vs 3/4 (1/12), 8/9 vs 7/8 (1/72)
    F = farey_set(2, 1)
    assert {2, 6, 8} <= F and 0 not in F


def test_farey_bound():
    # Lean claim: at most 2^(2m+3) Cantor numerators within 3^-b of a rational p/q != P/3^b
    for b in range(1, 9):
        for m in range(0, b):
            assert len(farey_set(b, m)) <= 2 ** (2 * m + 3)


def test_window_in_farey():
    # tau m >= b: q^-tau <= 3^-b, so every window hit is a Farey-set element
    for (b, m, tau) in [(8, 4, 2.2), (9, 4, 2.3), (9, 4, 2.5)]:
        assert tau * m >= b
        assert window_set(b, m, tau) <= farey_set(b, m)


def test_per_r_injective():
    # (r, P mod 3^(m+1)) determines P when 3 does not divide P q
    for (b, m, tau) in [(8, 4, 2.2), (9, 5, 2.3), (10, 5, 2.3), (10, 6, 2.2)]:
        pairs, inj = per_r_pairs(b, m, tau)
        assert inj


def test_threshold():
    # 3 - log_3 2: below it the combined bound min(4^m, R 2^m) reaches 2^b at some m
    assert abs(threshold() - 2.36907) < 1e-4
    assert worst_exponent(threshold() + 0.02) < 0
    assert worst_exponent(threshold() - 0.02) > 0
