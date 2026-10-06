from stretch_exact_count import cantor_ints, low_residue_count, riesz_l1


def test_cantor_ints_two():
    # by hand: digits (d1 d0) in {0,2}^2 -> 0, 2, 6, 8 (matches Lean cantorInts_two)
    assert cantor_ints(2) == [0, 2, 6, 8]


def test_low_residue_hand():
    # b=2, k=1, q=1: residues P mod 9 in [0,3) or (6,9): P in {0, 2, 8} -> 3 <= 2*2
    assert low_residue_count(2, 1, 1) == 3
    # b=2, k=1, q=2: 2P mod 9 = 0, 4, 3, 7 -> only 0 and 7 qualify
    assert low_residue_count(2, 1, 2) == 2


def test_low_residue_bound():
    for b in range(1, 8):
        for k in range(0, b + 1):
            for q in range(1, 60):
                if q % 3:
                    assert low_residue_count(b, k, q) <= 2 * 2 ** k


def test_riesz_l1_hand():
    # b=1: s=0,1,2: |1+e(0)|=2, |1+e(2/3)|=1, |1+e(4/3)|=1 -> 4/3
    assert abs(riesz_l1(1) - 4 / 3) < 1e-12
    for b in range(2, 8):
        assert riesz_l1(b) <= (4 / 3) ** b + 1e-9
