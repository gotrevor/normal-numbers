#!/usr/bin/env -S uv run --quiet --with pytest python3 -m pytest
"""Known-answer tests: values printed in Fonga 2608.27802 (worked example + table, p.10-11)
and Brier et al. 2110.04263 Table 3 / Table 4 (whose '(4,7,8)' row is a typo for {2,7,8}:
4*7*8 = 224, not 112)."""
import subprocess, json, time, pathlib, sys
sys.path.insert(0, str(pathlib.Path(__file__).parent))
from fonga_tmax import tmax_exact

HERE = pathlib.Path(__file__).parent

def tm(D):
    return tmax_exact(D, time.time() + 60)[0]

def test_fonga_table():
    assert tm({4: 2, 7: 1}) == 7          # witness 111744 = 3^2 * 97 * 2^7
    assert tm({2: 4, 7: 1}) == 13         # 172122112
    assert tm({2: 2, 4: 1, 7: 1}) == 15   # 211111411712
    assert tm({2: 1, 7: 1, 8: 1}) == 9    # 1178112

def test_witnesses_by_hand():
    assert 111744 == 9 * 97 * 2**7
    assert 211111411712 % 2**15 == 0 and 211111411712 % 2**16 != 0

def test_brier_table3_reproduced():
    subprocess.run([str(HERE / "graphs.py"), "60"], cwd=HERE, check=True, capture_output=True)
    data = json.load(open(HERE / "families.json"))
    want = {"2": (33, 1117, 30), "4": (9, 1062, 32), "6": (84, 6377, 37), "8": (51, 4774, 45)}
    for d, (nU, nF, kmax) in want.items():
        assert len(data[d]["U"]) == nU
        assert len(data[d]["fams"]) == nF
        assert max(f[2] for f in data[d]["fams"]) == kmax
    assert data["4"]["U"] == [4, 14, 27, 72, 98, 189, 294, 1161216, 2**23 * 3**7 * 7]

def _brute_max_v2(D, maxlen):
    """independent instrument: place the exceptional digits at every position set of an
    all-ones string of length <= maxlen and take the max 2-adic valuation directly."""
    import itertools
    digs = [d for d, c in D.items() for _ in range(c)]
    best = 0
    for L in range(len(digs), maxlen + 1):
        for pos in itertools.permutations(range(L), len(digs)):
            x = (10**L - 1) // 9 + sum((d - 1) * 10**p for d, p in zip(digs, pos))
            best = max(best, (x & -x).bit_length() - 1)
    return best

def test_tmax_matches_bruteforce_small():
    # max v2 over the family is attained by a number of length <= tmax+1 (positions <= v2/e);
    # brute force up to length 9 must agree with the recursion for these small families.
    for D in ({4: 2, 7: 1}, {2: 1, 7: 1, 8: 1}, {6: 1, 9: 1}, {8: 2}):
        assert _brute_max_v2(D, 9) == tm(D)
