"""Persistent check for experiments/t3c_critical_runs.py (T3c verdict, 2026-09-20).

Every expected number below was worked out BY HAND, not captured from the probe:

* K = 4: 3^29 = 68 630 377 364 883 ~ 6.9e13 < 2^48 ~ 2.8e14, while
  3^30 ~ 2.06e14 > 2^47 ~ 1.4e14, so the critical position is n* = 33
  (a = 29, c = 48).  D = 2^48 - 3^29 ~ 2.1e14 and 6D > 2^48, so no leading 5: L = 0.
* K = 5: a = 92, c = 146: log2(3^92) = 92 * 1.58496 = 145.82 < 146, and a = 93 gives
  147.40 > 145, so n* = 97.  D/2^146 = 1 - 2^-0.18 = 0.117; 6D <= 2^146 but
  36D > 2^146, so exactly one leading 5: L = 1.
* K = 8: Bailey-Borwein's forced zero-run in block 8 occupies positions 2188..2543
  (length 356, N2 probe); the critical position is where 3^a first exceeds 2^c/6,
  i.e. the LAST position of that run, so n* = 2543.

Run: uv run --with pytest pytest -q experiments/test_t3c_critical_runs.py
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from t3c_critical_runs import critical, run_of_fives, alpha_digits_base6  # noqa: E402


def test_critical_positions_by_hand():
    assert critical(4) == (33, 29, 48)
    assert critical(5) == (97, 92, 146)
    assert critical(8)[0] == 2543  # end of the BB-2012 zero-run 2188 + 356 - 1


def test_runs_by_hand():
    for K, L in [(4, 0), (5, 1)]:
        n, a, c = critical(K)
        assert run_of_fives((1 << c) - 3 ** a, c) == L


def test_readout_run_matches_true_digit_stream():
    """Independent of the readout theorem: count 5s in alpha's actual digits."""
    for K in (5, 6, 7, 8):
        n, a, c = critical(K)
        L = run_of_fives((1 << c) - 3 ** a, c)
        digs = alpha_digits_base6(n + L + 3)
        run = 0
        while digs[n + run] == 5:
            run += 1
        assert run == L


def test_cli_runs():
    out = subprocess.run([os.path.join(HERE, "t3c_critical_runs.py"), "6"],
                         capture_output=True, text=True, check=True).stdout
    assert " 5       97       92      146      1" in out
