"""Tests for independence_relative.py, driven through the CLI.

Every expected verdict is worked out by hand in the comment beside it, never captured from the
tool.  Run: `uv run --with pytest pytest experiments/test_independence_relative.py`.
"""

import subprocess
import sys
from pathlib import Path

TOOL = Path(__file__).parent / "independence_relative.py"


def check(g, spec):
    out = subprocess.run([sys.executable, str(TOOL), "check", str(g), spec],
                         capture_output=True, text=True, check=True).stdout.strip()
    return out


def test_c4_collapses():
    # C4 is a proved universal family (EVIDENCE-2026-08-29 tier 2): every live SCC is a cycle.
    assert check(3, "0,1,0 0,3,2 3,1,0 1,1,2") == "('collapse', None)"


def test_both_avoid_zero_binary_collapses():
    # X and Y avoid 0 in binary: both tails are 111..., so the only live path is one cycle.
    assert check(2, "1,0,0 0,1,0") == "('collapse', None)"


def test_difference_channel_is_degenerate():
    # X - Y avoids 0 in binary: its tail is 111..., so X - Y is rational, X free.
    # Fat SCC (X free), degenerate along the direction (1, -1).
    assert check(2, "1,-1,0") == "('indep', [(1, -1)])"


def test_cantor_channel_is_open():
    # X avoids 1 in base 3 (middle-thirds Cantor), Y unconstrained: positive entropy in
    # X alone, and no rational relation is forced.  Must NOT be certified.
    assert check(3, "1,0,1") == "('open', 1)"


def test_ternary_line_family():
    # Hand proof in IndependenceRelative.ternary_line: X avoids 2, Y avoids 1, Y - X avoids 2
    # forces the tails of Y and 2X to agree, i.e. 2X - Y rational.  Witness (2, -1).
    assert check(3, "1,0,2 0,1,1 -1,1,2") == "('indep', [(2, -1)])"
