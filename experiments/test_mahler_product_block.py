"""Persistent check for experiments/mahler_product_block.py (2026-10-05).

Every expectation comes from a HAND argument or a KERNEL-CHECKED Lean theorem, never from
the probe's own output:

* Base 2, S = {1}: an irrational has both binary digits i.o. (avoiding one = constant tail),
  so {1} is a base-2 block.
* Base 3, S = {1}: NOT a block - a ternary expansion over {0, 2} that is not eventually
  periodic is irrational and avoids 1.
* Base 3, {1, 2}, digit 1: the five-line hand proof (docs/mahler-sets-2026-08-29.md): on a
  {0,2}-tail, 2x emits 1 at every 20 / 02 junction, so avoiding 1 in both forces a constant tail.
* Base 3, {1, 2} is NOT a block: Liouville witness B = 1, digits(1) = {1}, digits(2) = {2},
  neither has both nonzero digits.
* Base 3, {2, 11} and {4, 22} ARE blocks: Lean `c2_product_block` and `IsProductBlock.image_mul`.
* Base 5, M(5,1) = 6 (Lean `mahler_M_five_eq_six`): {1..6} forces every digit, and {1..5} does
  NOT force digit 1 (the Lean lower-bound construction is a real irrational, so a collapse there
  would be a checker bug).
* 194 = 1*125 + 2*25 + 3*5 + 4 = 1234 in base 5, the smallest number using all four nonzero
  base-5 digits (fewest digits, then smallest leading digit, ascending).

Run: uv run --with pytest --with scipy --with numpy pytest -q experiments/test_mahler_product_block.py
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from mahler_product_block import (  # noqa: E402
    covers, digits, failing, per_digit, refine, root, uncovered)


def collapses(g, chans):
    core, col = root(g), False
    for m, d in chans:
        core, c = refine(g, core, m, d)
        col = col or c
    return col


def test_base2_one_is_block():
    assert failing(2, [1]) == []


def test_base3_one_is_not_block():
    assert failing(3, [1], limit=1) != []


def test_base3_digit1_hand_proof():
    assert per_digit(3, [1, 2], 1)


def test_base3_one_two_not_block():
    assert failing(3, [1, 2], limit=1) != []
    assert uncovered([1, 2], 3, 10)[0] == 1


def test_base3_lean_blocks():
    assert failing(3, [2, 11]) == []
    assert failing(3, [4, 22]) == []


def test_base5_mahler_constant_six():
    assert all(per_digit(5, [1, 2, 3, 4, 5, 6], d) for d in range(5))
    assert not per_digit(5, [1, 2, 3, 4, 5], 1)


def test_liouville_filter_194():
    assert digits(194, 5) == {1, 2, 3, 4}
    assert covers(194, 1, 5)
    assert not covers(193, 1, 5)


def test_complement_symmetry():
    # x -> -x complements every digit, so (d_m) collapses iff (g-1-d_m) does.
    rng = random.Random(7)
    for _ in range(60):
        S = rng.sample([1, 2, 3, 4, 6, 7, 8, 9, 11], 3)
        ds = [rng.randrange(5) for _ in S]
        assert collapses(5, list(zip(S, ds))) == collapses(5, [(m, 4 - d) for m, d in zip(S, ds)])


# --- The compiled port (experiments/mahler_block_rs) must reach the same hand verdicts. ---
import subprocess  # noqa: E402

RS = os.path.join(HERE, "mahler_block_rs")


def rs_failing(g, S, *flags):
    subprocess.run(["cargo", "build", "--release", "-q"], cwd=RS, check=True)
    out = subprocess.run([os.path.join(RS, "target", "release", "mahler_block"), "failing",
                          str(g), ",".join(map(str, S)), *flags],
                         capture_output=True, text=True, check=True).stdout
    return int(out.split()[1])


def test_rust_hand_verdicts():
    assert rs_failing(2, [1]) == 0                      # base 2: {1} is a block
    assert rs_failing(3, [1], "--nosym") > 0            # base 3: {1} is not
    assert rs_failing(3, [1, 2], "--nosym") > 0         # Liouville B = 1 kills {1, 2}
    assert rs_failing(3, [2, 11]) == 0                  # Lean c2_product_block
    assert rs_failing(3, [4, 22]) == 0                  # Lean image_mul


def test_rust_matches_python_counts():
    # Agreement between two implementations (not a hand value): the port is a port.
    for g, S in ((5, [1, 2, 3, 4, 8]), (5, [1, 2, 3, 4, 8, 16]), (3, [1, 2])):
        assert rs_failing(g, S) == len(failing(g, S))


def rs_count(*args):
    """First integer after the leading word of a Rust subcommand's output."""
    subprocess.run(["cargo", "build", "--release", "-q"], cwd=RS, check=True)
    out = subprocess.run([os.path.join(RS, "target", "release", "mahler_block"),
                          *map(str, args)], capture_output=True, text=True, check=True).stdout
    return int(out.split()[1])


def test_rust_rung_verdicts():
    # A rung 2 -> g is a product block: base 3 has 3 digits, so {2, 11} is a rung 2 -> 3.
    assert rs_count("lift", 3, 2, 3, "2,11") == 0
    assert rs_count("lift", 3, 2, 3, "2") > 0
    # KIN = 1 keeps every non-cycle SCC, which is exactly the block checker's collapse test.
    for S in ("2,3,7", "3,4,6,7"):
        assert rs_count("lift", 5, 1, 5, S) == rs_count("failing", 5, S)


def test_rust_word_verdicts():
    # K = 1 is the digit checker.
    assert rs_count("wfail", 3, 1, "2,11") == 0
    assert rs_count("wfail", 2, 1, "1") == 0
    # Binary 2-words, S = {1}, by hand: up to complement the avoided word is 00 or 01.  Avoiding
    # 01 forces 1^a 0^inf (rational); avoiding 00 leaves the golden-mean shift (irrational
    # points).  So exactly one failing assignment, ["00"].
    assert rs_count("wfail", 2, 2, "1") == 1
    # Binary 3-words, Liouville X = sum 2^-(i!): m X shows the bits of m between zero gaps, and
    # no m < 23 = 10111_2 has all eight 3-words in 0^3 m 0^3 (a 22-row enumeration; 2m adds
    # nothing), so every S of odd m < 23 fails.
    assert rs_count("wfail", 2, 3, ",".join(map(str, range(1, 23, 2)))) > 0


def test_rust_x_3x_5x_hand_proof():
    # Hand proof in isWordBlock_two_two_one_three_five's docstring: an irrational word in the
    # tokens 01 and 001 beats {1, 3} (x avoids 11, 3x avoids 00); adding 5 closes it.
    assert rs_count("wfail", 2, 2, "1,3") > 0
    assert rs_count("wfail", 2, 2, "1,3,5") == 0
