"""Tests for qspan_digit_probe.py, values worked out by hand; the CLI is driven via subprocess."""
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import qspan_digit_probe as P  # noqa: E402


def test_combo_sum_no_carry():
    # x = 0.1234, y = 0.0101 -> x + y = 0.1335
    assert P.combo_digits("1234", "0101", 1, 1, 1, 4) == "1335"


def test_combo_division():
    # x = 0.1000, (x)/7 = 0.0142857... -> first 4 digits 0142
    assert P.combo_digits("1000", "0000", 1, 0, 7, 4) == "0142"


def test_combo_negative_takes_fractional_part():
    # y - x with x = 0.2, y = 0.1: -0.1 -> fractional part 0.9
    assert P.combo_digits("2", "1", -1, 1, 1, 1) == "9"


def test_block_deviation_uniform_and_constant():
    assert P.block_deviation("0123456789", 1) == 0.0
    # all 7s: freq(7) = 1, deviation 0.9
    assert abs(P.block_deviation("7777777777", 1) - 0.9) < 1e-12


def test_cli_runs():
    out = subprocess.run([sys.executable, str(HERE / "qspan_digit_probe.py"), "--n", "2000",
                          "--amax", "1", "--qmax", "2"], capture_output=True, text=True, check=True)
    assert "combinations" in out.stdout


def test_nu_hat_hand_values():
    # x + y, h = 1: |phi(0.1)|^2 |phi(0.01)|^2 ... = 0.6472^2 * 0.9959^2 * ... ~ 0.415 (by hand)
    assert abs(abs(P.nu_hat("01234", 1, 1, 1)) - 0.415) < 0.003
    # 4x + 5y, h = 1: the i = 1 factor phi(0.4) vanishes (5 * 0.4 is an integer, 0.4 is not)
    assert abs(P.nu_hat("01234", 4, 5, 1)) < 1e-12
    # 4x + 5y, h = 25: 0.2 * 0.2 * (0.647 * 0.483) * ~0.97 ~ 0.012 (by hand)
    assert 0.010 < abs(P.nu_hat("01234", 4, 5, 25)) < 0.014
