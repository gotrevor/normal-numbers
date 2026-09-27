"""Real-CLI regression controls.  Expected fractions below are hand calculations.

Run `./probes/swingc2_window.py test -q`.  These test the finite encoder, not
the infinite joint-disjunctivity claim or the external prime-distribution input.
"""
import json
import subprocess
import sys
from pathlib import Path

CLI = Path(__file__).with_name('swingc2_window.py')


def run(*args, code=0):
    p = subprocess.run([sys.executable, str(CLI), *map(str, args)], capture_output=True, text=True)
    assert p.returncode == code, p.stderr + p.stdout
    return json.loads(p.stdout)


def test_dependent_bases_same_position():
    # 58/8 = 7+1/4, 58/64 = 29/32.  These spell 0 and 3.
    d = run('encode', '--bases', 2, 4, '--values', 0, 3, '--lengths', 1, 1)
    assert (d['depth'], d['a'], d['divisor_count']) == (3, 29, 58)
    assert d['coordinates'] == ['1/4', '29/32']


def test_coprime_bases():
    # 22/8 = 2+3/4, 22/27 is in the middle half of ternary [2/3,1).
    d = run('encode', '--bases', 2, 3, '--values', 1, 2, '--lengths', 1, 1)
    assert (d['depth'], d['a']) == (3, 11)
    assert d['coordinates'] == ['3/4', '22/27']


def test_resonance_can_occur_at_shallow_depth():
    # 2*(1/4 - 4/16)=0, but 2*(1/8 - 4/64)=1/8.
    assert run('character', '--bases', 2, 4, '--coefficients', 1, -4, '--depth', 2)['mean'] == 1
    d = run('character', '--bases', 2, 4, '--coefficients', 1, -4, '--depth', 3)
    assert d == {'theta': '1/8', 'period': 32, 'mean': 0}


def test_equal_base_obstruction_persists():
    assert run('character', '--bases', 3, 3, '--coefficients', 1, -1, '--depth', 12)['mean'] == 1
    p = subprocess.run([sys.executable, str(CLI), 'encode', '--bases', '2', '2',
                        '--values', '0', '1', '--lengths', '1', '1'], capture_output=True, text=True)
    assert p.returncode == 2 and 'distinct bases' in p.stderr


def test_zero_character_control():
    assert run('character', '--bases', 2, 3, 4, '--coefficients', 0, 0, 0, '--depth', 3)['mean'] == 1


def test_period_cap_is_not_a_refutation():
    d = run('encode', '--bases', 2, 4, '--values', 0, 3, '--lengths', 1, 1,
            '--max-period', 8, code=3)
    assert d == {'status': 'period_cap', 'depth': 3, 'period': 32, 'examined_depths': [1, 2]}


def test_depth_cap_is_not_a_refutation():
    d = run('encode', '--bases', 2, 4, '--values', 0, 3, '--lengths', 1, 1,
            '--max-depth', 2, code=2)
    assert d == {'status': 'no_witness_within_depth_cap', 'examined_depths': [1, 2]}


def test_all_one_digit_pairs_for_dependent_bases():
    from fractions import Fraction
    for x in range(2):
        for y in range(4):
            d = run('encode', '--bases', 2, 4, '--values', x, y, '--lengths', 1, 1)
            p, q = map(Fraction, d['coordinates'])
            assert Fraction(x, 2) < p < Fraction(x+1, 2)
            assert Fraction(y, 4) < q < Fraction(y+1, 4)
