#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# ///
"""Exact cutoff audit.  No assertion about asymptotic distribution of π.

Control: cutoff 4 reproduces the proved 64/p exit collapse.
Candidate: cutoff 6 preserves unique denominators but introduces cubic residues.
Also check the finite-prime dyadic regrouping suggested by the rho recurrence.
Run: uv run scripts/pi_route2_cutoff_review.py
"""
from fractions import Fraction
from math import isqrt


def primes_below(bound):
    sieve = bytearray(b'\x01') * bound
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(bound - 1) + 1):
        if sieve[p]:
            sieve[p*p:bound:p] = b'\x00' * len(range(p*p, bound, p))
    return [p for p in range(2, bound) if sieve[p]]


def exit_piece(slope, p):
    assert p % 4 == 1
    n, j = p // slope, p // 8
    if j >= n:
        return None  # never entered this narrower reservoir
    c = 4 if p % 8 == 1 else -1
    return (c * pow(16, n + 1 - j, p)) % p


def run():
    ps = [p for p in primes_below(20001) if p % 4 == 1]
    assert all(exit_piece(4, p) == 64 % p for p in ps)
    sixth = [(p, exit_piece(6, p)) for p in ps if exit_piece(6, p) is not None]
    for p, r in sixth:
        rhs = 64**3 if p % 6 == 1 else 1024
        assert pow(r, 3, p) == rhs % p
    assert exit_piece(6, 89) == 39  # sole exit at n=14; other candidate 85 is composite
    assert exit_piece(6, 13) == 4
    assert exit_piece(6, 13) != 64 % 13
    for p in ps:
        if p > 200:
            break
        sign = 1 if p % 8 == 1 else -1
        numerator = sign * 2**((p-1)//2) - 1
        assert numerator % p == 0
        original = Fraction(4 if sign == 1 else -1, p * 16**(p//8))
        original -= Fraction(4, p * 16**((p-1)//4))
        dyadic = Fraction(4 * (numerator//p), 2**(p-1))
        assert original == dyadic
        assert dyadic.denominator & (dyadic.denominator - 1) == 0
    old_matches = sum(r == 64 % p for p, r in sixth)
    bulk = sum(p/4 <= r <= 3*p/4 for p, r in sixth)
    print(f'cutoff-4 control: {len(ps)}/{len(ps)} exact 64 residues')
    print(f'cutoff-6: {len(sixth)}/{len(sixth)} cubic identities; '
          f'{old_matches} retain 64 residue; {bulk} residues in [p/4,3p/4]')
    print('exact sole-exit witness: n=14, p=89, fractional transfer=39/89')
    print('finite-prime rho regrouping: exact rational checks passed for p<=200')


if __name__ == '__main__':
    run()
