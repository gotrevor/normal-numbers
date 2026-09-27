#!/usr/bin/env -S uv run --quiet python3
"""SubLeafA probe (SwingC2): does the padded divisor-count window of E_b = sum_m tau(m)/b^m
hit every residue?  Equivalently: does every length-L word occur in base-b digits of E_b?
Known-answer check: the tau-Lambert digits must agree with an exact Fraction evaluation of
sum_{n>=1} 1/(b^n - 1) (the two series are equal), e.g. E_10 = 0.122324243426..."""
import sys

def tau_sieve(M):
    t = [0]*(M+1)
    for d in range(1, M+1):
        for m in range(d, M+1, d):
            t[m] += 1
    return t

def digits(b, M, guard=64):
    """First M base-b digits after the point of E_b = sum_{m>=1} tau(m)/b^m."""
    T = M + guard
    t = tau_sieve(T)
    S = 0
    for m in range(1, T+1):
        S += t[m] * b**(T-m)
    S //= b**guard           # = floor(E_b * b^M)
    ds = []
    for _ in range(M):
        S, r = divmod(S, b)
        ds.append(r)
    return ds[::-1]


def legacy_scan():
    # --- known-answer check -------------------------------------------------------
    from fractions import Fraction as F
    def ref(b, M):
        x = sum(F(1, b**n - 1) for n in range(1, 400))
        ds = []
        for _ in range(M):
            x *= b; d = int(x); ds.append(d); x -= d
        return ds
    assert digits(10, 12) == ref(10, 12) == [1,2,2,3,2,4,2,4,3,4,2,6]
    assert digits(3, 12) == ref(3, 12) == [2,0,0,1,0,2,0,2,1,2,1,1]
    print("known-answer OK: base 10 ->", ''.join(map(str, digits(10, 12))),
          " base 3 ->", ''.join(map(str, digits(3, 12))))

    # --- the probe ----------------------------------------------------------------
    for b in (3, 4, 10):
        M = 200000
        ds = digits(b, M)
        for L in range(1, 5):
            seen = set()
            for i in range(M-L+1):
                v = 0
                for j in range(L):
                    v = v*b + ds[i+j]
                seen.add(v)
            tot = b**L
            miss = tot - len(seen)
            first = None
            if miss == 0:
                # position by which all words have appeared
                seen2 = set();
                for i in range(M-L+1):
                    v = 0
                    for j in range(L):
                        v = v*b + ds[i+j]
                    seen2.add(v)
                    if len(seen2) == tot:
                        first = i; break
            print(f"b={b:2d} L={L}: {len(seen)}/{tot} words seen"
              + (f", all by position {first}" if first is not None else f", MISSING {miss}"))


def main():
    """Exact encoding controls for the simultaneous Lambert research note.

    No arguments retains the original digit census.  `encode` tests the NEW
    finite encoding lemma, not the infinite arithmetic theorem.  `character`
    evaluates the exact cyclic Fourier mean by geometric-sum orthogonality.
    """
    import argparse
    import json
    import math
    import os
    from fractions import Fraction
    from pathlib import Path

    if len(sys.argv) == 1:
        legacy_scan()
        return
    if sys.argv[1] == 'test':
        os.execvp('uv', ['uv', 'run', '--quiet', '--with', 'pytest', 'python3',
                        '-m', 'pytest', str(Path(__file__).with_name('test_swingc2_window.py')),
                        *sys.argv[2:]])
    parser = argparse.ArgumentParser(description=main.__doc__)
    subs = parser.add_subparsers(dest='command', required=True)
    enc = subs.add_parser('encode', help='find one even divisor count encoding all cylinders')
    enc.add_argument('--bases', nargs='+', type=int, required=True)
    enc.add_argument('--values', nargs='+', type=int, required=True)
    enc.add_argument('--lengths', nargs='+', type=int, required=True)
    enc.add_argument('--max-depth', type=int, default=8)
    enc.add_argument('--max-period', type=int, default=1000000)
    char = subs.add_parser('character', help='exact mean of a character on the even-count lattice')
    char.add_argument('--bases', nargs='+', type=int, required=True)
    char.add_argument('--coefficients', nargs='+', type=int, required=True)
    char.add_argument('--depth', type=int, required=True)
    args = parser.parse_args()
    if any(b < 2 for b in args.bases):
        parser.error('bases must be at least 2')
    if args.command == 'character':
        if len(args.bases) != len(args.coefficients) or args.depth < 1:
            parser.error('one coefficient per base and positive depth required')
        moduli = [b**args.depth for b in args.bases]
        theta = 2 * sum((Fraction(h, q) for h, q in zip(args.coefficients, moduli)), Fraction())
        modulus = math.lcm(*moduli)
        print(json.dumps({'theta': str(theta), 'period': modulus // math.gcd(modulus, 2),
                          'mean': int(theta.denominator == 1)}))
        return
    if len(set(args.bases)) != len(args.bases):
        parser.error('encoding theorem requires distinct bases')
    if not len(args.bases) == len(args.values) == len(args.lengths):
        parser.error('one value and length per base required')
    if args.max_depth < 1 or args.max_period < 1:
        parser.error('depth and period caps must be positive')
    if any(ell < 1 or not 0 <= v < b**ell
           for b, v, ell in zip(args.bases, args.values, args.lengths)):
        parser.error('positive lengths and values in their digit ranges required')
    intervals = [(Fraction(4*v+1, 4*b**ell), Fraction(4*v+3, 4*b**ell))
                 for b, v, ell in zip(args.bases, args.values, args.lengths)]
    examined = []
    for depth in range(1, args.max_depth + 1):
        moduli = [b**depth for b in args.bases]
        modulus = math.lcm(*moduli)
        period = modulus // math.gcd(modulus, 2)
        if period > args.max_period:
            print(json.dumps({'status': 'period_cap', 'depth': depth, 'period': period,
                              'examined_depths': examined}))
            raise SystemExit(3)
        for a in range(1, period + 1):
            coords = [Fraction((2*a) % q, q) for q in moduli]
            if all(lo <= x <= hi for x, (lo, hi) in zip(coords, intervals)):
                # Raising a by its period preserves all coordinates and makes a >= 2.
                if a < 2:
                    a += period
                print(json.dumps({'status': 'witness', 'depth': depth,
                                  'survivor_offset': depth-1, 'a': a, 'divisor_count': 2*a,
                                  'period': period, 'coordinates': list(map(str, coords))}))
                return
        examined.append(depth)
    print(json.dumps({'status': 'no_witness_within_depth_cap', 'examined_depths': examined}))
    raise SystemExit(2)


if __name__ == '__main__':
    main()
