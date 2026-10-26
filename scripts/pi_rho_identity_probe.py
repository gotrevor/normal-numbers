#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["mpmath==1.3.0"]
# ///
"""Bounded PSLQ search for rho, with exact rational truncation bounds.

This is a numerical candidate search, not a proof of absence of identities.
Two implementations compute the recurrence sum and its prime regrouping.
Known-answer and deliberately perturbed controls validate detection and rejection.
"""
from __future__ import annotations
import argparse
import contextlib
from fractions import Fraction
import io
import json
from math import isqrt
from pathlib import Path
import time

from mpmath import mp


def sieve(bound: int) -> bytearray:
    prime = bytearray(b'\x01') * (bound + 1)
    prime[:2] = b'\x00\x00'
    for p in range(2, isqrt(bound) + 1):
        if prime[p]:
            prime[p*p:bound+1:p] = b'\x00' * len(range(p*p, bound+1, p))
    return prime


def rho_intervals(n: int):
    prime = sieve(8*n + 5)
    recurrence = Fraction(0)
    power = 1
    for k in range(n):
        kick = -Fraction(64, 4*k+1) if prime[4*k+1] else Fraction(0)
        if prime[8*k+1] and 4*(k+1) < 8*k+1:
            kick += Fraction(64, 8*k+1)
        if prime[8*k+5] and 4*(k+1) < 8*k+5:
            kick -= Fraction(16, 8*k+5)
        power *= 16
        recurrence += kick / power
    # From the proved |kick_k| <= 144/(k+1) and a geometric sum.
    err_recurrence = Fraction(10, (n+1) * 16**n)
    dyadic = Fraction(0)
    for p in range(5, 8*n+1, 4):
        if not prime[p]:
            continue
        sign = 1 if p % 8 == 1 else -1
        numerator = sign * 2**((p-1)//2) - 1
        assert numerator % p == 0
        dyadic += Fraction(4 * (numerator // p), 2**(p-1))
    # Bounding even the omitted composite-index terms gives
    # sum_{m>=2n} 8*4^-m = (32/3)*16^-n < 12*16^-n.
    err_dyadic = Fraction(12, 16**n)
    lo = max(recurrence - err_recurrence, dyadic - err_dyadic)
    hi = min(recurrence + err_recurrence, dyadic + err_dyadic)
    assert lo <= hi, 'The two bounded arithmetic computations disagree'
    return recurrence, dyadic, err_recurrence, err_dyadic, lo, hi


def as_mp(q: Fraction):
    return mp.mpf(q.numerator) / q.denominator


def decimal_integer(v: int, digits: int) -> str:
    sign = '-' if v < 0 else ''
    s = str(abs(v)).zfill(digits + 1)
    return sign + s[:-digits] + '.' + s[-digits:]


def outward_decimals(lo: Fraction, hi: Fraction, digits: int):
    scale = 10**digits
    a = lo.numerator * scale // lo.denominator
    b = -((-hi.numerator * scale) // hi.denominator)
    return decimal_integer(a, digits), decimal_integer(b, digits)


def basis_specs():
    return [
        ('rational', ['rho', '1'], 10**20),
        ('pi_affine', ['rho', 'pi', '1'], 10**12),
        ('pi_log2', ['rho', 'pi', 'log2', '1'], 10**10),
        ('small_logs', ['rho', 'pi', 'log2', 'log3', 'log5', 'log7', '1'], 10**8),
        ('arctan_logs', ['rho', 'pi', 'atan_half', 'log2', 'log3', 'log5', 'log7', 'log17', '1'], 10**6),
        ('other_constants', ['rho', 'pi', 'pi_squared', 'sqrt2', 'sqrt3', 'catalan', 'zeta3', '1'], 10**6),
        ('quadratic_pi', ['rho', 'rho_squared', 'rho_pi', 'pi', 'pi_squared', '1'], 10**6),
    ] + [(f'algebraic_degree_{d}', ['1'] + [f'rho_power_{j}' for j in range(1, d+1)], 10**8)
         for d in range(2, 7)]


def constants(rho):
    values = {'rho': rho, '1': mp.mpf(1), 'pi': mp.pi, 'pi_squared': mp.pi**2,
              'sqrt2': mp.sqrt(2), 'sqrt3': mp.sqrt(3), 'catalan': mp.catalan,
              'zeta3': mp.zeta(3), 'atan_half': mp.atan(mp.mpf(1)/2),
              'rho_squared': rho**2, 'rho_pi': rho*mp.pi}
    values.update({f'log{n}': mp.log(n) for n in [2, 3, 5, 7, 17]})
    values.update({f'rho_power_{j}': rho**j for j in range(1, 7)})
    return values


def controlled_pslq(dps, logs):
    fake = (7*mp.pi - 3*mp.log(2) + 5)/11
    tol = mp.mpf(10)**(-(dps-50))
    with contextlib.redirect_stdout(io.StringIO()) as out:
        relation = mp.pslq(mp.matrix([fake, mp.pi, mp.log(2), 1]),
                           tol=tol, maxcoeff=100, maxsteps=1000, verbose=True)
    (logs / f'control-{dps}.log').write_text(out.getvalue())
    assert relation is not None
    assert relation[0] != 0
    assert abs(mp.fdot(relation, [fake, mp.pi, mp.log(2), 1])) < tol
    expected = [11, -7, 3, -5]
    assert relation == expected or relation == [-x for x in expected], relation
    perturbed = fake + mp.mpf(10)**-40
    assert abs(mp.fdot(relation, [perturbed, mp.pi, mp.log(2), 1])) > tol
    return {'recovered_relation': relation, 'perturbed_control_rejected': True}


def run(args):
    logs = Path(args.logs)
    logs.mkdir(parents=True, exist_ok=True)
    report = {'description': 'Numerical candidate search, not certified identity exclusion',
              'mpmath_version': '1.3.0', 'maxsteps': args.maxsteps, 'levels': []}
    start = time.perf_counter()
    previous = None
    for dps in args.precisions:
        mp.dps = dps + 40
        n = dps + 80
        rec, dyadic, er, ed, lo, hi = rho_intervals(n)
        if previous:
            assert max(previous[0], lo) <= min(previous[1], hi)
        previous = (lo, hi)
        assert abs(as_mp(rec) - as_mp(dyadic)) < mp.mpf(10)**(-(dps+20))
        rho = as_mp(rec)
        low, high = outward_decimals(lo, hi, dps)
        level = {'decimal_precision': dps, 'working_precision': mp.dps,
                 'recurrence_terms': n, 'prime_cutoff': 8*n,
                 'rho_interval_lower': low, 'rho_interval_upper': high,
                 'recurrence_tail_bound': mp.nstr(as_mp(er), 12),
                 'prime_regrouping_tail_bound': mp.nstr(as_mp(ed), 12),
                 'control': controlled_pslq(dps, logs), 'searches': []}
        values = constants(rho)
        tol = mp.mpf(10)**(-(dps-50))
        for name, labels, height in basis_specs():
            t = time.perf_counter()
            with contextlib.redirect_stdout(io.StringIO()) as out:
                relation = mp.pslq(mp.matrix([values[v] for v in labels]),
                                   tol=tol, maxcoeff=height, maxsteps=args.maxsteps, verbose=True)
            verbose = out.getvalue()
            (logs / f'{name}-{dps}.log').write_text(verbose)
            item = {'family': name, 'basis': labels, 'maxcoeff': height,
                    'tolerance': str(tol), 'relation': relation,
                    'seconds': round(time.perf_counter()-t, 3),
                    'termination_message': verbose.splitlines()[-6:]}
            if relation is not None:
                item['residual'] = mp.nstr(abs(mp.fdot(relation, [values[v] for v in labels])), 20)
                item['rho_coefficient_present'] = any(c and label.startswith('rho')
                    for c, label in zip(relation, labels))
            level['searches'].append(item)
            print(f'{dps} dps {name}: {relation}; {item["seconds"]}s', flush=True)
        report['levels'].append(level)
        report['elapsed_seconds'] = round(time.perf_counter()-start, 3)
        Path(args.output).write_text(json.dumps(report, indent=2) + '\n')
        print(f'completed {dps} digits; rho={mp.nstr(rho, 55)}', flush=True)
    print(f'completed all searches in {report["elapsed_seconds"]} seconds', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--precisions', type=int, nargs='+', default=[200, 400, 800])
    parser.add_argument('--maxsteps', type=int, default=5000)
    parser.add_argument('--logs', default='tmp/20261026-rho-identity')
    parser.add_argument('--output', default='docs/pi-routes/rho-identity-probe.json')
    run(parser.parse_args())
