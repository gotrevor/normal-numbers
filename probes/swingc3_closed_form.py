#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# ///
"""Numeric check of SwingC3Closed.tailLarge_eq_tsum:

    tailLarge P b n = sum_{p > P prime} b^{n mod p} / (b^p - 1).

LHS is the defining vertical sum  sum_{i>=0} omega_{>P}(n+i+1) / b^{i+1}.

Hand-computed known answer (b=2, P=1, n=0), i.e. plain omega:
  omega(1)=0, omega(2)=1, omega(3)=1, omega(4)=1, omega(5)=1, omega(6)=2, omega(7)=1, omega(8)=1
  vertical head = 0/2 + 1/4 + 1/8 + 1/16 + 1/32 + 2/64 + 1/128 + 1/256
                = (0+32+16+8+4+4+1)... in 256ths: 0*128? -- do it exactly below.
"""
from fractions import Fraction

def _primes_upto(N):
    sieve = [True]*(N+1)
    sieve[0:2] = [False, False]
    for i in range(2, int(N**0.5)+1):
        if sieve[i]:
            for j in range(i*i, N+1, i):
                sieve[j] = False
    return [i for i in range(N+1) if sieve[i]]

_P = _primes_upto(100000)

def primefactors(m):
    out = []
    for p in _P:
        if p*p > m:
            break
        if m % p == 0:
            out.append(p)
            while m % p == 0:
                m //= p
    if m > 1:
        out.append(m)
    return out

def primerange(a, b):
    return [p for p in _P if a <= p < b]


def omega_large(P, m):
    return sum(1 for p in primefactors(m) if p > P)

def vertical(P, b, n, I=400):
    return sum(Fraction(omega_large(P, n+i+1), b**(i+1)) for i in range(I))

def closed(P, b, n, PMAX=400):
    return sum(Fraction(b**(n % p), b**p - 1) for p in primerange(P+1, PMAX))

# hand-computed known answer: b=2, P=1, n=0, head i=0..7
head = (Fraction(0,2) + Fraction(1,4) + Fraction(1,8) + Fraction(1,16)
        + Fraction(1,32) + Fraction(2,64) + Fraction(1,128) + Fraction(1,256))
assert head == Fraction(0*128 + 1*64 + 1*32 + 1*16 + 1*8 + 2*4 + 1*2 + 1*1, 256), head
v_head = sum(Fraction(omega_large(1, 0+i+1), 2**(i+1)) for i in range(8))
assert v_head == head, (v_head, head)
print("known-answer check OK: head(b=2,P=1,n=0) =", head, "=", float(head))

for (b, P) in [(2,1), (3,2), (4,3), (2,5), (5,7)]:
    for n in [0, 1, 6, 30, 101]:
        L = float(vertical(P, b, n))
        R = float(closed(P, b, n))
        ok = abs(L - R) < 1e-9 * max(1.0, abs(L))
        print(f"b={b} P={P} n={n:4d}  vertical={L:.12f}  closed={R:.12f}  {'OK' if ok else 'MISMATCH'}")
        assert ok
print("all closed-form checks passed")
