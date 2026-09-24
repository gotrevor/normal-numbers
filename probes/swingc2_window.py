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
