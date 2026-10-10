#!/usr/bin/env python3
"""Exact enumeration of integers with only digits 0/1 in two (or more) bases.
Top-down over the base-B digits (B = first base): a node fixes the top digits, so N lies in
[lo, lo + (B^p - 1)/(B - 1)]; it is kept only if every other base b has a 0/1-digit integer in
that interval (next01(b, lo) <= hi, exact).  solutions(bases, L) lists the solutions with exactly
L base-B digits; counts(bases, Lmax) gives the per-length counts."""
import sys

def next01(b, lo):
    """Least integer >= lo whose base-b digits are all 0/1."""
    if lo <= 0: return 0
    ds = []
    x = lo
    while x: ds.append(x % b); x //= b
    ds.reverse()                       # most significant first
    for i, d in enumerate(ds):
        if d > 1:
            # bump the prefix ds[:i] to the next 0/1 prefix, zero the rest
            pre = 0
            for e in ds[:i]: pre = pre * b + e
            nxt = next01(b, pre + 1)
            return nxt * b ** (len(ds) - i)
    return lo

def solutions(bases, L):
    B = bases[0]; others = bases[1:]
    out = []
    stack = [(1, L - 1)]               # (prefix value, remaining digits p)
    while stack:
        P, p = stack.pop()
        lo = P * B ** p; hi = lo + (B ** p - 1) // (B - 1)
        if any(next01(b, lo) > hi for b in others): continue
        if p == 0:
            out.append(P); continue
        stack.append((P * B, p - 1)); stack.append((P * B + 1, p - 1))
    return sorted(out)

def digits(n, b):
    s = ''
    while n: s = str(n % b) + s; n //= b
    return s or '0'

if __name__ == "__main__":
    bases = [int(x) for x in sys.argv[1].split(',')]
    Lmax = int(sys.argv[2])
    for L in range(1, Lmax + 1):
        sol = solutions(bases, L)
        print(L, len(sol), sol[:4] if len(sol) <= 4 else str(sol[:3]) + '...', flush=True)
