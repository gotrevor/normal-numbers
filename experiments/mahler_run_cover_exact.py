#!/usr/bin/env -S uv run --quiet python3
"""Exact run-cover decision: is there B >= 1 with no 1^k in binary(m*B) for every m in S?

Reads B least-significant bit first through the joint carry automaton (carry_i < m_i, current
run of ones r_i < k).  B odd is no loss (doubling is a shift).  A state accepts when feeding
zeros flushes every carry without a k-run.  Breadth-first, so the witness is the shortest B.

  mahler_run_cover_exact.py K m1,m2,...        -> witness B or COVER (with states explored)
  mahler_run_cover_exact.py --twoadic K m1,..  -> also report whether an infinite (2-adic) B exists
"""
import sys
from collections import deque


def bits_ok(c, r, k):
    """Flush carry c from run r: True iff no k-run appears."""
    while c:
        if c & 1:
            r += 1
            if r >= k:
                return False
        else:
            r = 0
        c >>= 1
    return True


def step(state, b, ms, k):
    cs, rs = state
    nc, nr = [], []
    for m, c, r in zip(ms, cs, rs):
        t = c + m * b
        if t & 1:
            r += 1
            if r >= k:
                return None
        else:
            r = 0
        nc.append(t >> 1)
        nr.append(r)
    return (tuple(nc), tuple(nr))


def search(k, ms, limit=10**7):
    start = (tuple(0 for _ in ms), tuple(0 for _ in ms))
    first = step(start, 1, ms, k)
    if first is None:
        return "COVER", 0, None
    parent = {first: (None, 1)}
    q = deque([first])
    while q:
        st = q.popleft()
        if all(bits_ok(c, r, k) for c, r in zip(*st)):
            bits, cur = [], st
            while cur is not None:
                p, b = parent[cur]
                bits.append(b)
                cur = p
            return "WITNESS", len(parent), int("".join(map(str, bits)), 2)
        for b in (0, 1):
            nx = step(st, b, ms, k)
            if nx is not None and nx not in parent:
                parent[nx] = (st, b)
                q.append(nx)
        if len(parent) > limit:
            return "LIMIT", len(parent), None
    return "COVER", len(parent), None


def twoadic(k, ms):
    """Is there an infinite valid path (a 2-adic B avoiding 1^k in every m*B)?"""
    start = (tuple(0 for _ in ms), tuple(0 for _ in ms))
    first = step(start, 1, ms, k)
    if first is None:
        return False
    seen, order, stack = {first}, [], [first]
    while stack:
        st = stack.pop()
        order.append(st)
        for b in (0, 1):
            nx = step(st, b, ms, k)
            if nx is not None and nx not in seen:
                seen.add(nx)
                stack.append(nx)
    # prune states with no successors until stable; an infinite path exists iff anything survives
    alive = set(seen)
    changed = True
    while changed:
        changed = False
        for st in list(alive):
            if not any((nx := step(st, b, ms, k)) is not None and nx in alive for b in (0, 1)):
                alive.discard(st)
                changed = True
    return first in alive


if __name__ == "__main__":
    args = sys.argv[1:]
    adic = args and args[0] == "--twoadic"
    if adic:
        args = args[1:]
    k = int(args[0])
    ms = [int(x) for x in args[1].split(",")]
    verdict, n, B = search(k, ms)
    out = f"{verdict} k={k} S={ms} states={n}"
    if B is not None:
        out += f" B={B} products={[bin(m * B)[2:] for m in ms]}"
    if adic:
        out += f" twoadic={'yes' if twoadic(k, ms) else 'no'}"
    print(out)
