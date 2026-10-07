#!/usr/bin/env python3
"""Decide whether C(1, M1, ..., Mk) contains a nonzero 3-adic integer.
Nonzero element => (shift) a unit element, x_0 = 1.  State = tuple of carries.
Element exists  <=>  the graph reachable from the state after digit 1 has a cycle.
Returns (nonzero?, reachable_size) or (None, size) if the cap is hit."""
import sys

def step(state, Ms, b):
    out = []
    for s, M in zip(state, Ms):
        v = s + M*b
        if v % 3 == 2: return None
        out.append(v//3)
    return tuple(out)

def decide(Ms, cap=200000):
    start = step(tuple(0 for _ in Ms), Ms, 1)
    if start is None: return False, 0
    color = {}  # 1 = on stack, 2 = done
    stack = [(start, iter((0,1)))]
    color[start] = 1
    while stack:
        st, it = stack[-1]
        for b in it:
            nx = step(st, Ms, b)
            if nx is None: continue
            c = color.get(nx)
            if c == 1: return True, len(color)
            if c is None:
                color[nx] = 1
                if len(color) > cap: return None, len(color)
                stack.append((nx, iter((0,1))))
                break
        else:
            color[st] = 2; stack.pop()
    return False, len(color)

if __name__ == "__main__":
    N = int(sys.argv[1]); 
    nonzero=[]; unk=[]; maxr=0
    for a in range(1, N+1):
        for c in range(a+1, N+1):
            r, sz = decide((4**a, 4**c))
            maxr = max(maxr, sz)
            if r is None: unk.append((a,c,sz))
            elif r: nonzero.append((a,c,sz))
    print("pairs", N*(N-1)//2, "max reachable", maxr)
    print("nonzero", len(nonzero), nonzero[:80])
    print("unknown", unk)
