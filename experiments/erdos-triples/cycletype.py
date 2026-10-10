#!/usr/bin/env python3
"""Classify the nonzero points of C(1, M1, ..., Mk) (3-adic, digits 0/1) by cycle type.
The carry automaton is finite, so a nonzero point exists iff a reachable cycle exists, and
every cycle is either the zero state's digit-0 self-loop (x a positive integer, all of x, M x
0/1-digit integers: 'integer type') or a cycle using a digit-1 edge (a purely periodic tail:
'cyclic type', a x3-periodic point of the circle Cantor set K with M theta in K).
classify(Ms) -> (integer?, cyclic?, reachable size)."""
import sys
from triple import step

def graph(Ms, cap=500000):
    start = step(tuple(0 for _ in Ms), Ms, 1)
    if start is None: return None, {}
    adj = {}; todo = [start]; adj[start] = []
    while todo:
        s = todo.pop()
        for b in (0, 1):
            t = step(s, Ms, b)
            if t is None: continue
            adj[s].append((t, b))
            if t not in adj:
                adj[t] = []; todo.append(t)
                if len(adj) > cap: raise RuntimeError("cap")
    return start, adj

def sccs(adj):
    idx = {}; low = {}; on = set(); st = []; out = []; n = [0]
    for root in adj:
        if root in idx: continue
        work = [(root, iter(adj[root]))]; idx[root] = low[root] = n[0]; n[0] += 1; st.append(root); on.add(root)
        while work:
            v, it = work[-1]
            for (w, _) in it:
                if w not in idx:
                    idx[w] = low[w] = n[0]; n[0] += 1; st.append(w); on.add(w)
                    work.append((w, iter(adj[w]))); break
                elif w in on: low[v] = min(low[v], idx[w])
            else:
                work.pop()
                if work: low[work[-1][0]] = min(low[work[-1][0]], low[v])
                if low[v] == idx[v]:
                    comp = set()
                    while True:
                        w = st.pop(); on.discard(w); comp.add(w)
                        if w == v: break
                    out.append(comp)
    return out

def classify(Ms):
    start, adj = graph(Ms)
    if start is None: return False, False, 0
    zero = tuple(0 for _ in Ms)
    integer = zero in adj
    cyclic = False
    for comp in sccs(adj):
        for v in comp:
            if any(w in comp and b == 1 for (w, b) in adj[v]):
                cyclic = True
    return integer, cyclic, len(adj)

if __name__ == "__main__":
    N = int(sys.argv[1])
    for a in range(1, N + 1):
        for c in range(a + 1, N + 1):
            i, cy, sz = classify((4**a, 4**c))
            if i or cy: print(a, c - a, "integer" if i else "", "CYCLIC" if cy else "", sz)
