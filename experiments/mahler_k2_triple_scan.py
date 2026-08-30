#!/usr/bin/env python3
"""Probe: is there a 3-element multiplier set {m1,m2,m3} (base 3) whose
certificate family collapses for EVERY length-2 ternary word (diagonal
assignment w,w,w)?  A perfect triple would be a finite Mahler set for
k = 2 in the C1 {1,2} genre.  Negative results recorded in
PENDING_WORK / probe docs, not formalized."""
import itertools, sys
sys.path.insert(0, '.')
from adder_baseg_emit import FamilyG, tarjan_scc

def collapses(g, channels):
    fam = FamilyG(g, channels, True)
    S, A = fam.S, fam.A
    preds = fam.pred_tables()
    edges = []
    for sig in range(A):
        p = preds[sig]
        for sp in range(S):
            if p[sp] >= 0:
                edges.append((p[sp], sp))
    alive = [True] * S
    while True:
        out = [0] * S
        for s, sp in edges:
            if alive[s] and alive[sp]:
                out[s] += 1
        dying = [s for s in range(S) if alive[s] and out[s] == 0]
        if not dying:
            break
        for s in dying:
            alive[s] = False
    led = [(s, sp) for s, sp in edges if alive[s] and alive[sp]]
    adj = {}
    for s, sp in led:
        adj.setdefault(s, []).append(sp)
    n, labels = tarjan_scc(S, adj)
    intra = [0] * S
    for s, sp in led:
        if labels[s] == labels[sp]:
            intra[s] += 1
    members = {}
    for s in range(S):
        if alive[s]:
            members.setdefault(labels[s], []).append(s)
    loops = {s for s, sp in led if s == sp}
    for comp, ms in members.items():
        cyc = len(ms) > 1 or ms[0] in loops
        if cyc and not all(intra[s] == 1 for s in ms):
            return False
    return True

words = [[a, b] for a in range(3) for b in range(3)]
best = (0, None)
for trip in itertools.combinations(range(1, 11), 3):
    got = 0
    for w in words:
        if collapses(3, [(m, 0, w) for m in trip]):
            got += 1
    if got > best[0]:
        best = (got, trip)
        print("new best:", trip, got, "/9", flush=True)
    if got == 9:
        print("PERFECT TRIPLE:", trip, flush=True)
print("done; best:", best, flush=True)
