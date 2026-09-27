#!/usr/bin/env python3
"""
Is the INTEGER CF transducer synchronizing?  (decidable; this probe decides it)

NormalNumbers/VandeheyAutomaton.lean routes around Vandehey's broken Lemma 3.3 by
demanding a genuine CF word `z` that is SYNCHRONIZING for the det-+-D transducer:
reading `z` from any reachable state lands in one state, so merging is pathwise.

Transducer (our normalization, not Vandehey's Type I-VI forms):
  state M=[[p,q],[r,s]], |det M|=D, as the Moebius map t |-> (pt+q)/(rt+s) on (0,1).
  ingest a>=1 :  M <- M . B_a,        B_a      = [[0,1],[1,a]]   (t = 1/(a+t'))
  emit   d>=1 :  M <- B_d^{-1} . M,   B_d^{-1} = [[-d,1],[1,0]]
                 allowed when M((0,1)) is inside the cylinder (1/(d+1), 1/d)
  emit int n>=1: M <- M - n*[[r,s],[0,0]]   allowed when M((0,1)) inside (n,n+1)
  reduced       = nothing emittable (image inside (0,1), straddling some 1/d).
  delta(M,a)    = reduce(M . B_a).

A DFA is synchronizing iff every PAIR of states can be merged, so the probe reports
the pair-merge relation and the SCCs/classes it leaves behind.
"""
import sys
from fractions import Fraction as F
from math import gcd
from collections import deque

def norm(M):
    p,q,r,s = M
    g = gcd(gcd(abs(p),abs(q)), gcd(abs(r),abs(s)))
    if g > 1: p,q,r,s = p//g, q//g, r//g, s//g
    for v in (s,r,q,p):
        if v != 0:
            if v < 0: p,q,r,s = -p,-q,-r,-s
            break
    return (p,q,r,s)

def det(M): p,q,r,s = M; return p*s-q*r

def image(M):
    p,q,r,s = M
    if r != 0:
        t0 = F(-s, r)
        if 0 <= t0 <= 1: return None
    if s == 0 or (r+s) == 0: return None
    a, b = F(q,s), F(p+q, r+s)
    return (min(a,b), max(a,b))

def step_emit(M):
    """one emission if available: returns new state or None"""
    im = image(M)
    if im is None: return None
    lo, hi = im
    p,q,r,s = M
    if hi < 1:
        if lo <= 0: return None
        d = int(1//hi)
        if d >= 1 and lo > F(1,d+1) and hi < F(1,d):
            return norm((-d*p + r, -d*q + s, p, q))
        return None
    # integer part
    n = int(lo) if lo >= 0 else None
    if n is None or n < 1: return None
    if hi < n+1 and lo >= n:
        return norm((p - n*r, q - n*s, r, s))
    return None

def reduce_state(M, cap=200):
    for _ in range(cap):
        N = step_emit(M)
        if N is None: return norm(M)
        M = N
    raise RuntimeError("emission did not terminate: %s" % (M,))

def ingest(M, a):
    p,q,r,s = M
    return norm((q, p + a*q, s, r + a*s))

def delta(M, a): return reduce_state(ingest(M, a))

def explore(M0, digits, cap=30000):
    seen = {reduce_state(M0)}
    fr = deque(seen)
    while fr:
        M = fr.popleft()
        for a in digits:
            N = delta(M, a)
            if N not in seen:
                seen.add(N); fr.append(N)
                if len(seen) > cap: raise RuntimeError("blew up past %d" % cap)
    return sorted(seen)

def pair_merge(states, digits):
    """backward BFS: which pairs can be merged?  returns (mergeable set, dist)"""
    idx = {M:i for i,M in enumerate(states)}
    # forward transitions
    tr = {M: [delta(M,a) for a in digits] for M in states}
    mergeable = {(M,M) for M in states}
    fr = deque(mergeable)
    # predecessors of pairs
    preds = {}
    for M in states:
        for k,a in enumerate(digits):
            for N in states:
                pass
    # cheaper: iterate to fixpoint
    changed = True
    while changed:
        changed = False
        for i,M in enumerate(states):
            for N in states[i+1:]:
                if (M,N) in mergeable: continue
                for k in range(len(digits)):
                    A, B = tr[M][k], tr[N][k]
                    key = (A,B) if (A,B) in mergeable else (B,A)
                    if key in mergeable or A == B:
                        mergeable.add((M,N)); changed = True; break
    return mergeable

def sync_word(states, digits, maxlen=25):
    cur = {tuple(states): ()}
    for L in range(1, maxlen+1):
        nxt = {}
        for img, w in cur.items():
            for a in digits:
                nimg = tuple(sorted(set(delta(M,a) for M in img)))
                if len(nimg) == 1: return w + (a,), nimg[0]
                if nimg not in nxt: nxt[nimg] = w + (a,)
        best = min(len(i) for i in nxt)
        print("  len %d: %d images, min size %d" % (L, len(nxt), best), file=sys.stderr)
        cur = nxt
        if len(cur) > 60000: 
            print("  frontier too big", file=sys.stderr); return None, None
    return None, None

def run(name, M0, K, maxlen=20):
    digits = list(range(1, K+1))
    print("\n=== %s  M0=%s  det=%d  digits 1..%d" % (name, M0, det(M0), K))
    try:
        states = explore(M0, digits)
    except RuntimeError as e:
        print("  EXPLORE FAILED:", e); return
    print("  reachable reduced states: %d" % len(states))
    print("  dets:", sorted(set(det(M) for M in states)))
    w, tgt = sync_word(states, digits, maxlen)
    if w:
        print("  SYNCHRONIZING WORD: %s  ->  %s" % (list(w), (tgt,)))
        return
    print("  NO synchronizing word up to length %d" % maxlen)
    mg = pair_merge(states, digits)
    bad = [(M,N) for i,M in enumerate(states) for N in states[i+1:] if (M,N) not in mg]
    print("  unmergeable pairs: %d of %d" % (len(bad), len(states)*(len(states)-1)//2))
    for M,N in bad[:6]:
        print("    %s  det%d  vs  %s  det%d" % (M, det(M), N, det(N)))

if __name__ == "__main__":
    run("x -> 2x", (2,0,0,1), 8)
    run("x -> x/2", (1,0,0,2), 8)
    run("x -> 3x", (3,0,0,1), 8)
    run("x -> (x+1)/2", (1,1,0,2), 8)
