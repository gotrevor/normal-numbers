"""Exact single-track adder machine (right-to-left deterministic carries).
State = (window of last k-1 input digits (to the right), carry tuple c[m] for m in S).
Transition on new digit x (prepended to the left): c'[m] = (m*x + c[m]) // g, emitted digit (m*x+c[m]) % g.
Window check: the k digits emitted by channel m over the k-window (x, window) are determined by c[m] at the right end.
Edge allowed iff no channel emits W over the window.
Collapse iff every SCC of the allowed graph is a simple cycle or trivial.
"""
import sys
from itertools import product
sys.setrecursionlimit(10000)

def channel_digits(m, xs, c, g):
    # xs: list of k digits left-to-right; c: carry at right end. returns emitted digits left-to-right
    out = []
    for x in reversed(xs):
        v = m*x + c
        out.append(v % g); c = v // g
    return out[::-1], c

def collapse(g, k, S, W):
    W = tuple(W)
    # enumerate states
    windows = list(product(range(g), repeat=k-1))
    carries = list(product(*[range(m) for m in S]))
    idx = {}
    states = []
    for w in windows:
        for c in carries:
            idx[(w,c)] = len(states); states.append((w,c))
    n = len(states)
    adj = [[] for _ in range(n)]
    for i,(w,c) in enumerate(states):
        for x in range(g):
            xs = (x,)+w
            ok = True; newc = []
            for j,m in enumerate(S):
                d, _ = channel_digits(m, list(xs), c[j], g)
                if tuple(d) == W: ok = False; break
                newc.append((m*xs[-1] + c[j]) // g)
            if ok:
                nw = xs[:k-1] if k > 1 else ()
                adj[i].append(idx[(nw, tuple(newc))])
    # Tarjan SCC iterative
    index = [None]*n; low = [0]*n; onst = [False]*n; st = []; counter = 0
    sccs = []
    for root in range(n):
        if index[root] is not None: continue
        stack = [(root, iter(adj[root]))]
        index[root] = low[root] = counter; counter += 1; st.append(root); onst[root] = True
        while stack:
            v, it = stack[-1]
            advanced = False
            for w in it:
                if index[w] is None:
                    index[w] = low[w] = counter; counter += 1; st.append(w); onst[w] = True
                    stack.append((w, iter(adj[w]))); advanced = True; break
                elif onst[w]:
                    low[v] = min(low[v], index[w])
            if advanced: continue
            stack.pop()
            if stack:
                u = stack[-1][0]; low[u] = min(low[u], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = st.pop(); onst[w] = False; comp.append(w)
                    if w == v: break
                sccs.append(comp)
    # entropy check
    bad = []
    for comp in sccs:
        cs = set(comp)
        e = sum(1 for v in comp for w in adj[v] if w in cs)
        if e > len(comp):
            bad.append((len(comp), e))
    return bad, n

if __name__ == "__main__":
    for (g,k) in [(2,1),(2,2),(2,3),(3,1),(3,2),(5,1),(7,1)]:
        S = list(range(1, g**k))
        res = {}
        for W in product(range(g), repeat=k):
            bad, n = collapse(g, k, S, W)
            res[W] = (len(bad)==0, bad[:3])
        allc = all(v[0] for v in res.values())
        print(f"g={g} k={k} S=1..{g**k-1}: collapse for all W? {allc}", flush=True)
        for W,v in res.items():
            if not v[0]: print("   escape W=",W, "nontrivial SCCs (|V|,|E|):", v[1])
        # also check S = 1..g^k-2 escapes for W=(g-1)^k
        S2 = list(range(1, g**k-1))
        if S2:
            bad, n = collapse(g, k, S2, (g-1,)*k)
            print(f"   S=1..{g**k-2}, W=(g-1)^k: escape? {len(bad)>0}")
