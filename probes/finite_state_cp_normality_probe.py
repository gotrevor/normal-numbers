#!/usr/bin/env python3
"""Tripwire for Literature.cartonPerifel_normal: block discrepancy of w1 w~1 w2 w~2 ...
vs uniform, with a known-normal control (lex concatenation w1 w2 w3 ..., Champernowne-type)
and a known-NON-normal control (w_n followed by 0^{|w_n|}).

For each sequence we report D_l(N) = max_u | count_u(x[:N]) / (N-l+1) - k^-l | for l = 1,2,3
at the end of each block AND at several mid-block points, and the worst value over the
last stage.  Also reports the free-reduction coder's zero frequency at block ends (headline leaf).
"""
import itertools, sys

def lex_block(k, n):
    out = []
    for t in itertools.product(range(k), repeat=n):
        out.extend(t)
    return out

def build(k, nmax, kind):
    seq, marks = [], []  # marks: (label, position)
    for n in range(1, nmax + 1):
        w = lex_block(k, n)
        if kind == "cp":
            parts = [("w", w), ("w~", w[::-1])]
        elif kind == "lex":
            parts = [("w", w)]
        elif kind == "zero":
            parts = [("w", w), ("0", [0] * len(w))]
        for lab, p in parts:
            start = len(seq)
            for frac in (0.25, 0.5, 0.75):
                marks.append((f"n={n} mid-{lab} {frac}", start + int(frac * len(p))))
            seq.extend(p)
            marks.append((f"n={n} end-{lab}", len(seq)))
    return seq, marks

def disc(seq, N, k, l):
    cnt = {}
    for i in range(N - l + 1):
        u = tuple(seq[i:i + l])
        cnt[u] = cnt.get(u, 0) + 1
    tot = N - l + 1
    return max(abs(cnt.get(u, 0) / tot - k ** -l) for u in itertools.product(range(k), repeat=l))

def enc_zero_freq(seq, N):
    st, z = [], 0
    for a in seq[:N]:
        if not st:
            st.append(a); z += (a == 0)
        elif a == st[-1]:
            st.pop(); z += 1
        else:
            z += ((a - st[-1]) % k_glob == 0); st.append(a)
    return z / N

k_glob = None
if __name__ == "__main__":
    for k, nmax in ((2, 13), (3, 8), (5, 6)):
        k_glob = k
        print(f"=== k={k} (n<= {nmax}) ===")
        for kind in ("cp", "lex", "zero"):
            seq, marks = build(k, nmax, kind)
            # last two stages' marks
            tail = [m for m in marks if m[0].startswith(f"n={nmax - 1} ") or m[0].startswith(f"n={nmax} ")]
            early = [m for m in marks if m[0].startswith(f"n={nmax - 3} ")]
            worst_early = max(max(disc(seq, N, k, l) for l in (1, 2, 3)) for _, N in early)
            worst_tail = max(max(disc(seq, N, k, l) for l in (1, 2, 3)) for _, N in tail)
            line = f"{kind:5s} len={len(seq):8d}  worst D_(1..3) at stage n={nmax-3}: {worst_early:.4f}   at stages n={nmax-1},{nmax}: {worst_tail:.4f}"
            if kind == "cp":
                ends = [N for lab, N in marks if "end-w~" in lab]
                line += f"   coder zero-freq at last block end: {enc_zero_freq(seq, ends[-1]):.4f} (1/k={1/k:.4f})"
            print(line)
