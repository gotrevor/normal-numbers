#!/usr/bin/env python3
"""Gate 5: climb lengths.  For every Good block cell (level 6m <= 6*MMAX) with a Good positive-weight
block child, the number of blocks up to its nearest positive-weight block ancestor (the cell itself
counts as 0 if positive).  Exact on the finite tree (all sft-alive cells), no tail.  usage: MMAX"""
import sys
from collections import Counter
from tail5_measure import weight, good, sft
MMAX = int(sys.argv[1]); hist = Counter()
def dfs(k, a, lastpos):  # lastpos = block index of nearest positive-weight block ancestor (incl. self)
    if k % 6 == 0:
        m = k // 6
        if weight(k, a) > 0: lastpos = m
        if m == MMAX: return
        if good(k, a) and any(good(k + 6, 64 * a + j) and weight(k + 6, 64 * a + j) > 0 for j in range(64)):
            hist[m - lastpos] += 1
    for c in (2 * a, 2 * a + 1):
        if sft(k + 1, c) != 99: dfs(k + 1, c, lastpos)
dfs(0, 0, 0)
print("climb histogram (blocks -> parents):", sorted(hist.items()))
