#!/usr/bin/env python3
"""Gate 5 lap 3: dump the exact gate-4 core per level (reused by the totals probes).

For every level k <= KTOP: the Acc2 cells (binary SFT alive), whether each is Good449, and its
integer certificate weight W[bin] (coreWeight = W/maxW exactly for Good cells, k >= 5).
Saved as tail5_out/core/core_k{k}.pkl = (acc: array('Q'), good: bytes, wint: array('q')).
usage: tail5_dump.py KTOP
"""
import sys, pickle
from array import array
sys.argv, ARGS = ['x', 'none'], sys.argv[1:]
sys.path.insert(0, '.')
import tail5_measure as T
from pathlib import Path

OUT = Path(__file__).parent / 'tail5_out' / 'core'
OUT.mkdir(parents=True, exist_ok=True)

def wint(k, a):
    s = T.sft(k, a); p = T.pend(k)
    ib = (T.N * ((3 ** p * a) % 2 ** k)) >> k
    jb = sum(1 for e in T.EDGES if e * 2 ** k < 3 ** p * 2 ** 90)
    return T.W[s * T.N * T.M + ib * T.M + jb]

def main():
    ktop = int(ARGS[0])
    lev = [0]
    for k in range(1, ktop + 1):
        lev = [c for a in lev for c in (2 * a, 2 * a + 1) if T.sft(k, c) != 99]
        good = bytearray(len(lev)); w = array('q', bytes(8 * len(lev)))
        if k >= 5:
            for i, a in enumerate(lev):
                if T.good(k, a):
                    good[i] = 1; w[i] = wint(k, a)
        with open(OUT / f'core_k{k}.pkl', 'wb') as f:
            pickle.dump((array('Q', lev), bytes(good), w), f)
        print(f'level {k}: Acc2 {len(lev)} Good {sum(good)} positive {sum(1 for x in w if x > 0)}',
              flush=True)

if __name__ == '__main__':
    main()
