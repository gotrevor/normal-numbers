#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""
FEEDBACK adversary for Route A nodes A2 (window) and A3 (merging).

The schedule adversary injected huge partial quotients at n = 2^k, blind to what
the transducer was doing.  This one WATCHES the state and spends its injections
where they hurt most -- the version that could actually break A3 if anything can.

Legality: the stream must stay CF-normal, so injections must occupy a density-zero
set of positions.  Budget here is ceil(sqrt(n)) injections by step n, which is
density zero and far more generous than the 2^k schedule (at n=130 that is ~11
injections rather than ~7, and the adversary chooses WHERE, which is the point).

Attack W: at each allowed step, try each candidate digit and keep the one that
maximises the resulting real-place distortion -- greedily drive the state out of
the compact window and deny it recovery.

Attack M: the adversary sees ALL FOUR initial states evolving on its stream and
keeps the candidate that MAXIMISES the spread of their state coordinates, i.e. it
actively fights the merging it is trying to prevent.  A maximally informed
adversary; strictly stronger than anything the theorem has to survive.
"""
import sys, math, random
sys.path.insert(0, "/Users/gotrevor/src/normal-numbers/probes")
import transducer_window as T

Mat, Transducer = T.Mat, T.Transducer
ZERO, ONE, PHI_Z, zint = T.ZERO, T.ONE, T.PHI_Z, T.zint

CANDS = [10**3, 10**6, 10**18]
STARTS = {
    "phi*x":             Mat(PHI_Z, ZERO,    ZERO, ONE),
    "phi*x + phi":       Mat(PHI_Z, PHI_Z,   ZERO, ONE),
    "phi*x + 3":         Mat(PHI_Z, zint(3), ZERO, ONE),
    "(phi x+1)/(x+phi)": Mat(PHI_Z, ONE,     ONE,  PHI_Z),
}

def _try(tr, d):
    """apply digit d to a COPY of tr's state, return (newM, newoutlen)"""
    saveM, savelen = tr.M, len(tr.out)
    tr.step(d)
    M, ln = tr.M, len(tr.out)
    tr.M, tr.out = saveM, tr.out[:savelen]
    return M, ln

def budget_ok(used, n):
    return used < math.ceil(math.sqrt(n + 1))

# ------------------------------------------------------------------ attack W
def attack_window(runs, steps, seed, greedy=True):
    random.seed(seed)
    meds, worsts, rets, spends = [], [], [], []
    for _ in range(runs):
        base = T.cf_digits_of_random_real(nbits=steps * 10, cap=steps)
        tr = Transducer(Mat(PHI_Z, ZERO, ZERO, ONE))
        trace, used = [], 0
        for n, a in enumerate(base):
            d = a
            if greedy and budget_ok(used, n):
                best, bd = None, -1e9
                for c in CANDS:
                    M, _ = _try(tr, c)
                    if T.zsign(M.c) == 0: continue
                    v = T.distortion(M)
                    if v > bd: bd, best = v, c
                Mn, _ = _try(tr, a)
                nat = T.distortion(Mn) if T.zsign(Mn.c) != 0 else -1e9
                if best is not None and bd > nat:
                    d, used = best, used + 1
            tr.step(d)
            if T.zsign(tr.M.c) != 0: trace.append(T.distortion(tr.M))
        if not trace: continue
        s = sorted(trace)
        meds.append(s[len(s)//2]); worsts.append(s[-1]); spends.append(used)
        i = max(range(len(trace)), key=lambda j: trace[j]); j = i
        while j < len(trace) and trace[j] > 2.0: j += 1
        rets.append(j - i)
    f = lambda v: sum(v)/len(v)
    return f(meds), max(worsts), f(rets), f(spends)

# ------------------------------------------------------------------ attack M
def attack_merging(samples, steps, seed, greedy=True):
    random.seed(seed)
    coords = {k: [] for k in STARTS}
    spend = []
    for _ in range(samples):
        base = T.cf_digits_of_random_real(nbits=steps * 12, cap=steps)
        trs = {k: Transducer(M0) for k, M0 in STARTS.items()}
        used = 0
        for n, a in enumerate(base):
            d = a
            if greedy and budget_ok(used, n):
                def spread(dig):
                    vals = []
                    for tr in trs.values():
                        M, _ = _try(tr, dig)
                        c = T.state_coord(M)
                        if c is None: return -1e9
                        vals.append(c[0])
                    return max(vals) - min(vals)
                nat = spread(a)
                best, bs = None, nat
                for c in CANDS:
                    v = spread(c)
                    if v > bs: bs, best = v, c
                if best is not None:
                    d, used = best, used + 1
            for tr in trs.values(): tr.step(d)
        spend.append(used)
        for k, tr in trs.items():
            c = T.state_coord(tr.M)
            if c: coords[k].append(c[0])
    names = list(STARTS); worst, pair = 0.0, None
    for i, a in enumerate(names[:-1]):
        for b in names[i+1:]:
            v = T.ks(coords[a], coords[b])
            if v > worst: worst, pair = v, (a, b)
    return worst, pair, sum(spend)/len(spend)


if __name__ == "__main__":
    print("=" * 84)
    print("FEEDBACK ADVERSARY -- state-aware, density-zero budget ceil(sqrt(n))")
    print("=" * 84)

    print("\n(W) WINDOW under a greedy distortion-maximising adversary   5 runs x 250 steps")
    print(f"{'mode':>10} | {'median':>8} {'worst':>8} {'recover':>8} {'injections used':>16}")
    for mode, g in (("passive", False), ("greedy", True)):
        m, w, r, s = attack_window(5, 250, 777, greedy=g)
        print(f"{mode:>10} | {m:>8.3f} {w:>8.3f} {r:>8.1f} {s:>16.1f}")

    print("\n(M) MERGING under an adversary that maximises state spread")
    print("    (sees all four starts; strictly stronger than the theorem must survive)")
    print(f"{'mode':>10} | {'seed':>5} {'worst KS':>9} {'injections':>11}  worst pair")
    res = {"passive": [], "greedy": []}
    for sd in (11, 22, 33):
        for mode, g in (("passive", False), ("greedy", True)):
            w, pair, s = attack_merging(90, 110, sd, greedy=g)
            res[mode].append(w)
            print(f"{mode:>10} | {sd:>5} {w:>9.4f} {s:>11.1f}  {pair[0]} vs {pair[1]}")
    pm = sum(res["passive"])/len(res["passive"]); gm = sum(res["greedy"])/len(res["greedy"])
    print(f"\n  passive mean {pm:.4f}   greedy mean {gm:.4f}   delta {gm-pm:+.4f}")
    print("  (a real break needs greedy well ABOVE the passive null, not inside its spread)")
