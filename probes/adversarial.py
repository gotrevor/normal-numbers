#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""
Adversarial probe for Route A node A3 (uniform merging on the compact window W).

The green probe measured merging along GAUSS-TYPICAL input.  Route A needs it
along ARBITRARY CF-normal input, and the gap is precise: CF-normality pins the
frequencies of every FIXED finite word, so it says nothing about digits that
occur with density zero.  A CF-normal x may therefore carry a sparse sequence of
ENORMOUS partial quotients, and those are exactly the unbounded-rank excursion
events the attack map worried about.

So: inject huge partial quotients at density-zero positions into an otherwise
Gauss-typical stream and re-run both measurements.  Density-zero injection does
not disturb any fixed word's limiting frequency, so the perturbed stream stays
CF-normal; if the window or the merging dies here, Route A's A3 is in trouble
along admissible input, which no amount of a.e. sampling would have revealed.

Injection schedules (all density zero):
  squares   n = k^2        digit = BIG           (mild, frequent-ish)
  powers    n = 2^k        digit = BIG^k         (growing, very sparse)
  brutal    n = 2^k        digit = 10^(3k)       (super-exponential growth)
"""
import sys, math, random
sys.path.insert(0, "/Users/gotrevor/src/normal-numbers/probes")
import transducer_window as T

Z, Mat, Transducer = T.Z, T.Mat, T.Transducer
ZERO, ONE, PHI_Z, zint = T.ZERO, T.ONE, T.PHI_Z, T.zint


def inject(digs, schedule, big=10**6):
    """replace digits at density-zero positions with huge ones"""
    out = list(digs)
    n = len(out)
    if schedule == "none":
        return out
    if schedule == "squares":
        k = 1
        while k * k < n:
            out[k * k] = big
            k += 1
    elif schedule == "powers":
        k, pos = 1, 2
        while pos < n:
            out[pos] = big ** min(k, 3)
            pos *= 2; k += 1
    elif schedule == "brutal":
        k, pos = 1, 2
        while pos < n:
            out[pos] = 10 ** (3 * k)
            pos *= 2; k += 1
    return out


def window_stats(schedule, runs, digits, seed, big=10**6):
    random.seed(seed)
    meds, maxes, halves, rets = [], [], [], []
    for _ in range(runs):
        base = T.cf_digits_of_random_real(nbits=digits * 8, cap=digits)
        digs = inject(base, schedule, big)
        tr = []
        Tr = Transducer(Mat(PHI_Z, ZERO, ZERO, ONE))
        for d in digs:
            Tr.step(d)
            if T.zsign(Tr.M.c) != 0: tr.append(T.distortion(Tr.M))
        if not tr: continue
        h = len(tr) // 2
        s = sorted(tr)
        meds.append(s[len(s) // 2]); maxes.append(s[-1])
        halves.append((sorted(tr[:h])[h // 2] if h else float("nan"),
                       sorted(tr[h:])[(len(tr) - h) // 2]))
        # recovery: after the worst excursion, how many steps back under 2?
        i = max(range(len(tr)), key=lambda j: tr[j])
        j = i
        while j < len(tr) and tr[j] > 2.0: j += 1
        rets.append(j - i)
    return meds, maxes, halves, rets


def doeblin(schedule, samples, steps, seed, big=10**6):
    random.seed(seed)
    starts = {
        "phi*x":              Mat(PHI_Z, ZERO,    ZERO, ONE),
        "phi*x + phi":        Mat(PHI_Z, PHI_Z,   ZERO, ONE),
        "phi*x + 3":          Mat(PHI_Z, zint(3), ZERO, ONE),
        "(phi x+1)/(x+phi)":  Mat(PHI_Z, ONE,     ONE,  PHI_Z),
    }
    coords = {}
    for name, M0 in starts.items():
        us = []
        for _ in range(samples):
            base = T.cf_digits_of_random_real(nbits=steps * 12, cap=steps)
            digs = inject(base, schedule, big)
            Tr = Transducer(M0)
            for d in digs[:steps]: Tr.step(d)
            c = T.state_coord(Tr.M)
            if c: us.append(c[0])
        coords[name] = us
    names = list(starts)
    worst, pair = 0.0, None
    for i, a in enumerate(names[:-1]):
        for b in names[i + 1:]:
            d = T.ks(coords[a], coords[b])
            if d > worst: worst, pair = d, (a, b)
    n = min(len(v) for v in coords.values())
    return worst, 1.36 * math.sqrt(2 / n), pair, n


if __name__ == "__main__":
    print("=" * 86)
    print("ADVERSARIAL PROBE -- density-zero injections of enormous partial quotients")
    print("=" * 86)
    print("\n(W) WINDOW under injection   6 runs x 400 digits")
    print(f"{'schedule':>10} | {'median':>8} {'1st-half':>9} {'2nd-half':>9} {'worst':>8}"
          f" {'steps to recover':>17}")
    for sch in ("none", "squares", "powers", "brutal"):
        meds, maxes, halves, rets = window_stats(sch, 6, 400, 4242)
        if not meds: print(f"{sch:>10} |  (no data)"); continue
        f_ = sum(h[0] for h in halves) / len(halves)
        s_ = sum(h[1] for h in halves) / len(halves)
        print(f"{sch:>10} | {sum(meds)/len(meds):>8.3f} {f_:>9.3f} {s_:>9.3f}"
              f" {max(maxes):>8.3f} {sum(rets)/len(rets):>17.1f}")

    print("\n(M) DOEBLIN under injection   150 streams x 150 steps, 4 starts")
    print(f"{'schedule':>10} | {'worst KS':>9} {'critical':>9} {'verdict':>20} {'worst pair'}")
    for sch in ("none", "squares", "powers", "brutal"):
        w, c, pair, n = doeblin(sch, 150, 150, 4242)
        v = "INDISTINGUISHABLE" if w < c else "DISTINGUISHABLE"
        print(f"{sch:>10} | {w:>9.4f} {c:>9.4f} {v:>20} {pair[0]} vs {pair[1]}")
