#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""CONTROL: run the identical adversary against the RATIONAL case q = 2, 3, 5/2,
where Vandehey's theorem is PROVED and the state entries are provably bounded by D.

If the rational case shows the same 2*log10(digit) scaling, then this distortion
functional is not measuring Vandehey's "entries <= D" and the A2-is-false reading
is an artifact of the instrument, not a fact about Z[phi]."""
import sys, math, random
sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent))
sys.path.insert(0, "/Users/gotrevor/src/normal-numbers/probes")
import transducer_window as T
import feedback_adv as F

CASES = {
    "q = phi (Z[phi])": T.Mat(T.PHI_Z, T.ZERO, T.ZERO, T.ONE),
    "q = 2 (rational)": T.Mat(T.zint(2), T.ZERO, T.ZERO, T.ONE),
    "q = 3 (rational)": T.Mat(T.zint(3), T.ZERO, T.ZERO, T.ONE),
    "q = 5/2 (ratl)":   T.Mat(T.zint(5), T.ZERO, T.ZERO, T.zint(2)),
}

print("=" * 80)
print("CONTROL -- same adversary, rational q (Vandehey PROVED, entries bounded by D)")
print("=" * 80)
print(f"{'case':>18} {'digit':>7} | {'median':>8} {'worst':>8} {'2*log10':>8} {'max|entry|':>11}")
for name, M0 in CASES.items():
    for e in (6, 18, 36):
        random.seed(1357)
        worst, meds, ment = 0.0, [], 0.0
        for _ in range(3):
            base = T.cf_digits_of_random_real(nbits=1600, cap=160)
            tr = T.Transducer(M0)
            trace, used = [], 0
            for n, a in enumerate(base):
                d = a
                if F.budget_ok(used, n):
                    M, _ = F._try(tr, 10 ** e); Mn, _ = F._try(tr, a)
                    if T.zsign(M.c) != 0 and T.zsign(Mn.c) != 0 \
                       and T.distortion(M) > T.distortion(Mn):
                        d, used = 10 ** e, used + 1
                tr.step(d)
                if T.zsign(tr.M.c) != 0:
                    trace.append(T.distortion(tr.M))
                    ment = max(ment, max(T.log10_abs(x) for x in tr.M.entries()))
            if trace:
                s = sorted(trace); meds.append(s[len(s)//2]); worst = max(worst, s[-1])
        print(f"{name:>18} {'10^'+str(e):>7} | {sum(meds)/len(meds):>8.3f} {worst:>8.2f}"
              f" {2*e:>8} {ment:>11.2f}")
    print()
