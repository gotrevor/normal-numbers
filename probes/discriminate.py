#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""
DISCRIMINATING TEST -- does q = phi differ from rational q in the real-place dynamics?

Route A rests on exactly one claim: the conjugate place never feeds back, so
Vandehey's finiteness was a certificate rather than part of the dynamics.  If that
is right, the real-place transducer dynamics at q = phi should be statistically
INDISTINGUISHABLE from a rational q, where the theorem is proved.

The null is not "zero difference": different q differ for trivial reasons (det,
denominator).  So build the null from rational-vs-rational pairs and ask where
phi-vs-rational falls inside it.

Observables, all real-place: distortion distribution, emission rate, excursion tail.
"""
import sys, math, random
sys.path.insert(0, "/Users/gotrevor/src/normal-numbers/probes")
import transducer_window as T

Mat, Transducer, zint = T.Mat, T.Transducer, T.zint
ZERO, ONE, PHI_Z = T.ZERO, T.ONE, T.PHI_Z

CASES = {
    "phi":  Mat(PHI_Z,    ZERO, ZERO, ONE),
    "2":    Mat(zint(2),  ZERO, ZERO, ONE),
    "3":    Mat(zint(3),  ZERO, ZERO, ONE),
    "5/2":  Mat(zint(5),  ZERO, ZERO, zint(2)),
    "7/3":  Mat(zint(7),  ZERO, ZERO, zint(3)),
}
RATIONALS = ["2", "3", "5/2", "7/3"]

def sample(M0, runs, digits, seed):
    random.seed(seed)
    dist, rates = [], []
    for _ in range(runs):
        digs = T.cf_digits_of_random_real(nbits=digits * 8, cap=digits)
        tr = Transducer(M0)
        for d in digs:
            tr.step(d)
            if T.zsign(tr.M.c) != 0: dist.append(T.distortion(tr.M))
        rates.append(len(tr.out) / len(digs))
    return dist, sum(rates) / len(rates)

RUNS, DIGITS = 7, 350
data = {}
for name, M0 in CASES.items():
    d, r = sample(M0, RUNS, DIGITS, 31337)
    s = sorted(d)
    data[name] = (d, r)
    tail = [sum(1 for v in d if v > t) / len(d) for t in (2, 3, 4, 5)]
    print(f"  q = {name:>4}: n={len(d):>5}  median {s[len(s)//2]:.3f}"
          f"  p90 {s[int(.9*len(s))]:.3f}  p99 {s[int(.99*len(s))]:.3f}"
          f"  emit-rate {r:.3f}  tail {['%.4f'%t for t in tail]}")

print("\n  pairwise KS on the pooled distortion distribution:")
null = []
for i, a in enumerate(RATIONALS[:-1]):
    for b in RATIONALS[i+1:]:
        v = T.ks(data[a][0], data[b][0]); null.append((f"{a} vs {b}", v))
        print(f"    rational null   {a:>4} vs {b:<4}  {v:.4f}")
phi_vs = []
for b in RATIONALS:
    v = T.ks(data["phi"][0], data[b][0]); phi_vs.append((f"phi vs {b}", v))
    print(f"    TEST            phi  vs {b:<4}  {v:.4f}")

nv = [v for _, v in null]; pv = [v for _, v in phi_vs]
nmin, nmax = min(nv), max(nv)
print(f"\n  rational-vs-rational null range: [{nmin:.4f}, {nmax:.4f}]  mean {sum(nv)/len(nv):.4f}")
print(f"  phi-vs-rational range:           [{min(pv):.4f}, {max(pv):.4f}]  mean {sum(pv)/len(pv):.4f}")
outside = sum(1 for v in pv if v > nmax)
print(f"  phi comparisons exceeding the null max: {outside}/{len(pv)}")
print("\n  inside the null  => the real-place dynamics do not see the arithmetic,")
print("                      which is precisely Route A's load-bearing claim.")
print("  above the null   => the conjugate place DOES feed back; Route A needs rework.")

emit = {k: v[1] for k, v in data.items()}
er = [emit[k] for k in RATIONALS]
print(f"\n  emission rate: phi {emit['phi']:.3f} vs rational [{min(er):.3f}, {max(er):.3f}]")
