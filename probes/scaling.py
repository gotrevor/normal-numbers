#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""Is the adversarial excursion BOUNDED (compact window) or does it scale with the
injected digit (no compact window, only recurrence)?  Decisive test: give the greedy
adversary progressively larger candidate digits and watch the worst distortion."""
import sys, math, random
sys.path.insert(0, str(__import__("pathlib").Path(__file__).parent))
sys.path.insert(0, "/Users/gotrevor/src/normal-numbers/probes")
import transducer_window as T
import feedback_adv as F

print("=" * 78)
print("Does the excursion scale with the adversary's digit?  (A2 as stated vs recurrence)")
print("=" * 78)
print(f"{'max digit':>12} {'log10':>7} | {'median':>8} {'worst dist':>11} {'2*log10':>9}"
      f" {'recover':>8} {'p99':>7}")
for e in (3, 6, 12, 18, 30, 48):
    F.CANDS = [10 ** e]
    random.seed(2468)
    meds, worst, rec, allv = [], 0.0, [], []
    for _ in range(4):
        base = T.cf_digits_of_random_real(nbits=2000, cap=200)
        tr = T.Transducer(T.Mat(T.PHI_Z, T.ZERO, T.ZERO, T.ONE))
        trace, used = [], 0
        for n, a in enumerate(base):
            d = a
            if F.budget_ok(used, n):
                M, _ = F._try(tr, 10 ** e)
                Mn, _ = F._try(tr, a)
                if T.zsign(M.c) != 0 and T.zsign(Mn.c) != 0 \
                   and T.distortion(M) > T.distortion(Mn):
                    d, used = 10 ** e, used + 1
            tr.step(d)
            if T.zsign(tr.M.c) != 0: trace.append(T.distortion(tr.M))
        if not trace: continue
        s = sorted(trace); meds.append(s[len(s)//2]); allv += trace
        worst = max(worst, s[-1])
        i = max(range(len(trace)), key=lambda j: trace[j]); j = i
        while j < len(trace) and trace[j] > 2.0: j += 1
        rec.append(j - i)
    a = sorted(allv)
    print(f"{'10^'+str(e):>12} {e:>7} | {sum(meds)/len(meds):>8.3f} {worst:>11.2f}"
          f" {2*e:>9} {sum(rec)/len(rec):>8.1f} {a[int(0.99*len(a))]:>7.2f}")
print("\n  worst tracking 2*log10(digit) => the excursion is UNBOUNDED over admissible")
print("  input: no fixed compact W contains every post-emission state.")
print("  median + p99 + recovery staying flat => the state RECURS to a compact window,")
print("  which is the statement A2 should actually make.")
