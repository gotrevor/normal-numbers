#!/usr/bin/env -S uv run --quiet python3
"""Sparse-pair blocking certificate for the transversal ceiling.

Claim under test: for x = sum_{k>=1} 2^(-2^k) (irrational: gap sequence grows),
every positive-integer multiple m*x has a binary tail consisting of isolated
copies of bin(m) separated by long 0-runs.  Hence the set of words occurring
infinitely often in m*x is exactly the factor set of 0^* bin(m) 0^*, and in
particular the word 1^(len(bin(m))+1) NEVER occurs: m*x is not disjunctive,
for every m simultaneously.

Consequence (checked here only at the digit level): the pair (X, Y) = (x, x)
is admissible for the universal adder theorems (not both rational) yet has NO
disjunctive channel anywhere in the lattice a*X + b*Y = m*x.  So no family of
universal clauses can entail "some channel is disjunctive".

Known-answer control: the same pipeline on a seeded-random real must SEE the
forbidden word 1^(l+1) and must ESCAPE the factor language - proving the
instrument can detect both failures.  (A negative needs a control.)
"""

import random
import sys

K = 15                     # x truncated to sum_{k=1}^{K} 2^(-2^k)
E = 1 << K                 # working denominator 2^E
TRANSIENT = 128            # skip positions where small-k blocks may interact
WINDOW_END = 1 << 13       # analyze digits [TRANSIENT, WINDOW_END)
MS = [1, 3, 5, 6, 7, 100, 1000]

def frac_bits(num: int, denom_exp: int) -> str:
    """Binary digits of frac(num / 2^denom_exp), most significant first."""
    return format(num % (1 << denom_exp), f"0{denom_exp}b")

def factors(s: str, L: int) -> set:
    return {s[i:i + L] for i in range(len(s) - L + 1)}

def allowed_language(m: int, L: int) -> set:
    """Length-L factors of 0^L bin(m) 0^L."""
    return factors("0" * L + format(m, "b") + "0" * L, L)

def analyze(bits: str, m: int, L: int):
    window = bits[TRANSIENT:WINDOW_END]
    obs = factors(window, L)
    allowed = allowed_language(m, L)
    ones = "1" * L
    return obs, allowed, ones in obs

def main() -> int:
    x_num = sum(1 << (E - (1 << k)) for k in range(1, K + 1))

    failures = []
    for m in MS:
        ell = len(format(m, "b"))
        bits = frac_bits(m * x_num, E)
        for L in (ell + 1, 12):
            obs, allowed, has_ones = analyze(bits, m, L)
            if not obs <= allowed:
                failures.append(f"m={m} L={L}: factors escape 0*bin(m)0*: "
                                f"{sorted(obs - allowed)[:3]}")
            if L == ell + 1 and has_ones:
                failures.append(f"m={m}: forbidden word 1^{L} occurred")
        # sanity: bin(m) itself is realized (the blocks really are there)
        if format(m, "b") not in factors(bits[TRANSIENT:WINDOW_END],
                                         len(format(m, "b"))):
            failures.append(f"m={m}: bin(m) block not found (construction bug)")

    # Known-answer control: random real -> pipeline must see the forbidden
    # word AND escape the factor language (red side of the checker).
    rng = random.Random(20260829)
    r_num = rng.getrandbits(E)
    control_hits = 0
    control_escapes = 0
    for m in MS:
        ell = len(format(m, "b"))
        bits = frac_bits(m * r_num, E)
        obs, allowed, has_ones = analyze(bits, m, ell + 1)
        control_hits += has_ones
        control_escapes += (not obs <= allowed)
    if control_hits != len(MS):
        failures.append(f"CONTROL BLIND: 1^(l+1) seen in only "
                        f"{control_hits}/{len(MS)} random multiples")
    if control_escapes != len(MS):
        failures.append(f"CONTROL BLIND: factor language escaped in only "
                        f"{control_escapes}/{len(MS)} random multiples")

    if failures:
        print("FAIL")
        for f in failures:
            print("  " + f)
        return 1
    print(f"PASS: for all m in {MS}, tail factors of m*x lie in 0*bin(m)0*, "
          f"1^(len+1) absent, bin(m) present; control saw both failure modes "
          f"({len(MS)}/{len(MS)} each).  Window [{TRANSIENT},{WINDOW_END}).")
    return 0

if __name__ == "__main__":
    sys.exit(main())
