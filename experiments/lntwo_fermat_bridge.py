#!/usr/bin/env -S uv run --quiet --with sympy python3
"""Probe: the Fermat-quotient bridge at prime-adjacent indices (R3 door).

Claim (from Glaisher / Z.-H. Sun, sweep doc 2026-08-29; unit UNPINNED there):
  A_{p-1} == L_{p-1} * q_p(2)  (mod p)
where A_n = lnTwoNum n = sum_{k=1}^{n} (L_n/k) 2^{n-k},  L_n = lcm(1..n),
and q_p(2) = (2^{p-1} - 1)/p mod p is the Fermat quotient.

Derivation being tested: x_{p-1} = A/L = sum 2^{p-1-k}/k = 2^{p-1} * sum 1/(k 2^k)
== 1 * q_p(2) (mod p), using 2^{p-1} == 1 and Sun's sum_{k<p} 1/(k 2^k) == q_p(2).

Also reported:
  - Wieferich cases (q_p(2) == 0): the degenerate primes for the door.
  - distribution sanity of q_p(2)/p (should look uniform on [0,1)).

Everything is exact modular arithmetic; O(p) per prime.
"""

from sympy import primerange

P_MAX = 20_000

ok, bad = 0, []
wieferich = []
qvals = []
for p in primerange(3, P_MAX):
    n = p - 1
    # L = lcm(1..n) mod p  (p does not divide L since all factors < p)
    L = 1
    lcm_exact_mod = 1
    # compute lcm(1..n) mod p via factor accumulation: lcm = prod over primes r<=n of r^floor(log_r n)
    from sympy import primerange as pr2
    Lmod = 1
    for r in pr2(2, n + 1):
        e = 1
        while r ** (e + 1) <= n:
            e += 1
        Lmod = (Lmod * pow(r, e, p)) % p
    # A mod p = sum_{k=1}^{n} (L/k mod p) * 2^{n-k}
    A = 0
    for k in range(1, n + 1):
        A = (A + Lmod * pow(k, -1, p) * pow(2, n - k, p)) % p
    q = ((pow(2, p - 1, p * p) - 1) // p) % p
    qvals.append(q / p)
    if q == 0:
        wieferich.append(p)
    if A == (Lmod * q) % p:
        ok += 1
    else:
        bad.append((p, A, (Lmod * q) % p))

print(f"== Fermat-quotient bridge check, primes 3 <= p < {P_MAX} ==")
print(f"A_(p-1) == L_(p-1) * q_p(2) (mod p):  {ok} hold, {len(bad)} fail")
if bad:
    print(f"   FIRST FAILURES: {bad[:5]}")
print(f"Wieferich primes in range (q_p(2)=0): {wieferich}   [known: 1093, 3511]")
# crude uniformity check of q_p(2)/p
buckets = [0] * 10
for v in qvals:
    buckets[min(9, int(v * 10))] += 1
print(f"q_p(2)/p decile counts (uniform-ish expected): {buckets}")
