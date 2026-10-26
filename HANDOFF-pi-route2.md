# HANDOFF — pi route 2 (prime reservoir), lap 1 — 2026-10-26

## Node graph
- `PiPrimeReservoirSupport` (route premise, 70% truth, untested) —**green edge**→ `IsDisjunctive 16 π`
  via `pi_disjunctive_of_primeReservoirSupport` (assumes `PiBBP`; axiom-clean).
- `fresh_prime_dvd_head_den`: **proved** (p-adic norm: unique pair (p/8, p%8) carries the pole,
  every other fraction p-integral since denominators lie in (0, 2p)).  Helper lemmas
  `bbpCoeff`, `bbpRationalHead_eq_sum_product`, `padicNorm_bbpFrac_le`,
  `padicNorm_le_one_of_not_dvd_den`.

- `PiReservoirDiagonalSupport` (new node, weaker in form): premise → node
  (`reservoirDiagonalSupport_of_support`), node + PiBBP → sink
  (`pi_disjunctive_of_reservoirDiagonalSupport`); both green, axiom-clean.
- Probe `scripts/pi_route2_joint.py` N=1500: fresh-prime pair chi²/cell 0.96, no empty 8×8 cell,
  corr +0.0075; composite control equally uniform (chi² 1.05) ⇒ probe does not discriminate primality.

- Lap 2: `bbpPrimeReservoir_succ` (PrimeReservoirStep.lean, green): R_{n+1} = 16R_n − exit_n + entry_n,
  exit = primes in (4n,4n+4] (O(1) mass mod 1, the arithmetic source), entry = j=n pair (O(1/n)).
  Since R+S = 16ⁿ·sₙ evolves by ×16 + kick, the antidiagonal D = R−S gets the kick −2·exit:
  the diagonal node asks D ≈ 0 simultaneously with R+S ≈ 2t.

## This lap
Both "First (one lap)" bridges closed, `#print axioms` = [propext, Classical.choice, Quot.sound].

## Next move (lap 3)
State S_{n+1} = 16 S_n + exit_n + 16·kick_n − entry_n, then the node: exit_n mod 1 (one or zero
primes in a length-4 window, p≡1,5 mod 8) is equidistributed / dense along the subsequence where
fract(16ⁿπ) is in a given interval — and test it numerically against a non-prime control.
## Older next move
Find a control that FAILS (rational telescoping lock from PI-ROUTES-NEXT), so the probe
discriminates; then attack the diagonal node via a Weyl sum along e(h(R−S)) — the
antidiagonal character is exactly what the diagonal node needs.
## Old next move
Research question: the probe `scripts/pi_route2_joint.py` — exact (fract R_n, fract S_n) for
n ≤ ~3000, 2-D discrepancy + correlation, with control replacing prime denominators by a
non-prime set.  Then name the weakest node giving joint support (costume audit + corner check).
