# HANDOFF — pi route 2 (prime reservoir), lap 1 — 2026-10-26

## Node graph
- `PiPrimeReservoirSupport` (route premise, 70% truth, untested) —**green edge**→ `IsDisjunctive 16 π`
  via `pi_disjunctive_of_primeReservoirSupport` (assumes `PiBBP`; axiom-clean).
- `fresh_prime_dvd_head_den`: **proved** (p-adic norm: unique pair (p/8, p%8) carries the pole,
  every other fraction p-integral since denominators lie in (0, 2p)).  Helper lemmas
  `bbpCoeff`, `bbpRationalHead_eq_sum_product`, `padicNorm_bbpFrac_le`,
  `padicNorm_le_one_of_not_dvd_den`.

## This lap
Both "First (one lap)" bridges closed, `#print axioms` = [propext, Classical.choice, Quot.sound].

## Next move
Research question: the probe `scripts/pi_route2_joint.py` — exact (fract R_n, fract S_n) for
n ≤ ~3000, 2-D discrepancy + correlation, with control replacing prime denominators by a
non-prime set.  Then name the weakest node giving joint support (costume audit + corner check).
