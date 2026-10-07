# HANDOFF 2026-10-07: repetition lap 2 (branch proof/cantor-repetition)

Supersedes repetition-lap1.  Operator kickoff: KICKOFF-2026-10-06-repetition.md.

## State
Single open sorry in scope: `repPairArith_of_three_dvd` (node `RepPairArith`, measure-free).
Chain (all proved): RepPairArith ⇒ RepPairDecay (`repPairDecay_of_arith`) ⇒ a.e. normal to
3ˢt (`ae_isNormal_rep_of_pairDecay`, via `secondMoment_le_pairs`) ⇒ `liouvilleCantorFullProfile`.
Nodes are in summable-along-sched form (admits rates exp(−c log N/loglog N)).

Proved this lap: `src_eq_iff_block`, `srcWeight_block`, `prod_block_eq_cyc`, `cycProdR(_lip)`,
`norm_charFun_repReal_le_cyc(_int)`, `repBound`, `norm_charFun_repReal_le_repBound`,
`eq_three_pow_of_pow_eq`, `gcd_small_of_CZ` (from literature node `CZGcdPow`).
Probe `scripts/rep_arith.py`: RepPairArith greedy sums at the 1/N diagonal floor for b=6,12
(N ≤ 200), b=9 control flat .25–.30.

## Mathematical picture
Frequency windows have bounded multiplicative length; runs have length (k+2)a → ∞; so copy coins
carry the bound.  Copy pair term = cyclic digits of h tᵐ(b^d−1) mod 3^a−1, generically WRAPPED
(no-wrap pairs are a 1/(k+2) fraction).  Wall: short multiplicative orbit (length ~ k a, modulus
3^a−1) avoiding low-complexity residues — below BGK range.  This is the real crux
(`TOrbitCyclicDecay`).  `BadGcdSparse`: CZ handles short shifts only.

## Next
1. Assemble RepPairArith ⇐ (copy-zone true-law sum, with κ = run of the window) + free + shadow
   nodes, so the crux is a conjunction of named leaves.
2. Look for a construction-level fix (the frozen statement is ∃ x): e.g. vary the period inside a
   run so the cyclic modulus changes along the run.
