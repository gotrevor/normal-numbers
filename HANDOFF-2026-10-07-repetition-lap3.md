# HANDOFF 2026-10-07: repetition lap 2 end (branch proof/cantor-repetition, HEAD 1af91564)

Supersedes repetition-lap2/lap1.  Operator kickoff: KICKOFF-2026-10-06-repetition.md.  Tree clean.

## State (src/NormalNumbers/CantorRepetition.lean, 2 sorries)
- `repPairArith_of_three_dvd` (crux leaf, node `RepPairArith`, measure-free, summable-along-sched).
- `repPairArith_of_inputs` (assembly, 60%): Baker (`CantorExactExponentProfile.Literature.
  BakerLogDiscrepancy`) + `TOrbitCyclicDecay t` + `BadGcdSparseH b` ⇒ RepPairArith.  Zone plan in
  its docstring (copy / band / top-window-in-gap / low-window).
Chain proved: RepPairArith ⇒ RepPairDecay ⇒ a.e. normal to 3ˢt ⇒ liouvilleCantorFullProfile.

## Construction (REDESIGNED this lap)
Only EVEN runs copy (`src`); odd runs are fresh coins.  Gap ratio between copy runs 4(k+3) → ∞,
which fixes the large-t (log₃b/s ≥ 2) gap-spanning class.  Liouville uses runs 2n (unchanged).

## Proved this lap (copy-zone toolkit, all Even k)
src_eq_iff_block, srcWeight_block, prod_block_eq_cyc, cycProdR(_lip/_add_int/_neg),
norm_charFun_repReal_le_cyc(_int), repBound (+ _le_repBound, _some_add, _some_neg),
repBound_pair_le('), copyRun_sum_le, cycProd_pairH, int_gcd_mul_le, copyZoneDecayH_of,
secondMoment_le_pairs, eq_three_pow_of_pow_eq, gcd_small_of_CZ (lit. node CZGcdPow).
Nodes: CopyZoneDecayH, BadGcdSparseH, ExpOrderPeriods (short-period alternative), CZGcdPow.

## Probes
scripts/rep_arith.py: greedy RepPairArith at the 1/N floor for b=2,6,12 (N ≤ 380, incl.
gap-spanning windows for b=12); b=9 control flat .25–.30.  scripts/rep_order.py: ord of 2 mod
3^ℓ−1 is 3^{(.56–.90)ℓ} at prime ℓ.

## Next
1. `isFresh i := isFree i || odd-run i`; prove ‖𝔼e(ξ repReal)‖ ≤ Bf isFresh M ξ (rest reads only
   even-run block coins; mimic charFun_add/repCopy_congr) and switch `repBound none` to it.
2. Assembly: per N, κ = run of v=s·min when window inside even run k (copyRun_sum_le +
   copyZoneDecayH_of), band trivially, top-in-gap via bf_le_topProd + sum_topProd_le, low window
   via Cassels low-digit count.
3. Walls (open math): TOrbitCyclicDecay (cyclic digits of tᵐc mod 3^a−1), BadGcdSparseH (long
   shifts), Baker (cited).
