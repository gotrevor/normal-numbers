# HANDOFF 2026-10-10 — operator gate 4 (shared-phase {2,3} core at 4.49), lap 3

Branch `proof/uniformbad-threshold`, HEAD 2c33b8a6. No uncommitted edits (only scripts/cstar_models/__pycache__).

## Done
- Measurement: kill test negative (shared phase >> per-level abs3 baseline, which dies).  Codex review fixes
  (per-C SFT `gen_sft.js` = sft45 at 4.5; review suite 4/4; bin000 relabel; corner artifact = closed touching).
- Containment pruning (twoThreeBad semantics) + exact interval certifier `scripts/cstar_models/exactinf3.c`
  (build: `leanc -O2 [-DSFT_H='"sft449.h"'] -o X exactinf3.c`; run `X N M D C 0 16 c G [dump]`).
  FLOAT CERTIFICATES at growth 9/5, D=6: c=4.5 (N=128 M=12/24, N=256 M=12); **c=4.49 N=128 M=24**
  (weights `v449_N128_M24_D6.txt.gz`; final pass 5.3M boxes / 146M leaves).  Entry (`entry.js`): root weight 1.
  All numbers: `scripts/cstar_models/shared3_results.txt`.
- Lean (`src/NormalNumbers/UniformBadCoherent.lean`, all proved): coherentBlockCertificate_of_weights,
  coherentBlockCertificate_of_good, alive_of_not_bad, clean449_alive, two_rpow_lt, forb2_of_window,
  good449_clean, coherentTwoThree449_of_clean.  `coherentTwoThree449` (frozen, unchanged statement) now
  = coherentTwoThree449_of_clean cleanCertificate449; the ONLY sorry is `cleanCertificate449` (50%),
  stated on `Good449`.  BarrierAudit crux link moved to it.

## Next (in order)
1. Base-3 bridge: for a Good449 cell (k ≥ 5) with signature (sft state, x = frac(3^n a/2^k), rho = 3^n/2^k,
   n = pending stage), descendant j is Good iff its interval avoids the new-stage windows (and Acc2).
2. Finite decide: the 25-state automaton (sft449) tracks Acc2 (check over all words ≤ 13 bits; δ2hi =
   4451/100000 — regenerate the SFT with δ2hi instead of float 2^-4.49 so they match).
3. Exact Lean checker (native_decide) re-running the target-pruned B&B with rational δ3 bounds and
   rational rho/δ bin edges, against stored weights; soundness lemma.
4. Early levels 0–4 by backward recursion; root weight > 0 (numerically 1).
Margin note: G=1.82 at c=4.5 D=6 did not converge; 9/5 is close to the edge at N=128.
