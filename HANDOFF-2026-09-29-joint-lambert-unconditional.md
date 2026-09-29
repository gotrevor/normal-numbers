# Handoff: the joint Lambert headline is UNCONDITIONAL

**Date** 2026-09-29 · **Branch** `proof/joint-lambert-unconditional` · **HEAD** `9f0003a` (proof commit `f6fbf87`) ·
`lake build` 🟢 10481 jobs · tree clean · nothing pushed.

Scope was `sorry-free: src/NormalNumbers/JointLambertUnconditional.lean`. **Met.**

## The result

    NormalNumbers.JointLambert.jointLambertDisjunctivity_unconditional : JointLambertDisjunctivity
    NormalNumbers.JointLambert.jointWords_two_four_unconditional       : JointWords ({2, 4} : Finset ℕ)

No hypotheses. `#print axioms` = `[propext, Classical.choice, Quot.sound]` on both. The frozen
statements of `JointLambertStatement.lean` are unchanged, and every pre-existing
`JointLambert*.lean` is byte-for-byte identical to `20d5f75` (`git diff --numstat 20d5f75` over
them is empty); only `src/NormalNumbers.lean` gains three imports.

## The mathematical advance

`AGP` was never the consumer's obligation. `docs/JOINT-LAMBERT-AGP-GAP.md` correctly audits the
obstacles to the *strong* `AGP` statement, but the qualitative joint-Lambert headline asks for
much less, and two avoidable demands of the old schedule hid that.

1. **The CRT modulus was tied to the search endpoint.** `X = 2^{4k⁴}` with `B ≤ 2^{k⁴}` puts
   `B = X^{1/4}` — precisely the AGP range. Nothing downstream needs the tie: `X` may grow as
   fast in the killed-window height `k` as we like. At `X = 2^{4k¹²}` the same `B` sits in the
   **Siegel–Walfisz** range, `log B = k⁴ ≪ √log X = 2k⁶√log 2`, where the already-proved and
   axiom-clean `exists_pointwise_exponential_distribution` applies.
2. **A lower bound on the excised conductor was demanded.** `exists_prime_allocation` dodges any
   finite set of non-unit moduli at one pool prime each, with no size hypothesis, so `AGP`'s
   `D > log X` clause was never needed. `P = 1` costs nothing, `P` prime costs at most one prime,
   so `D₀ = 1` in `pool_card_ge`.

**The decisive inequality** (`eventually_rescaled_error_small`): the relative error budget is
`4C·k¹²·exp(k⁴ log 2 − η k⁶ √log 2) → 0` because `k⁶ ≫ k⁴`. The *identical* computation on the
old schedule gives `exp(k⁴ log 2 − η k² √log 2) → +∞`. That divergence, and nothing else, is what
forced AGP.

## The chain

    exists_rescaled_prime_supply                (JointLambertRescaledPrimes) — the crux
      ← exists_pointwise_exponential_distribution  (proved, installed)
      ← Erdos446.eventually_primeCounting_tenth_bounds  (π(x) ≥ (9/10)x/log x)
    exists_joint_prime_candidates_rescaled      (JointLambertRescaledPrimes)
      ← primeIntervalSupply_holds, exists_prime_allocation, count_lower_bound at k³
    exists_joint_small_tail{,_all_bases}_rescaled  (JointLambertRescaledTail)
      U = 2^{k¹²}, X = U⁴, H = U³, Z = U⁶; near tail (192k²⁴+128k¹²)/2^k → 0,
      far tail 4·2^{6k¹²}/2^{2^k} → 0, both via eventually_nat_poly_le_two_pow
    jointWords_unconditional                    (JointLambertUnconditional)

## Still open (unchanged, and no longer on the headline's critical path)

`AGP`, `AGPExpRange`, `exceptionalModulus_gt_log`, `agpExpRange_holds` in
`JointLambertPrimeSelection.lean` / `JointLambertAGPRange.lean`. Nothing here proves or uses them.
The `JointLambertAGPRange` sorries are designated-open audit surface; do not attack or relocate.

## Next dependency, if this line is continued

The natural next target is the **quantitative** statement (the paper's frequency count) rather
than the qualitative common-position one. That does need a genuine density input, and the
rescale trick does not reach it: the candidate density `1/(16k¹²)` is enough for "some index
exists" but the frequency statement needs the count uniform in the *base*, which re-couples `X`
to the window. Expect AGP, or a log-free zero-density estimate, to be genuinely required there.

## Gotchas found this lap

- A wide cold `lake build` on this box hits the EMFILE ceiling in a rotating set of upstream
  targets. Loop: extract `✖ … Building <target>` names, build each singly, retry. Converged in
  ~3 rounds; the residual single failure was my own file's real error, misread as a flake.
- `le_or_lt` → `le_or_gt`; `tendsto_pow_mul_exp_neg_atTop_nhds_zero` lives in the `Real`
  namespace; `tendsto_pow_const_div_const_pow_of_one_lt` is the clean polynomial-vs-`2^k` source.
- `set x : ℝ := (n : ℕ)` makes `exact_mod_cast` fail on the folded name; `rw [hx]` first.
- When porting by textual exponent substitution, `(k : ℝ) ^ 4` does **not** contain the substring
  `k ^ 4`. Both spellings must be rewritten, and the higher degree first.

## Files

New: `KICKOFF-2026-09-28-joint-lambert-rescale.md`,
`src/NormalNumbers/JointLambert{RescaledPrimes,RescaledTail,Unconditional}.lean`,
`docs/JOINT-LAMBERT-RESCALED-PROOF.md`.
Changed: `src/NormalNumbers.lean` (3 imports), `docs/JOINT-LAMBERT-AGP-GAP.md` (correction §).
