# HANDOFF 2026-09-24 (laps 16–18) — swing at C3, branch `wip/swing-c3`

**Checkpoint.**  HEAD `4cba3b4`, working tree CLEAN, nothing to push (host pushes).
`lake build` green, **9198 jobs**.  `src/` holds **2** swing sorries
(`weylLambertTwist_holds` — the crux; `tailLargeDecouple_holds` — ratified, kept per the kickoff
addendum) plus the 2 designated-open off-campaign ones (`PrimeLambertOscillation`,
`MahlerDriftOne`) — do not touch those.

Obey `DIRECTION.md` → CURRENT DIRECTIVE (rewritten at lap 16; it OUTRANKS this file), then
`KICKOFF-2026-09-24-swing-c3.md`.  Previous baton: `HANDOFF-2026-09-24-swing-c3-lap15.md`.
Detailed record: `PENDING_WORK.md` → laps 16, 17, 18.  Durable overview: `STATUS.md`.

## The state in one paragraph

`CastingOut.conjC3_via_weylLambert : ConjC3` rests on ONE named `sorry`,
`weylLambertTwist_holds`: `(1/N)∑_{n<N} e(jn/Q)·e(h·b^n·L_P) → 0` for `0 < j < Q`,
`L_P = ∑_{p>P} 1/(b^p−1)`.  Lap 16 (review) proved the sharpest period bound the truncation
method admits and **refuted the whole truncate-and-bound-in-`L¹` family**; laps 17–18 built the
signed replacement.  Everything below is axiom-clean (trust triple).

## What laps 16–18 added

| file | content |
|---|---|
| `SwingC3Var.lean` | **Total variation replaces the period.**  `norm_sum_addChar_prod_le`: `‖∑_{n<N, n≡a [MOD m]} e(jn/Q)∏_{p∈F}g_p(n)‖ ≤ Q·∏_{p∈F}(1+V_p)`, `V_p = ∑_{r<p}‖g_p(r)−1‖` — uniform in `N`, **no period `∏p`**.  At the crux's summand `V_p ≤ 16\|h\|/(b−1)` (a constant, = the exact complete-period mass), so `Q∏_{P<p≤K}p ≈ Qe^K` becomes `Q(1+16\|h\|/(b−1))^{π(K)}` (`norm_sum_addChar_tailTrunc_le_var`, `norm_sum_addChar_tailLarge_le_var`; `var_pow_le_primePeriod` checks it is never worse).  Window `K ≲ log N` → `K ≲ log N·loglog N`. |
| `SwingC3Signed.lean` | **The exact Euler product.**  `sum_filter_prod_eq_prod` (CRT: a product of coprime-periodic factors has a factorizing complete sum, over any ambient progression); `primeFactor b p h = (1/p)∑_{r<p}e(h·tailPrimeTerm b p r)`; `sum_range_ee_tailTrunc_eq`: the complete-period mean of the truncated phase is EXACTLY `∏_{P<p≤K} primeFactor b p h`.  Plus **the one-factor estimate** `norm_primeFactor_sq_le`: `‖primeFactor‖² ≤ 1 − Σ_p/p + 2(16\|h\|/(b−1))²/p²`, `Σ_p = ∑_{r<p}‖1−z_r‖²`. |

## The refutation that redirects the campaign (do NOT re-derive — `PENDING_WORK` lap 16 §2)

The discarded mass is `≍ N(loglog N − loglog K)`, needing `K = N^{1−o(1)}`, and: the improved
period term buys only a `loglog` factor in `K`; the signs-free subset expansion gives
`(log N)^{c−1}` only for `c = ∑_d min(2,2π|h|b^{−d}) < 1` (i.e. `|h| ≲ b/6`) and `(log N)^c` on the
complement; Rankin/Dickman trimming reduces the residual mass only from `loglog N` to
`logloglog N`.  **Absolute values cost `∏(1+|w_p|)` where the truth is `∏(1+w_p)`; all the decay
lives in the signs.**  Further `K`-tuning is forbidden drift.

## IMMEDIATE NEXT STEP (lap 19): finish the complete-period half

Three small steps, all elementary, all in `SwingC3Signed.lean`:
1. `Σ_p ≥ ‖1 − e(h·b^{p−1}/(b^p−1))‖²` — one term of a sum of nonnegatives
   (`Finset.single_le_sum`, index `p−1`).
2. `‖1 − ee x‖² = 2(1 − cos 2πx) ≥ 16‖x‖²_ℤ` — reduce `x` mod 1 (`Real.cos_add_int_mul_two_pi`,
   `Real.cos_neg`) into `[−1/2,1/2]`, then mathlib's
   `Real.cos_le_one_sub_mul_cos_sq : |t| ≤ π → cos t ≤ 1 − 2t²/π²` at `t = 2π‖x‖`.
3. `x_p := h·b^{p−1}/(b^p−1) = h/b + h/(b(b^p−1))`, so for `b ∤ h` and `b^p ≥ 2|h|+1`,
   `‖x_p‖ ≥ 1/(2b)` and hence `Σ_p ≥ 4/b²`.  With lap 18's estimate:
   `‖primeFactor b p h‖² ≤ 1 − 2/(b²p)` for `p ≥ p₀(b,h)`.
Then, since `∑_p 1/p` diverges (mathlib: `Nat.Prime.not_summable_one_div` / the Mertens file),
`∏_{P<p≤K} ‖primeFactor b p h‖ → 0` as `K → ∞`.  **That is the complete-period half of the crux,
unconditional.**  WLOG `b ∤ h` is legitimate: `|A_N(h,j)| = |A_N(hb,j)| + O(1/N)` exactly, from
`tailLarge(n+1) = b·tailLarge(n) − ω_{>P}(n+1)`.

### After that
The remaining gap is purely the *incomplete*-sum half: the Euler product governs
`∑_{n<∏_{P<p≤K}p}` while the crux needs `∑_{n<N}` with `N ≪ ∏_{P<p≤K}p`.  Lap 16's variation
bound is the frame that plugs in there (it is the only bound that is `N`-free and period-free).
Directive item 2 (the `ω`-bridge `tailLarge P b n = ∑_{m≥1}b^{−m}ω_{>P}(n+m)`, siting the crux as
Elliott with slowly growing order, then a named `conjC3_of_H`) remains open and is the fallback
deliverable.  `SwingC3Convergent.setTail_addChar_tendsto` is still cheap, on-path, not the crux.

## Gotchas recorded in laps 16–18
* `Complex.normSq_eq_norm_sq : normSq z = ‖z‖^2` is the bridge to `re`/`im`; `Complex.re_sum`,
  `Complex.im_sum`, `Complex.abs_im_le_norm` are the names here.
* `Nat.count_modEq_card` + `Nat.count_eq_card_filter_range` give AP counts in `range (m*Q)` free;
  `Nat.chineseRemainder` + `Nat.modEq_and_modEq_iff_modEq_mul` merge two congruences into one
  modulus with no `ZMod` plumbing — this is what makes both inductions work.
* `Finset.induction_on` case names here: `empty` / `@insert q s hq ih`.
* `positivity` cannot see `0 ≤ 16|h|/(b−1)` without `2 ≤ b`; use `div_nonneg _ (by linarith)`.
* `set g := …` then `field_simp` fails to match the unfolded form — `simp only [hg]` first.
* `Finset.range_subset` is still not the `m ≤ n` iff in this mathlib.
