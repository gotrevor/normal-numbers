# HANDOFF 2026-09-24 (lap 16, review lap) — swing at C3, branch `wip/swing-c3`

**Checkpoint.**  HEAD `1c48626`+, `lake build` green, **9197 jobs**.  `src/` holds **2** swing
sorries (`weylLambertTwist_holds`, `tailLargeDecouple_holds`) plus the 2 designated-open
off-campaign ones (`PrimeLambertOscillation`, `MahlerDriftOne`) — do not touch those.

Obey `DIRECTION.md` → CURRENT DIRECTIVE (rewritten this lap), then
`KICKOFF-2026-09-24-swing-c3.md`.  Previous baton: `HANDOFF-2026-09-24-swing-c3-lap15.md`.
Detailed record: `PENDING_WORK.md` → "lap 16".  Durable overview: `STATUS.md`.

## Review verdict: route KEPT, **method PIVOTED**

The crux is still `weylLambertTwist_holds` — `(1/N)∑_{n<N} e(jn/Q)·e(h·b^n·L_P) → 0` — and
`conjC3_via_weylLambert : ConjC3` depends on that ONE leaf.  No route trigger fired.  What
changed is the method: laps 5–15 were all tuning the two terms of the master inequality, and this
lap (a) closed the first term as far as the method allows, and (b) proved the second term's whole
family cannot be closed.  **Further `K`-tuning / period / `L¹`-tail work is now forbidden.**

## 1. New, proved, axiom-clean: `src/NormalNumbers/SwingC3Var.lean`

    norm_sum_addChar_prod_le :
      ‖∑_{n<N, n≡a [MOD m]} e(jn/Q) ∏_{p∈F} g_p(n)‖ ≤ Q · ∏_{p∈F} (1 + V_p),
      V_p = ∑_{r<p} ‖g_p(r) − 1‖

for `p`-periodic `g_p`, pairwise-coprime `F`, everything coprime to `Q`.  Uniform in `N`, and the
period `∏_{p∈F} p` is GONE.  This is the "sub-trivial incomplete-sum bound" lap 15 named as the
only structurally untried handle.  Proof: peel one prime, refine the ambient progression by CRT,
base case an AP character sum `≤ Q` (`norm_sum_addChar_ap_le`), built on a sharper stub bound
`norm_sum_range_le_sum_norm_period` (`‖∑_{n<N}g‖ ≤ ∑_{n<L}‖g‖`).

Instantiated at the crux, `V_p ≤ 16|h|/(b−1)` — the **exact** complete-period mass of lap 12's
`sum_range_tailPrimeTerm_period`, a constant independent of `p`.  Hence

    norm_sum_addChar_tailTrunc_le_var : ‖∑_{n<N} e(jn/Q)e(h·tailTrunc_K)‖
        ≤ Q·(1 + 16|h|/(b−1))^{π(K)−π(P)}          (was  Q·∏_{P<p≤K} p ≈ Q e^K)

`var_pow_le_primePeriod` machine-checks it is never worse; `norm_sum_addChar_tailLarge_le_var` is
the master inequality with the sharpened first term.  Window: `K ≲ log N` → `K ≲ log N·loglog N`.

## 2. Proved-by-analysis, recorded as REFUTED: the truncation/`L¹` family

The discarded mass is `≍ N(loglog N − loglog K)`, so it needs `K = N^{1−o(1)}`, and:
* the improved period term buys only a `loglog` factor in `K` — mass unchanged;
* the full subset expansion with absolute values gives `(log N)^{c−1}` on `∏_T p ≤ N/Q` (useful
  only for `c = ∑_d min(2,2π|h|b^{−d}) < 1`, i.e. `|h| ≲ b/6`) and `(log N)^{c}` on the rest;
* Rankin / Dickman smooth trimming reduces the residual mass only from `loglog N` to `logloglog N`.

So **the tail must be treated with its signs**; see `PENDING_WORK.md` lap 16 §2 for the three
computations.  Do not re-derive them.

## 3. The next attack (in order)

1. **The signed skeleton.**  Formalize `w_p := (1/p)∑_{r<p}(e(h·tailPrimeTerm b p r) − 1)`; prove
   `p·w_p → w = ∑_{d≥1}(e(hb^{−d}) − 1)` and `Re w_p < 0`; aim at `∏_{P<p≤K}(1+w_p) ≍
   (log K)^{Re w}`.  Numerically calibrated: `−Re w = ∑_{d≥1}(1−cos 2πhb^{−d})` gives `a = 1.76`
   for `b=3,h=1` against lap 11's measured `a ≈ 1.9`, and is consistent with the exact symmetry
   `|A_N(h,j)| = |A_N(hb,j)| + O(1/N)` (so WLOG `b ∤ h`).
2. **The `ω`-bridge.**  Put the exact identity `tailLarge P b n = ∑_{m≥1} b^{−m}·ω_{>P}(n+m)` in
   `src/`.  It converts the crux into a correlation of `z_m^{ω}` at the shifts `m = 1..D` with
   `D → ∞` (fixed `D` leaves `b^{−D}loglog N → ∞`), each factor non-pretentious — i.e. Elliott
   with slowly growing order.  Then a named `conjC3_of_H` against that hypothesis.
3. Cheap and on-path but NOT the crux: `SwingC3Convergent.setTail_addChar_tendsto` (both halves
   proved since lap 15; only the ε-bookkeeping remains).

## Gotchas recorded this lap
* `Finset.range_subset` is still not the `m ≤ n` iff here — prove subsets by hand.
* `positivity` cannot see `0 ≤ 16|h|/(b−1)` without `2 ≤ b`; use `div_nonneg _ (by linarith)`.
* `Nat.count_modEq_card` + `Nat.count_eq_card_filter_range` give the AP count in `range (m*Q)`
  for free; `Nat.chineseRemainder` + `Nat.modEq_and_modEq_iff_modEq_mul` merge two congruences
  into one modulus without any `ZMod` plumbing.
* `Finset.induction_on` case names here are `empty` / `@insert q s hq ih`.
