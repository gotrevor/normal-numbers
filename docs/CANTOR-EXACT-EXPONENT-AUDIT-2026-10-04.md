# Audit: `K` ∩ exact irrationality exponent `μ₀` ∩ normal to every base prime to 3 (2026-10-04)

Rank 1 of `docs/OPEN-PROBLEMS-SWEEP-2026-10-04.md`.  Frozen in
`src/NormalNumbers/CantorExactExponent.lean` (range `μ₀ > 2 + log₂ 3`) and
`src/NormalNumbers/CantorExactExponentStretch.lean` (all `μ₀ > 2`).  Direction only; the Lean
files are the record.

## Statement as frozen

`CantorExactExponent.exists_computable_mem_cantorSet_irrExponent_normal`: for rational
`μ₀ > threshold = 2 + log₂ 3 ≈ 3.585`, a computable `e` with `x = cantorExpReal μ₀ e ∈ cantorSet`,
`HasIrrExponent x μ₀`, `IsNormal b x` for every `b ≥ 2` with `3 ∤ b`, and `¬ IsNormal 3 x`.

`HasIrrExponent x μ₀ := (∀ p < μ₀, LiouvilleWith p x) ∧ ∀ p > μ₀, ¬ LiouvilleWith p x`.  Mathlib
(v4.33.1 pin) has no irrationality-exponent definition; `LiouvilleWith` carries a constant `C`,
which does not move the supremum, so this is the usual exponent.

Source wording (Bugeaud 2012): p. 219 "There exist Liouville numbers in the middle third Cantor
set K and there are Liouville numbers which are normal to base 2.  Furthermore, K contains
numbers normal to base 2.  But we do not know whether there are real numbers with all these three
properties."  Thm 7.21 (p. 158): "Let μ ≥ 2.  The middle third Cantor set K contains uncountably
many elements whose irrationality exponent is equal to μ."  The frozen statement is the
finite-exponent triple between the two; it is not a numbered problem.

## Corrections to the sweep

1. **Threshold `4.17 → 3.585`.**  The sweep summed `q` balls per denominator.  Only
   `O(2^{F(m)})` numerators reach the support at `q ≈ 3ᵐ` (`card_near_le`), so the block cost
   is `3ᵐ 2^{−W(m)}` with `W` the free count in the window `(m, τm]`, not `3^{2m} 2^{−F(τm)}`.
   On the Borel–Cantelli range `W(m) ≥ (μ₀ − 2)m − C` (`window_freeCount_ge`, valid for every
   `μ₀ > 2`), summable iff `μ₀ − 2 > log₂ 3` (`summable_bc_of_threshold_lt`).  The binding point
   is the window entering run `k+1` at `m = a_{k+1}/(τ−1)`; the window starting inside run `k` at
   `m = (μ₀−1)a_k` binds only below `μ₀ ≈ 3.07`.
2. **Profile.**  The sweep's "not normal to any base with `3 ∣ b`" does not follow for finite
   `μ₀`: the run argument needs the run to cover a fraction `> 1/b` of the `b`-adic orbit, which
   holds when `2 log₃ b < μ₀` (`not_isNormal_of_three_dvd_of_small`) and fails for, e.g.,
   `b = 3·2¹⁰` (`log₃ b ≈ 7.3`).  Cassels makes `μ_K`-a.e. point normal to such bases, so the
   true profile at large `b` with `3 ∣ b` is unknown.  The headline therefore claims
   `3 ∤ b → normal` and `¬ normal to 3`, not `↔`.

## Difficulty check

- **Proved implications (existing):** `CantorLiouvilleAll.secondMoment_le_b` (every free set),
  `CantorLiouville.not_isNormal_three_pt`, `SchedFamily.exists_computable_normal_sched_family'`
  (with a `bad'` slot), the 10.37 lower-bound argument.
- **Unproved premise:** `ae_not_liouvilleWith` (Borel–Cantelli upper bound), and its computable
  form `exists_exponent_tests`.
- **Mechanism:** trivial numerator count + Frostman ball mass + triangle inequality at the forced
  approximations.  Paper proof about one page; Lean needs the counting, the ball mass, the
  window count and prefix tests.
- **Refusal below the threshold:** at the run entry the window holds `≤ a_{k+1} − m` free places
  (`freeCount_window_le_of_run`).  Kernel controls on the real schedules:
  `bcTerm_red_mu_three` (`μ₀ = 3`, `m = 108`: window `108`, cost `3^{108}/2^{108} > 1`) and
  `bcTerm_green_mu_four` (`μ₀ = 4`, `m = 128`: window `256`, `2^{256} > 3^{128}`).  The method
  separates the two sides of `3.585` on the actual `expFree` schedules.
- **Base-3 sibling:** `not_isNormal_three_cantorExpReal` (every `ω`).
- **Stretch `2 < μ₀ ≤ 3.585`:** needs a count of rationals near `K` beyond the trivial one.  BFR
  and Bugeaud–Durand (18) are open for `K`; He–Liao 2602.01307 Cor. 6.5 is a proved local
  equidistribution with a small, non-explicit exponent `α − 1`, for the self-similar measure.  At
  best it reaches `μ₀` near 2 after a transfer to the forced-run measure.  10%.

## Prior-art log (this audit; the sweep's log in §1.4 there is not repeated)

| Search | Result |
|---|---|
| `papers followups 1812.10689` (Schleischitz, 26 citers) | rationals in `K`, dyadic approximation; no normality |
| `papers followups 2309.05851` (Fraser–Wheeler) | 2 citers, Fourier dimension, not `K` |
| `papers followups 1601.00153` (Becher–Reimann–Slaman), PDF read | 7 citers, none relevant.  Thm 1: a Cantor-like set `E` (not `K`) with uniform-measure-a.e. exponent `a`; no normality |
| `papers followups 2203.12477` (Baker) | dyadic approximation only |
| `papers followups 2409.08061` (Bénard–He–Zhang, 24 citers) | He–Liao 2602.01307, 2608.15686; S. Chen 2510.17096; none on normality |
| `papers followups 2602.01307`, `2510.17096` | He–Liao, Daviaud (intrinsic); nothing on the triple |
| `papers followups` on Bugeaud 2008 (Math. Ann.) and 2002 (CRAS) DOIs | nothing combining `K`, exponent, normality |
| OpenAlex: citers of Bugeaud 2012 (W1557463835, 200 listed), title filter | Hochman–Shmerkin, Dayan–Ganguly–Weiss, Becher–Heiber–Slaman; none on the triple |
| OpenAlex keyword searches (4) | Becher–Lew Deveali 2607.06773 (sparse binary Cantor sets, no exponent), Morris 2025 (T-numbers in `K`, non-normal), Feng 2026 (non-normal, not `K`) |
| Web search (6), incl. "Problem 10.37", "Cantor set" + "irrationality exponent" + "normal" | nothing on the triple |
| PDFs read: Bugeaud–Durand (JEMS 2016), Chow–Varjú–Yu 2402.18395, Hochman–Shmerkin 1302.5792, Bugeaud 2012 Ch. 7 | see citable statements below |

Instrument limits: arXiv export API not used (429 in the sweep); OpenAlex, Semantic Scholar
(`papers followups`), web search and direct PDF reads.  Citers of the book were filtered by
title, not full text.

**Verdict:** not found.  No paper gives `x ∈ K` with exponent exactly `μ` (any finite `μ > 2`)
normal to base 2.  Closest: Bugeaud Thm 7.21 (lacunary points of `K`, no base-2 claim), Thm 7.23
Amou–Bugeaud (normal to base `b` with exponent `μ`, not in `K`), Thm 7.25 Kaufman (Fourier route,
closed on `K`).  Freshness about 75%.

Citable statements verified against the text: Bugeaud 2012 Thm 7.16 (Weiss: `v₁ = 1`
`μ_K`-a.e.), Thm 7.15 (Cassels), Thm 7.21; Bénard–He–Zhang 2409.08061 Thm A (Khintchine
dichotomy for self-similar measures); Hochman–Shmerkin Thm 1.1 (needs convergent scenery, which
the forced runs destroy, so it does not give normality here off the shelf); He–Liao 2602.01307
Cor. 6.5.  Weiss 2001 itself: abstract only.

## Cited Props (need a referee)

- `CantorExactExponentStretch.Literature.Weiss2001` (new): `μ_K`-a.e. point has no
  `LiouvilleWith τ`, `τ > 2`.  Checked against Bugeaud Thm 7.16 and the Weiss abstract, not the
  paper.  Used only by the `μ₀ = 2` control.
- `CantorExactExponentStretch.Literature.Bugeaud2008Thm721` (new): existence form of Thm 7.21.
  Cited, unused.
- `CantorLiouvilleAll.Literature.Cassels1959` (existing, refereed with 10.37).

The headline and all its leaves use no cited Prop.

## Lean decls

Headline: `NormalNumbers.CantorExactExponent.exists_computable_mem_cantorSet_irrExponent_normal`
(wiring, proved from leaves).  Sorry leaves: `expForced_recur`, `liouvilleWith_cantorExpReal`,
`ae_frequently_two`, `abs_sub_ge_of_near`, `coins_ball_le`, `card_near_le`,
`window_freeCount_ge`, `summable_bc_of_threshold_lt`, `freeCount_window_le_of_run`,
`ae_not_liouvilleWith` (crux), `le_freeCount_exp`, `ae_isNormal_of_coprime_three`,
`not_isNormal_of_three_dvd_of_small`, `exists_exponent_tests`, `exists_computable_normal_avoid`.
Proved: `one_lt_threshold`, `expRun_anchor_four`, `bcTerm_red_mu_three`, `bcTerm_green_mu_four`,
`not_isNormal_three_cantorExpReal`, `ae_hasIrrExponent`, `exists_mem_cantorSet_irrExponent_normal`.

Stretch: `exists_computable_mem_cantorSet_irrExponent_normal_all` (10%),
`ae_not_liouvilleWith_all` (15%), `exists_mem_cantorSet_irrExponent_two_of_literature` (90%).

## Confidence and lap estimate

Headline 65%: mathematics about 85% (the B-C bound above `3.585` is a routine count once the
window lemma is right; the window lemma was checked case by case), Lean cost the rest.  Laps:
3 to 5 (ball mass + count: 1; window + summability: 1; a.e. assembly: 1; prefix tests and
derandomizer wiring: 1 to 2).

## Addendum 2026-10-05: He–Liao transfer checked, wall

Lap 2 closed the main file (both headlines `propext, Classical.choice, Quot.sound`, re-checked
on the Mac).  The open question from this audit, whether He–Liao 2602.01307 Cor. 6.5 transfers
from the Cantor measure to the forced-run measure, is answered no, for two reasons recorded in
Lean in `CantorExactExponentStretch.lean`:

* the trivial count fails only in run-entering windows, where the event concerns the discrete
  endpoint `P/3^b` below the cylinder scale (`endpoint_sep`); thickening costs `3^{2m−b} ≥ 1`
  for `μ₀ ≤ 3` (`thickening_cost_ge_one`), so even a Bugeaud–Durand-strength measure count
  reaches at best `μ₀ > 3`;
* Cor. 6.5's main term needs `α ≥ τ − 2 > 1` in those windows, and its `α − 1` is small and
  not explicit.

Reopen condition: `EndpointRationalCount` (a count on the discrete endpoints at the heuristic
density).  Maze row "He-Liao local count on the forced-run measure"; crux link for
`ae_not_liouvilleWith_all` with the new barrier `cantorExp_trivialCount_mu_three`.
