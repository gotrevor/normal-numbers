# Becher–Yuhjtman 2019 — pin note (read in full 2026-08-23)

V. Becher, S. A. Yuhjtman, *On absolutely normal and continued fraction normal
numbers*, IMRN 2019(19) 6136–6161, arXiv:1704.03622.  PDF alongside
(gitignored).  This note maps the proof for the B5′ expedition; page/lemma
numbers are the arXiv v1 numbering.

## Theorem 1

An algorithm computing a number that is absolutely normal AND CF-normal, first
n CF digits in O(n⁴) operations.  NB their "absolutely normal" is proved as
**simple normality to every integer base ≥ 2** (equivalent to full normality
to every base by the classical Pillai/powers equivalence — which WE must also
formalize to state the headline; see W5 in KHINCHIN.md).

## Dependency map — elementary vs deep

**Elementary layer** (all of it is our Counting.lean culture):

- **Prop 2**: non-recursive continuant formula `q_s = α_{1,s}` where
  `α_{r,s} = Σ_{I ∈ Ω_{r,s}} ∏_{i∈I} a_i`, Ω = subsets whose complement splits
  into adjacent pairs.  Monotonicity + the splitting identity
  `α_{1,s} = α_{1,r} α_{r+1,s} + α_{1,r-1} α_{r+2,s}`.
- **Lemma 3** (the workhorse — bounded distortion in elementary clothing):
  `q(a)q(b) ≤ q(ab) ≤ 2 q(a)q(b)` and `|I_b|/2 ≤ |I_{a,b}|/|I_a| ≤ 2|I_b|`.
  One-page algebra from Prop 2.
- **Lemma 7**: CF-discrepancy concatenation calculus (append a good block,
  discrepancy survives; short foreign blocks cost s/n).  Pure counting.
- **Lemma 8** (= Becher–Heiber–Slaman Lemma 2.5, from Hardy–Wright Thm 148):
  #(base-b blocks of length k with discrepancy ≥ ε) ≤ 2b^{k+1}e^{-bε²k/6}.
  Chernoff-flavored combinatorics.
- **Lemma 9**: b-ary discrepancy concatenation (= BHS Lemma 3.1).  Counting.
- **Prop 12**: any interval of measure < d^{-m} sits inside ≤ 2 consecutive
  d-ary intervals of order m.  Trivial.
- **Defs 10–11**: a *t-brick* = (σ_cf, σ_2, …, σ_t): one cf-ary interval
  nested inside one d-ary (or two adjacent d-ary) interval(s) per base
  d ≤ t, with relative length ≥ 1/(16e^{4c}d).  Refinement = extend all
  expansions with per-base discrepancy < ε.
- **Lemma 13** (main): every t-brick admits an ε-refinement, for every large
  enough relative CF order n.  Long but elementary GIVEN Lemmas 5, 6, 8:
  intersect the "good length" collection with the complements of per-base bad
  zones + CF bad zone; measures beat K/√n vs exponentially small.
- **§2.1–2.2**: schedule t(s) = max(2, ⌊(log s)^{1/5}⌋), ε(s) = 1/t(s),
  n(s) = ⌊log s⌋ + n_start; x = ∩ intervals; correctness by Lemma 7/9 chains
  ("for s sufficiently large" bookkeeping).

**Deep imports — exactly two, and BOTH serve only the O(n⁴) claim:**

- **Lemma 4** (Morita 1994 / Vallée 1997): CLT for log qₙ with optimal
  O(n^{-1/2}) error (Ruelle–Mayer transfer operator).  Feeds only Lemma 5
  ("many cf-ary subintervals of relative order n have length ≈ e^{-2nL}|I|,
  total mass ≥ K|I|/√n") — which exists to let n(s) grow logarithmically =
  polynomial time.
  **Efficiency-free substitute (ours)**: E[log qₙ | cylinder] ≤ Cn
  elementarily (log qₙ ≤ Σ log(aᵢ+1), single-digit conditional law within
  factor 2 of stationary by Lemma 3, Σ log(k+1)/k² < ∞), so by Markov ≥ half
  of |I| lies in subintervals with |J|/|I| ≥ e^{-C'n}; the upper bound
  |J|/|I| ≤ 2φ^{-2(n-1)} is free (Fibonacci ≤ qₙ).  Worse constants, no
  complexity claim, correctness intact.
- **Lemma 6** (Kifer–Peres–Weiss 2001, *A dimension gap for continued
  fractions with independent digits*, Israel J. Math 124, Lemma 3.1 +
  Remark 5.1, here conditioned on a cylinder via Lemma 3):
  Leb{x ∈ I_a : CF-block-v frequency over next n deviates by δ}
  ≤ 6M e^{-δ²n/2M} |I_a|, M = ⌈k − log(δ²/(2 log 2))⌉.
  **This is the ONE genuinely deep ingredient.**  Note we don't need the
  exponential rate: the construction needs only per-stage bad-measure < ¼,
  so ANY summable correlation decay for cylinder indicators + Chebyshev
  suffices.  Routes, in preference order: (i) read KPW's actual proof of
  Lemma 3.1 before deciding — it may be short (⚠️ unread as of 2026-08-23);
  (ii) formalize Kuzmin's theorem (Khinchin's book ch. III, elementary,
  e^{-c√m} decay — summable) — which IS Track B's Gauss–Kuzmin headline, so
  this route plants that flag as a lemma; (iii) vendor/adapt
  ronut01/erdos1002-lean's BV Lasota–Yorke + mixing (exists in Lean today,
  Apache 2.0, mathlib v4.27 vs our v4.33 — port cost + statement-shape risk).

## What we deliberately drop

The whole of §2.3 (complexity), Lemma 4/5 as stated, and the "leftmost
refinement is findable by inspecting O(s^{2L}) endpoints" machinery.  Our x
stays computable-in-principle (a definable recursion choosing e.g. the least
good refinement), which is all "a number in hand" needs.

## Khinchin graft (not in the paper — apparently new)

Add to Def 11's refinement requirement: all new CF digits ≤ D_t with D_t → ∞
slowly, plus block-frequency accuracy for digits ≤ D_t.  Capped stages keep
≥ half the good measure for D_t large (same Chebyshev stage bound), the cap
schedule gives uniform integrability of log a, and geometric mean → K₀ follows
from digit frequencies + caps.  ~90% this works as stated; the cap/bias
bookkeeping is the part to be careful with.
