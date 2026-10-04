/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorLiouvilleAll

/-!
# A computable point of the Cantor set with exact irrationality exponent `μ₀`, normal to every base prime to 3

**Source and wording.**  Y. Bugeaud, *Distribution modulo one and Diophantine approximation*,
Cambridge Tracts in Math. 193 (2012).
* p. 219 (before Problem 10.37): "There exist Liouville numbers in the middle third Cantor set K
  and there are Liouville numbers which are normal to base 2.  Furthermore, K contains numbers
  normal to base 2.  But we do not know whether there are real numbers with all these three
  properties."  p. 220: "The above problem concerns the intersection of three sets, any two of
  them having non-empty intersection."
* p. 158, Theorem 7.21 (Bugeaud, Math. Ann. 341 (2008) 677–684): "Let μ ≥ 2.  The middle third
  Cantor set K contains uncountably many elements whose irrationality exponent is equal to μ."

Problem 10.37 is the exponent-`∞` corner of the triple (`K`, exponent, `N(2)`), proved in this
repo as `CantorLiouvilleAll.exists_computable_liouville_mem_cantorSet_normalProfile`.  This file
freezes the **finite-exponent** triple: for rational `μ₀ > 2 + log₂ 3 ≈ 3.585`, a computable
`x ∈ K` with irrationality exponent exactly `μ₀`, normal to every base `b ≥ 2` with `3 ∤ b`
(`exists_computable_mem_cantorSet_irrExponent_normal`).  Not found in the literature (audit
`docs/CANTOR-EXACT-EXPONENT-AUDIT-2026-10-04.md`).  The range `2 < μ₀ ≤ 2 + log₂ 3` is the
separate file `CantorExactExponentStretch.lean`.

## Construction

The `CantorLiouville` coin point `pt free ω` with forced ternary zero-runs `[a k, ⌈μ₀ a k⌉)`,
`a 0 = 4`, `a (k+1) = (k+2) ⌈μ₀ a k⌉` (`expRunStart`, `expRunEnd`, `expFree`).  So the runs have
fixed relative length `μ₀ − 1` instead of the Liouville runs' growing one.

## Mechanism (English; the leaves below carry it)

1. **Lower bound** `μ(x) ≥ μ₀` (`liouvilleWith_cantorExpReal`): truncating before run `k` gives
   `|x − P/3^{a}| ≤ 3^{−⌈μ₀ a⌉}`, as in 10.37.
2. **Upper bound** `μ(x) ≤ μ₀` a.s. (`ae_not_liouvilleWith`, the crux).  Fix `τ > μ₀`, `q ≈ 3ᵐ`.
   * *Triangle range* `a/(τ−1) ≲ m ≲ (μ₀−1)a` around each run start `a`
     (`abs_sub_ge_of_near`): any `p/q ≠ P/3^a` has `|x − p/q| ≥ 1/(2q3^a) ≥ q^{−τ}`.
   * *Borel–Cantelli range* `(μ₀−1)a_k ≲ m ≲ a_{k+1}/(τ−1)`: the ball `B(p/q, q^{−τ})` has
     coin mass `≤ 2·2^{−F(τm)}` (`coins_ball_le`), and only `≤ 4·2^{F(m)}` numerators `p` reach
     the support (`card_near_le`), `F = freeCount`.  So the `q ≈ 3ᵐ` block costs
     `≲ 3ᵐ·2^{−(F(τm) − F(m))}`.  The free count in the window `(m, τm]` is
     `≥ (μ₀ − 2)m − C` on this range (`window_freeCount_ge`; worst cases: the window
     entering run `k+1` at `m = a_{k+1}/(τ−1)`, and starting inside run `k` at `m = (μ₀−1)a_k`).
     The block costs are summable iff `3·2^{−(μ₀−2)} < 1`, i.e. `μ₀ > 2 + log₂ 3`
     (`summable_bc_of_threshold_lt`).  **This is where the threshold comes from.**
3. **Normality** to every `b` with `3 ∤ b`: `CantorLiouvilleAll.secondMoment_le_b` is stated for
   every free set; the runs leave a linear free count (`le_freeCount_exp`), far more than the
   `M / log M` the Liouville runs left.
4. **Computability**: the upper-bound events become primitive-recursive prefix tests with mass
   `≤ 1/(j+1)²` (`exists_exponent_tests`), fed to the `bad'` slot of the family derandomizer
   (`exists_computable_normal_avoid`).

## Difficulty check

* **Proved implications:** the normality legs and the derandomizer exist for the 10.37 schedule;
  the 10.37 lower-bound argument transfers.
* **Unproved premise:** the Borel–Cantelli upper bound on the exponent (step 2), new
  infrastructure (rational counting near the support, ball masses, the window count).
* **Mechanism and its refusal below the threshold:** the count `4·2^{F(m)}` numerators per `q`
  is the trivial one (every depth-`m` cylinder holds `O(1)` fractions `p/q`).  At
  `m ≈ a_{k+1}/(τ−1)` the window holds only `a_{k+1} − m` free places
  (`freeCount_window_le_of_run`), so the block cost is `3ᵐ 2^{−(τ−2)m}`, which is `≥ 1` when
  `τ − 2 ≤ log₂ 3`.  Kernel controls on the concrete schedules: `μ₀ = 3` at `k = 1`
  (`bcTerm_red_mu_three`, cost `> 1`) and `μ₀ = 4` (`bcTerm_green_mu_four`, cost `< 1`).
  Below the threshold one needs a better count of rationals near `K`
  (Broderick–Fishman–Reich, Bugeaud–Durand conjecture (18), He–Liao 2602.01307), see the
  stretch file.
* **Known-false siblings:** base 3 (`not_isNormal_three_cantorExpReal`, every `ω`).  Bases
  `3 ∣ b`: the runs force non-normality only while `2 log₃ b < μ₀`
  (`not_isNormal_of_three_dvd_of_small`); for larger `b` with `3 ∣ b` the profile is **not
  claimed** (Cassels makes `μ_K`-a.e. point normal to base 6, and runs of bounded relative length
  need not spoil base `3·2¹⁰`).  So, unlike 10.37, the headline does not assert `↔ ¬ 3 ∣ b`.

## Confidence

Headline 65% (mathematics about 85%, the rest is Lean cost of the counting and of the prefix
tests).  No cited result is used by the headline or its leaves.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.CantorExactExponent

open CantorLiouville Derandomize

/-! ## Vocabulary -/

/-- **Exact irrationality exponent** in Mathlib's `LiouvilleWith` vocabulary: `x` is
`p`-approximable for every `p < μ₀` and for no `p > μ₀`.  Faithful to the usual
`μ(x) = sup {μ : 0 < |x − p/q| < q^{−μ} for infinitely many p/q}`: the constant `C` inside
`LiouvilleWith` does not change the supremum. -/
def HasIrrExponent (x μ₀ : ℝ) : Prop :=
  (∀ p < μ₀, LiouvilleWith p x) ∧ ∀ p > μ₀, ¬ LiouvilleWith p x

/-- The threshold `2 + log₂ 3 ≈ 3.585` of the trivial rational count. -/
noncomputable def threshold : ℝ := 2 + Real.logb 2 3

theorem one_lt_threshold : 1 < threshold := by
  have : 0 < Real.logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)
  unfold threshold; linarith

/-! ## The schedule -/

/-- End of the run starting at `a`: `⌈μ₀ a⌉`. -/
def expRunEnd (μ₀ : ℚ) (a : ℕ) : ℕ := ⌈μ₀ * a⌉₊

/-- Run starts: `a 0 = 4`, `a (k+1) = (k+2) ⌈μ₀ a k⌉`. -/
def expRunStart (μ₀ : ℚ) : ℕ → ℕ
  | 0 => 4
  | k + 1 => (k + 2) * expRunEnd μ₀ (expRunStart μ₀ k)

/-- Position `i` is forced to `0` iff it lies in a run `[a k, ⌈μ₀ a k⌉)`. -/
def expForced (μ₀ : ℚ) (i : ℕ) : Bool :=
  (List.range (i + 1)).any fun k =>
    decide (expRunStart μ₀ k ≤ i) && decide (i < expRunEnd μ₀ (expRunStart μ₀ k))

/-- Free positions carry a fair `{0, 2}` digit. -/
def expFree (μ₀ : ℚ) (i : ℕ) : Bool := !expForced μ₀ i

/-- The point coded by coins `ω`. -/
noncomputable def cantorExpReal (μ₀ : ℚ) (ω : ℕ → Bool) : ℝ := pt (expFree μ₀) ω

/-- Non-vacuity anchors for `μ₀ = 4`: runs `[4, 16)`, `[32, 128)`, `[384, 1536)`. -/
theorem expRun_anchor_four :
    expRunStart 4 1 = 32 ∧ expRunStart 4 2 = 384 ∧ expRunEnd 4 384 = 1536 ∧
      expForced 4 3 = false ∧ expForced 4 4 = true ∧ expForced 4 15 = true ∧
      expForced 4 16 = false ∧ expForced 4 32 = true ∧ expForced 4 128 = false := by
  decide +kernel

theorem mem_cantorSet (μ₀ : ℚ) (ω : ℕ → Bool) : cantorExpReal μ₀ ω ∈ cantorSet :=
  pt_mem_cantorSet _ _

/-- Forced positions recur (each run start is forced).  Confidence 95%.

English proof.  `k < expRunStart μ₀ k` (induction; the factor `k+2` and `⌈μ₀ a⌉ ≥ a`), and
`expRunStart μ₀ k < ⌈μ₀ · expRunStart μ₀ k⌉` as `μ₀ > 1` and `a ≥ 4`, so `i = expRunStart μ₀ N`
is forced, with `N ≤ i`. -/
theorem expForced_recur (μ₀ : ℚ) (hμ : 1 < μ₀) (N : ℕ) :
    ∃ i, N ≤ i ∧ expFree μ₀ i = false := by
  sorry

/-- **Base 3 fails, for every `ω`** (wiring from `CantorLiouville.not_isNormal_three_pt`). -/
theorem not_isNormal_three_cantorExpReal (μ₀ : ℚ) (hμ : 1 < μ₀) (ω : ℕ → Bool) :
    ¬ IsNormal 3 (cantorExpReal μ₀ ω) :=
  not_isNormal_three_pt _ ω (expForced_recur μ₀ hμ)

/-! ## Lower bound on the exponent -/

/-- **Lower bound: `x` is `μ₀`-approximable.**  Confidence 90%.

English proof.  Let `a = expRunStart μ₀ k`, `E = ⌈μ₀ a⌉`, `P = Σ_{i<a} d_i 3^{a−1−i}`.  Digits
in `[a, E)` are `0`, so `0 ≤ x − P/3^a ≤ Σ_{i ≥ E} 2·3^{−(i+1)} = 3^{−E} ≤ (3^a)^{−μ₀}`.  If some
free digit after `E` is `2` (hypothesis, applied past `E`), then `x ≠ P/3^a` (ternary
expansions with digits in `{0,2}` are unique).  The denominators `3^a → ∞`, so
`LiouvilleWith μ₀ x` with `C = 1`. -/
theorem liouvilleWith_cantorExpReal (μ₀ : ℚ) (hμ : 1 < μ₀) (ω : ℕ → Bool)
    (hf : ∀ N, ∃ i, N ≤ i ∧ expFree μ₀ i = true ∧ ω i = true) :
    LiouvilleWith μ₀ (cantorExpReal μ₀ ω) := by
  sorry

/-- Almost surely free `2`-digits recur.  Confidence 95%.

English proof.  As `CantorLiouville.ae_frequently_free`: the free places `[⌈μ₀ a k⌉, a (k+1))`
form infinitely many disjoint nonempty blocks, so by Borel–Cantelli (or independence) a.s.
infinitely many carry a coin `true`. -/
theorem ae_frequently_two (μ₀ : ℚ) (hμ : 1 < μ₀) :
    ∀ᵐ ω ∂coins, ∀ N, ∃ i, N ≤ i ∧ expFree μ₀ i = true ∧ ω i = true := by
  sorry

/-! ## Upper bound on the exponent: the leaves -/

/-- **Triangle inequality at a forced approximation.**  Confidence 95%.

English proof.  `p/q − P/3^a = (p 3^a − P q)/(q 3^a)` with a nonzero integer numerator, so
`|p/q − P/3^a| ≥ 1/(q 3^a)`, and `|x − p/q| ≥ 1/(q 3^a) − 3^{−E} ≥ 1/(2 q 3^a)` since
`2 q 3^a ≤ 3^E`. -/
theorem abs_sub_ge_of_near (x : ℝ) (P a E q : ℕ) (p : ℤ) (hq : 0 < q)
    (hx : |x - P / 3 ^ a| ≤ 1 / 3 ^ E) (hne : (p : ℝ) / q ≠ P / 3 ^ a)
    (hqE : 2 * q * 3 ^ a ≤ 3 ^ E) :
    1 / (2 * (q : ℝ) * 3 ^ a) ≤ |x - p / q| := by
  sorry

/-- **Ball mass (Frostman bound for the coin point).**  Confidence 90%.

English proof.  The depth-`n` cylinders of the point (fixing the free coins below `n`) are
intervals `[P/3ⁿ, P/3ⁿ + 3^{−n}]`, `P` with ternary digits in `{0,2}`; two distinct ones are
separated by a gap `≥ 3^{−n}`.  An open interval of length `2r ≤ 2·3^{−(n+1)} < 3^{−n}` meets at
most one of them, and each has coin mass `2^{−F(n)}` (or `0`). -/
theorem coins_ball_le (free : ℕ → Bool) (y r : ℝ) (n : ℕ) (hr : r ≤ 1 / 3 ^ (n + 1)) :
    coins.real {ω | |pt free ω - y| < r} ≤ 2 * (1 / 2 : ℝ) ^ freeCount free n := by
  sorry

open Classical in
/-- **Trivial count of numerators near the support.**  Confidence 90%.

English proof.  The support lies in the `≤ 2^{F(m)}` depth-`m` cylinders, intervals of length
`3^{−m} ≤ 1/q`.  The `r`-neighbourhood (`r ≤ 1/q`) of one has length `≤ 3/q`, so holds at most
`4` fractions `p/q`. -/
theorem card_near_le (free : ℕ → Bool) (q m : ℕ) (hq : 0 < q) (hqm : q ≤ 3 ^ m) (r : ℝ)
    (hr : r ≤ 1 / q) :
    ((Finset.range (q + 1)).filter fun p : ℕ => ∃ ω, |pt free ω - p / q| < r).card ≤
      4 * 2 ^ freeCount free m := by
  sorry

/-- **Window free count on the Borel–Cantelli range.**  Confidence 85%.

English proof.  Write `a = a_k`, `E = ⌈μ₀ a⌉`, `a' = a_{k+1}`, window `W(m) = F(⌈τm⌉) − F(m)`.
On the range `E − a − 2 ≤ m`, `(τ−1)m ≤ a' + 2`:
* `m ≥ E`, `τm ≤ a'`: all free, `W ≥ (τ−1)m − 1 ≥ (μ₀−2)m − 1`;
* `m ≥ E`, `τm > a'` (window enters run `k+1`; `τm ≤ τ(a'+2)/(τ−1) < ⌈μ₀ a'⌉` up to `O(1)`
  since `τ/(τ−1) < μ₀`): `W ≥ a' − m − 1 ≥ (τ−2)m − 3 ≥ (μ₀−2)m − 3`;
* `E − a − 2 ≤ m < E` (window starts in run `k`): `W ≥ τm − E − 1`, increasing in `m` with
  slope `τ > μ₀ − 2`; at `m = (μ₀−1)a` it is `≥ μ₀(μ₀−2)a − O(1) = (μ₀−2)m + (μ₀−2)a − O(1)`.
* the finitely many `k < τ` for which a window starting in run `k` reaches run `k+1` are
  absorbed in `C`. -/
theorem window_freeCount_ge (μ₀ : ℚ) (hμ : 2 < μ₀) (τ : ℝ) (hτ : (μ₀ : ℝ) < τ) :
    ∃ C : ℝ, ∀ k m : ℕ, expRunEnd μ₀ (expRunStart μ₀ k) ≤ m + expRunStart μ₀ k + 2 →
      (τ - 1) * m ≤ expRunStart μ₀ (k + 1) + 2 →
      ((μ₀ : ℝ) - 2) * m ≤
        (freeCount (expFree μ₀) ⌈τ * m⌉₊ : ℝ) - freeCount (expFree μ₀) m + C := by
  sorry

/-- **Where the threshold enters.**  The trivial-count block costs `3ᵐ 2^{−(μ₀−2)m}` are summable
exactly above `2 + log₂ 3`.  Confidence 95%.

English proof.  `3 · 2^{−(μ₀−2)} < 1 ⇔ μ₀ − 2 > log₂ 3`; geometric series. -/
theorem summable_bc_of_threshold_lt (μ₀ : ℝ) (hμ : threshold < μ₀) :
    Summable fun m : ℕ => (3 : ℝ) ^ m * (2 : ℝ) ^ (-((μ₀ - 2) * m)) := by
  sorry

/-! ## The sibling the mechanism must refuse -/

/-- **Structural cap at the entry of a run.**  If the window `(m, n]` reaches into the run
`[a', E')`, its free places are at most `a' − m`.  Confidence 95%.

English proof.  Places in `[a', n)` are forced; `freeCount` counts places `< n`. -/
theorem freeCount_window_le_of_run (μ₀ : ℚ) (k m n : ℕ) (hm : m ≤ expRunStart μ₀ k)
    (hn : n ≤ expRunEnd μ₀ (expRunStart μ₀ k)) :
    freeCount (expFree μ₀) n - freeCount (expFree μ₀) m ≤ expRunStart μ₀ k - m := by
  sorry

/-- **Red control (below the threshold).**  `μ₀ = τ = 3 < 2 + log₂ 3`: run `2` starts at
`a₂ = 216`, and at `m = a₂/(τ−1) = 108` the window `[108, 324)` holds `108` free places, so the
trivial block cost `3^{108} · 2^{−108}` exceeds `1`: the Borel–Cantelli sum of this method
diverges.  (Kernel.) -/
theorem bcTerm_red_mu_three :
    expRunStart 3 2 = 216 ∧
      freeCount (expFree 3) 324 - freeCount (expFree 3) 108 = 108 ∧
      2 ^ (freeCount (expFree 3) 324 - freeCount (expFree 3) 108) < 3 ^ 108 := by
  decide +kernel

/-- **Green control (above the threshold).**  `μ₀ = τ = 4`: `a₂ = 384`, at `m = 128` the window
`[128, 512)` holds `256` free places and `2^{256} > 3^{128}`: the block cost is below `1`.
(Kernel.) -/
theorem bcTerm_green_mu_four :
    expRunStart 4 2 = 384 ∧
      freeCount (expFree 4) 512 - freeCount (expFree 4) 128 = 256 ∧
      3 ^ 128 < 2 ^ (freeCount (expFree 4) 512 - freeCount (expFree 4) 128) := by
  decide +kernel

/-! ## Upper bound: assembly -/

/-- **The crux: the exponent is at most `μ₀`, almost surely.**  Confidence 80%.

English proof.  Fix `τ > μ₀`.  It suffices that a.s. only finitely many `p/q` satisfy
`|x − p/q| < q^{−τ'}` for some fixed `τ' ∈ (μ₀, τ)` (then `C/q^τ < q^{−τ'}` eventually).
Split `q ≈ 3ᵐ` by the run index `k` with `⌈μ₀ a_k⌉ − a_k − 2 ≤ m ≤ (a_{k+1}+2)/(τ'−1)` (BC range)
or `a_{k}/(τ'−1) − 1 ≤ m ≤ ⌈μ₀ a_k⌉ − a_k − 2` (triangle range).
* Triangle range: `abs_sub_ge_of_near` with `P/3^{a_k}` disposes of every `p/q ≠ P/3^{a_k}`;
  the rational `P/3^{a_k}` itself is excluded once a free `2` occurs in `[E_k, τ' a_k − 1)`,
  which fails with probability `2^{−(τ'−μ₀)a_k + O(1)}`, summable.
* BC range: by `card_near_le` (depth `m+1`) and `coins_ball_le` (depth `⌈τ'm⌉ − 1`) the
  probability of a hit with `q ∈ [3ᵐ, 3^{m+1})` is `≤ 2·3ᵐ · 4·2^{F(m+1)} · 2·2^{−F(⌈τ'm⌉−1)}
  ≤ 64 · 3ᵐ 2^{−W(m)}`, `≤ 64·2^C·3ᵐ 2^{−(μ₀−2)m}` by `window_freeCount_ge`; summable over `m` by
  `summable_bc_of_threshold_lt`.
Borel–Cantelli (`measure_limsup_atTop_eq_zero`) gives finitely many hits a.s. -/
theorem ae_not_liouvilleWith (μ₀ : ℚ) (hμ : threshold < μ₀) (τ : ℝ) (hτ : (μ₀ : ℝ) < τ) :
    ∀ᵐ ω ∂coins, ¬ LiouvilleWith τ (cantorExpReal μ₀ ω) := by
  sorry

/-- **Exact exponent, a.e.**  Wiring (proved): lower bound from `liouvilleWith_cantorExpReal`
plus `ae_frequently_two`; upper bound from `ae_not_liouvilleWith` along `μ₀ + 1/(n+1)`. -/
theorem ae_hasIrrExponent (μ₀ : ℚ) (hμ : threshold < μ₀) :
    ∀ᵐ ω ∂coins, HasIrrExponent (cantorExpReal μ₀ ω) μ₀ := by
  have h1 : (1 : ℚ) < μ₀ := by
    have := one_lt_threshold
    exact_mod_cast this.trans hμ
  have hup : ∀ᵐ ω ∂coins, ∀ n : ℕ,
      ¬ LiouvilleWith ((μ₀ : ℝ) + 1 / ((n : ℝ) + 1)) (cantorExpReal μ₀ ω) := by
    rw [ae_all_iff]
    intro n
    exact ae_not_liouvilleWith μ₀ hμ _ (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                                           linarith)
  filter_upwards [hup, ae_frequently_two μ₀ h1] with ω hω hf
  refine ⟨fun p hp => (liouvilleWith_cantorExpReal μ₀ h1 ω hf).mono hp.le, fun p hp hL => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hp)
  exact hω n (hL.mono (by linarith))

/-! ## Normality -/

/-- **Linear free count.**  Confidence 90%.

English proof.  Below `M`, the forced places lie in runs `[a_j, E_j)` with `E_j ≤ μ₀ a_j + 1`
and `a_{j+1} ≥ (j+2) E_j`; the free places `[E_{j}, a_{j+1})` before the last run reached
outnumber all earlier forced places by the factor `j+1`, so `F(M) ≥ M/(2μ₀ + 4) − 4`. -/
theorem le_freeCount_exp (μ₀ : ℚ) (hμ : 1 < μ₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, c * M ≤ freeCount (expFree μ₀) M + 4 := by
  sorry

/-- **Normal to every base prime to 3, a.e.**  Confidence 90%.

English proof.  `CantorLiouvilleAll.ae_isNormal_of_coprime_three` verbatim with `isFree`
replaced by `expFree μ₀`: `secondMoment_le_b (expFree μ₀)` with the linear free count of
`le_freeCount_exp` (stronger than `CantorLiouville.le_freeCount`) makes the bound summable along
`CantorLiouville.sched`, and `ae_isNormal_of_secondMoment` concludes. -/
theorem ae_isNormal_of_coprime_three (μ₀ : ℚ) (hμ : 1 < μ₀) :
    ∀ᵐ ω ∂coins, ∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → IsNormal b (cantorExpReal μ₀ ω) := by
  sorry

/-- **Existence form.**  Wiring (proved). -/
theorem exists_mem_cantorSet_irrExponent_normal (μ₀ : ℚ) (hμ : threshold < μ₀) :
    ∃ x : ℝ, x ∈ cantorSet ∧ HasIrrExponent x μ₀ ∧
      (∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → IsNormal b x) ∧ ¬ IsNormal 3 x := by
  have h1 : (1 : ℚ) < μ₀ := by
    have := one_lt_threshold
    exact_mod_cast this.trans hμ
  have : NeZero coins := by unfold coins; infer_instance
  obtain ⟨ω, he, hn⟩ := ((ae_hasIrrExponent μ₀ hμ).and (ae_isNormal_of_coprime_three μ₀ h1)).exists
  exact ⟨_, mem_cantorSet μ₀ ω, he, hn, not_isNormal_three_cantorExpReal μ₀ h1 ω⟩

/-- **Bases divisible by 3 with short logarithm fail, for every `ω`.**  Confidence 80%.

English proof.  Along run `k` (`a = a_k`, `E = ⌈μ₀ a⌉`), for `j` with `a ≤ v₃(b)·j` and
`b^{j+1} ≤ 3^E`, `bʲ P/3^a ∈ ℤ` and `{bʲ x} < 1/b` (`CantorLiouvilleAll.fract_lt_of_mem_run`'s
argument).  These `j` fill a fraction `≥ 1 − log₃ b / μ₀ − o(1) > 1/2 ≥ 1/b` of
`[0, E / log₃ b)`, contradicting Wall's criterion.  For `3 ∣ b` with `2 log₃ b ≥ μ₀` nothing is
claimed. -/
theorem not_isNormal_of_three_dvd_of_small (μ₀ : ℚ) (hμ : 1 < μ₀) (ω : ℕ → Bool) {b : ℕ}
    (hb : 2 ≤ b) (h3 : 3 ∣ b) (hsmall : 2 * Real.logb 3 b < μ₀) :
    ¬ IsNormal b (cantorExpReal μ₀ ω) := by
  sorry

/-! ## Computable form -/

/-- **The exponent tests.**  Confidence 70%.

English proof.  For rational `τ_n = μ₀ + 1/(n+1)` (rational, so `|x − p/q| < q^{−τ_n}` is
decided by integer powers on a prefix over-approximation of `x`), the events of
`ae_not_liouvilleWith` (BC blocks `m`, and the "no free `2` in `[E_k, τ a_k)`" events) are
decided by prefixes of length `≈ τ_n m + 2`.  Index them by `j` along a primitive-recursive
enumeration of `(n, m)` with the tails starting late enough that each block's mass is
`≤ 1/(j+1)²` (geometric decay from `summable_bc_of_threshold_lt`, with an explicit rational
base `3·2^{−(μ₀−2)} < 1` bounded through `μ₀ − 2 > 1.585 + ε`).  Avoiding all tests from some
stage on gives finitely many hits for every `τ_n`, hence the upper bound, and the free-`2`
recurrence, hence the lower bound. -/
theorem exists_exponent_tests (μ₀ : ℚ) (hμ : threshold < μ₀) :
    ∃ (bad' : ℕ → List Bool → Bool) (d' : ℕ → ℕ), Primrec₂ bad' ∧ Primrec d' ∧
      (∀ j, coins.real {ω | bad' j (pre ω (d' j)) = true} ≤ 1 / ((j : ℝ) + 1) ^ 2) ∧
      ∀ e : ℕ → Bool, (∃ j₁, ∀ j, j₁ ≤ j → bad' j (pre e (d' j)) = false) →
        HasIrrExponent (cantorExpReal μ₀ e) μ₀ := by
  sorry

/-- **Family derandomization for the exponent schedule.**  Confidence 85%.

English proof.  `CantorLiouvilleAll.exists_computable_normal_sched_family` with the
approximants of `CantorLiouville.clΨ`/`clA` built on `expFree μ₀` (primitive recursive as
`expRunStart` is, `μ₀` rational), `κ b = 16 b⁶`, `W` from `secondMoment_le_b (expFree μ₀)`, and
the schedule `clNs`/`clNr` (the linear free count of `le_freeCount_exp` beats the `√M` needed by
`cl_ev`). -/
theorem exists_computable_normal_avoid (μ₀ : ℚ) (hμ : 1 < μ₀)
    (bad' : ℕ → List Bool → Bool) (hbad' : Primrec₂ bad') (d' : ℕ → ℕ) (hd' : Primrec d')
    (hmass : ∀ j, coins.real {ω | bad' j (pre ω (d' j)) = true} ≤ 1 / ((j : ℝ) + 1) ^ 2) :
    ∃ e : ℕ → Bool, Computable e ∧
      (∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → IsNormal b (cantorExpReal μ₀ e)) ∧
      ∃ j₁, ∀ j, j₁ ≤ j → bad' j (pre e (d' j)) = false := by
  sorry

/-- **Headline.**  For every rational `μ₀ > 2 + log₂ 3 ≈ 3.585` there is a computable coin
sequence `e` such that `x = cantorExpReal μ₀ e` lies in the middle-third Cantor set, has
irrationality exponent exactly `μ₀`, is normal to every base `b ≥ 2` with `3 ∤ b`, and is not
normal to base 3.  The finite-exponent version of Bugeaud's three-set question (p. 219) between
Theorem 7.21 and Problem 10.37.  Wiring (proved from the leaves `exists_exponent_tests`,
`exists_computable_normal_avoid`, `expForced_recur`); overall confidence 65%. -/
theorem exists_computable_mem_cantorSet_irrExponent_normal (μ₀ : ℚ) (hμ : threshold < μ₀) :
    ∃ e : ℕ → Bool, Computable e ∧ cantorExpReal μ₀ e ∈ cantorSet ∧
      HasIrrExponent (cantorExpReal μ₀ e) μ₀ ∧
      (∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → IsNormal b (cantorExpReal μ₀ e)) ∧
      ¬ IsNormal 3 (cantorExpReal μ₀ e) := by
  have h1 : (1 : ℚ) < μ₀ := by
    have := one_lt_threshold
    exact_mod_cast this.trans hμ
  obtain ⟨bad', d', hbad', hd', hmass, hexp⟩ := exists_exponent_tests μ₀ hμ
  obtain ⟨e, hce, hn, j₁, hj⟩ := exists_computable_normal_avoid μ₀ h1 bad' hbad' d' hd' hmass
  exact ⟨e, hce, mem_cantorSet μ₀ e, hexp e ⟨j₁, hj⟩, hn,
    not_isNormal_three_cantorExpReal μ₀ h1 e⟩

end NormalNumbers.CantorExactExponent
