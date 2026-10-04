/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorLiouvilleAll
import NormalNumbers.CantorExpGeneric

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

/-! ## Schedule facts -/

section Schedule

variable {μ₀ : ℚ}

theorem expRunEnd_ge_q (μ₀ : ℚ) (a : ℕ) : μ₀ * a ≤ (expRunEnd μ₀ a : ℚ) := Nat.le_ceil _

theorem expRunEnd_lt_q (hμ : 1 < μ₀) (a : ℕ) : (expRunEnd μ₀ a : ℚ) < μ₀ * a + 1 :=
  Nat.ceil_lt_add_one (by positivity)

theorem expRunEnd_ge_r (μ₀ : ℚ) (a : ℕ) : (μ₀ : ℝ) * a ≤ (expRunEnd μ₀ a : ℝ) := by
  have := expRunEnd_ge_q μ₀ a; exact_mod_cast this

theorem expRunEnd_lt_r (hμ : 1 < μ₀) (a : ℕ) : (expRunEnd μ₀ a : ℝ) < (μ₀ : ℝ) * a + 1 := by
  have := expRunEnd_lt_q hμ a; exact_mod_cast this

theorem le_expRunEnd (hμ : 1 < μ₀) (a : ℕ) : a ≤ expRunEnd μ₀ a := by
  have h := expRunEnd_ge_q μ₀ a
  have : (a : ℚ) ≤ expRunEnd μ₀ a := by nlinarith [(Nat.cast_nonneg a : (0:ℚ) ≤ a)]
  exact_mod_cast this

theorem lt_expRunEnd (hμ : 1 < μ₀) {a : ℕ} (ha : 1 ≤ a) : a < expRunEnd μ₀ a := by
  have h := expRunEnd_ge_q μ₀ a
  have ha' : (1 : ℚ) ≤ a := by exact_mod_cast ha
  have : (a : ℚ) < expRunEnd μ₀ a := by nlinarith
  exact_mod_cast this

theorem expRunStart_succ (μ₀ : ℚ) (k : ℕ) :
    expRunStart μ₀ (k + 1) = (k + 2) * expRunEnd μ₀ (expRunStart μ₀ k) := rfl

theorem four_le_expRunStart (hμ : 1 < μ₀) (k : ℕ) : 4 ≤ expRunStart μ₀ k := by
  induction k with
  | zero => simp [expRunStart]
  | succ k ih =>
    rw [expRunStart_succ]
    have := le_expRunEnd hμ (expRunStart μ₀ k)
    nlinarith

theorem start_lt_end (hμ : 1 < μ₀) (k : ℕ) :
    expRunStart μ₀ k < expRunEnd μ₀ (expRunStart μ₀ k) :=
  lt_expRunEnd hμ (by have := four_le_expRunStart hμ k; omega)

theorem end_lt_start_succ (hμ : 1 < μ₀) (k : ℕ) :
    expRunEnd μ₀ (expRunStart μ₀ k) < expRunStart μ₀ (k + 1) := by
  rw [expRunStart_succ]
  have := start_lt_end hμ k
  nlinarith

theorem two_mul_end_le_start_succ (μ₀ : ℚ) (k : ℕ) :
    2 * expRunEnd μ₀ (expRunStart μ₀ k) ≤ expRunStart μ₀ (k + 1) := by
  rw [expRunStart_succ]; exact Nat.mul_le_mul_right _ (by omega)

theorem lt_expRunStart (hμ : 1 < μ₀) (k : ℕ) : k < expRunStart μ₀ k := by
  induction k with
  | zero => simp [expRunStart]
  | succ k ih =>
    have := end_lt_start_succ hμ k
    have := start_lt_end hμ k
    omega

theorem expRunStart_strictMono (hμ : 1 < μ₀) : StrictMono (expRunStart μ₀) :=
  strictMono_nat_of_lt_succ fun k => (start_lt_end hμ k).trans (end_lt_start_succ hμ k)

theorem expRunEnd_strictMono (hμ : 1 < μ₀) :
    StrictMono fun k => expRunEnd μ₀ (expRunStart μ₀ k) :=
  strictMono_nat_of_lt_succ fun k => (end_lt_start_succ hμ k).trans (start_lt_end hμ (k + 1))

theorem expForced_iff (hμ : 1 < μ₀) (i : ℕ) :
    expForced μ₀ i = true ↔
      ∃ k, expRunStart μ₀ k ≤ i ∧ i < expRunEnd μ₀ (expRunStart μ₀ k) := by
  unfold expForced
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨k, -, h⟩; exact ⟨k, h⟩
  · rintro ⟨k, h⟩
    exact ⟨k, by have := lt_expRunStart hμ k; omega, h⟩

theorem expFree_of_run (hμ : 1 < μ₀) {k i : ℕ} (h1 : expRunStart μ₀ k ≤ i)
    (h2 : i < expRunEnd μ₀ (expRunStart μ₀ k)) : expFree μ₀ i = false := by
  unfold expFree; rw [(expForced_iff hμ i).2 ⟨k, h1, h2⟩]; rfl

theorem expFree_of_gap (hμ : 1 < μ₀) {k i : ℕ} (h1 : expRunEnd μ₀ (expRunStart μ₀ k) ≤ i)
    (h2 : i < expRunStart μ₀ (k + 1)) : expFree μ₀ i = true := by
  unfold expFree
  rw [Bool.not_eq_true']
  by_contra hc
  rw [Bool.not_eq_false, expForced_iff hμ] at hc
  obtain ⟨j, hj1, hj2⟩ := hc
  rcases le_or_gt j k with hjk | hjk
  · have := (expRunEnd_strictMono hμ).monotone hjk
    omega
  · have := (expRunStart_strictMono hμ).monotone (show k + 1 ≤ j by omega)
    omega

theorem expFree_of_lt_four (hμ : 1 < μ₀) {i : ℕ} (h : i < 4) : expFree μ₀ i = true := by
  unfold expFree
  rw [Bool.not_eq_true']
  by_contra hc
  rw [Bool.not_eq_false, expForced_iff hμ] at hc
  obtain ⟨j, hj1, -⟩ := hc
  have := four_le_expRunStart hμ j
  omega

end Schedule

/-- Forced positions recur (each run start is forced).  Confidence 95%.

English proof.  `k < expRunStart μ₀ k` (induction; the factor `k+2` and `⌈μ₀ a⌉ ≥ a`), and
`expRunStart μ₀ k < ⌈μ₀ · expRunStart μ₀ k⌉` as `μ₀ > 1` and `a ≥ 4`, so `i = expRunStart μ₀ N`
is forced, with `N ≤ i`. -/
theorem expForced_recur (μ₀ : ℚ) (hμ : 1 < μ₀) (N : ℕ) :
    ∃ i, N ≤ i ∧ expFree μ₀ i = false :=
  ⟨expRunStart μ₀ N, (lt_expRunStart hμ N).le, expFree_of_run hμ le_rfl (start_lt_end hμ N)⟩

/-- **Base 3 fails, for every `ω`** (wiring from `CantorLiouville.not_isNormal_three_pt`). -/
theorem not_isNormal_three_cantorExpReal (μ₀ : ℚ) (hμ : 1 < μ₀) (ω : ℕ → Bool) :
    ¬ IsNormal 3 (cantorExpReal μ₀ ω) :=
  not_isNormal_three_pt _ ω (expForced_recur μ₀ hμ)

/-! ## Lower bound on the exponent -/

/-! ## The truncations `P_k / 3^{a_k}` -/

section Trunc

open CantorExpGeneric

variable {μ₀ : ℚ}

theorem ptDigit_run_zero (hμ : 1 < μ₀) (ω : ℕ → Bool) (k : ℕ) :
    ∀ i, expRunStart μ₀ k ≤ i → i < expRunEnd μ₀ (expRunStart μ₀ k) →
      ptDigit (expFree μ₀) ω i = 0 := fun i h1 h2 => by
  simp [ptDigit, expFree_of_run hμ h1 h2]

/-- `x = P/3^a + tail beyond E` along run `k`. -/
theorem cantorExpReal_trunc (hμ : 1 < μ₀) (ω : ℕ → Bool) (k : ℕ) :
    cantorExpReal μ₀ ω = (hd (expFree μ₀) ω (expRunStart μ₀ k) : ℝ) / 3 ^ expRunStart μ₀ k +
      tl (expFree μ₀) ω (expRunEnd μ₀ (expRunStart μ₀ k)) := by
  set a := expRunStart μ₀ k
  set E := expRunEnd μ₀ a
  have hE := hd_zero_ext (expFree μ₀) ω a E (le_expRunEnd hμ a) (ptDigit_run_zero hμ ω k)
  rw [cantorExpReal, pt_split (expFree μ₀) ω E, hE]
  push_cast
  rw [show (3 : ℝ) ^ E = 3 ^ (E - a) * 3 ^ a by
    rw [← pow_add]; congr 1; have := le_expRunEnd hμ a; omega]
  congr 1
  field_simp

/-- Truncations that miss `x` infinitely often give `LiouvilleWith μ₀`. -/
theorem liouvilleWith_of_ne (hμ : 1 < μ₀) (ω : ℕ → Bool)
    (h : ∀ N, ∃ k, N ≤ k ∧ cantorExpReal μ₀ ω ≠
      (hd (expFree μ₀) ω (expRunStart μ₀ k) : ℝ) / 3 ^ expRunStart μ₀ k) :
    LiouvilleWith μ₀ (cantorExpReal μ₀ ω) := by
  refine ⟨2, frequently_atTop.2 fun N => ?_⟩
  obtain ⟨k, hk, hne⟩ := h N
  set a := expRunStart μ₀ k
  set E := expRunEnd μ₀ a
  refine ⟨3 ^ a, ?_, (hd (expFree μ₀) ω a : ℤ), ?_, ?_⟩
  · have := lt_expRunStart hμ k
    have := Nat.lt_pow_self (n := a) (by norm_num : 1 < 3)
    omega
  · push_cast; exact hne
  · push_cast
    rw [cantorExpReal_trunc hμ ω k, add_sub_cancel_left, abs_of_nonneg (tl_nonneg _ _ _)]
    have h1 := tl_le (expFree μ₀) ω E
    have h2 : ((3 : ℝ) ^ a) ^ (μ₀ : ℝ) ≤ 3 ^ E := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by rw [mul_comm]; exact expRunEnd_ge_r μ₀ a)
    have h3 : 1 / (3 : ℝ) ^ E < 2 / ((3 : ℝ) ^ a) ^ (μ₀ : ℝ) := by
      have hp : (0 : ℝ) < ((3 : ℝ) ^ a) ^ (μ₀ : ℝ) := by positivity
      rw [div_lt_div_iff₀ (by positivity) hp]; linarith
    linarith

end Trunc

/-- **Lower bound: `x` is `μ₀`-approximable.**  Confidence 90%.

English proof.  Let `a = expRunStart μ₀ k`, `E = ⌈μ₀ a⌉`, `P = Σ_{i<a} d_i 3^{a−1−i}`.  Digits
in `[a, E)` are `0`, so `0 ≤ x − P/3^a ≤ Σ_{i ≥ E} 2·3^{−(i+1)} = 3^{−E} ≤ (3^a)^{−μ₀}`.  If some
free digit after `E` is `2` (hypothesis, applied past `E`), then `x ≠ P/3^a` (ternary
expansions with digits in `{0,2}` are unique).  The denominators `3^a → ∞`, so
`LiouvilleWith μ₀ x` with `C = 1`. -/
theorem liouvilleWith_cantorExpReal (μ₀ : ℚ) (hμ : 1 < μ₀) (ω : ℕ → Bool)
    (hf : ∀ N, ∃ i, N ≤ i ∧ expFree μ₀ i = true ∧ ω i = true) :
    LiouvilleWith μ₀ (cantorExpReal μ₀ ω) := by
  refine liouvilleWith_of_ne hμ ω fun N => ⟨N, le_rfl, fun heq => ?_⟩
  obtain ⟨i, hi, hfi, hωi⟩ := hf (expRunEnd μ₀ (expRunStart μ₀ N))
  have h2 : ptDigit (expFree μ₀) ω i = 2 := by simp [ptDigit, hfi, hωi]
  have := CantorExpGeneric.tl_ge (expFree μ₀) ω _ i hi h2
  rw [cantorExpReal_trunc hμ ω N] at heq
  have : (0 : ℝ) < 2 / 3 ^ (i + 1) := by positivity
  linarith

/-- Almost surely free `2`-digits recur.  Confidence 95%.

English proof.  As `CantorLiouville.ae_frequently_free`: the free places `[⌈μ₀ a k⌉, a (k+1))`
form infinitely many disjoint nonempty blocks, so by Borel–Cantelli (or independence) a.s.
infinitely many carry a coin `true`. -/
theorem ae_frequently_two (μ₀ : ℚ) (hμ : 1 < μ₀) :
    ∀ᵐ ω ∂coins, ∀ N, ∃ i, N ≤ i ∧ expFree μ₀ i = true ∧ ω i = true := by
  rw [ae_all_iff]
  intro N
  set p : ℕ → ℕ := fun k => expRunEnd μ₀ (expRunStart μ₀ k)
  have hp : StrictMono p := expRunEnd_strictMono hμ
  have hpn : ∀ k, k ≤ p k := fun k => by
    have := lt_expRunStart hμ k; have := le_expRunEnd hμ (expRunStart μ₀ k); simp only [p]; omega
  have hpf : ∀ k, expFree μ₀ (p k) = true := fun k =>
    expFree_of_gap hμ le_rfl (end_lt_start_succ hμ k)
  rw [ae_iff]
  set E := {ω : ℕ → Bool | ¬∃ i, N ≤ i ∧ expFree μ₀ i = true ∧ ω i = true}
  have hle : ∀ L : ℕ, coins E ≤ (2⁻¹ : ENNReal) ^ L := by
    intro L
    set S := (Finset.Ico N (N + L)).image p
    have hsub : E ⊆ {ω | ∀ i ∈ S, ω i = (fun _ => false) i} := by
      intro ω hω i hi
      simp only [S, Finset.mem_image, Finset.mem_Ico] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      simp only [E, Set.mem_setOf_eq, not_exists, not_and] at hω
      have := hω (p k) ((hpn k).trans' hk.1) (hpf k)
      simpa using this
    refine (measure_mono hsub).trans (le_of_eq ?_)
    rw [CantorExpGeneric.coins_cyl, Finset.card_image_of_injective _ hp.injective, Nat.card_Ico]
    simp
  have ht : Tendsto (fun L : ℕ => (2⁻¹ : ENNReal) ^ L) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  exact le_antisymm (ge_of_tendsto' ht hle) bot_le

/-! ## Upper bound on the exponent: the leaves -/

/-- **Triangle inequality at a forced approximation.**  Confidence 95%.

English proof.  `p/q − P/3^a = (p 3^a − P q)/(q 3^a)` with a nonzero integer numerator, so
`|p/q − P/3^a| ≥ 1/(q 3^a)`, and `|x − p/q| ≥ 1/(q 3^a) − 3^{−E} ≥ 1/(2 q 3^a)` since
`2 q 3^a ≤ 3^E`. -/
theorem abs_sub_ge_of_near (x : ℝ) (P a E q : ℕ) (p : ℤ) (hq : 0 < q)
    (hx : |x - P / 3 ^ a| ≤ 1 / 3 ^ E) (hne : (p : ℝ) / q ≠ P / 3 ^ a)
    (hqE : 2 * q * 3 ^ a ≤ 3 ^ E) :
    1 / (2 * (q : ℝ) * 3 ^ a) ≤ |x - p / q| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h3 : (0 : ℝ) < 3 ^ a := by positivity
  set n : ℤ := p * 3 ^ a - P * q with hn
  have hn0 : n ≠ 0 := by
    intro h0
    apply hne
    have : (p : ℝ) * 3 ^ a = P * q := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h0
      simp only [hn] at this; push_cast at this; linarith
    field_simp; linarith
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
  have hdiff : (p : ℝ) / q - P / 3 ^ a = n / (q * 3 ^ a) := by
    simp only [hn]; push_cast; field_simp
  have hge : 1 / ((q : ℝ) * 3 ^ a) ≤ |(p : ℝ) / q - P / 3 ^ a| := by
    rw [hdiff, abs_div, abs_of_pos (by positivity : (0:ℝ) < q * 3 ^ a)]
    exact div_le_div_of_nonneg_right hn1 (by positivity)
  have hE : 1 / (3 : ℝ) ^ E ≤ 1 / (2 * q * 3 ^ a) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast hqE
  have htri : |(p : ℝ) / q - P / 3 ^ a| ≤ |x - p / q| + |x - P / 3 ^ a| := by
    rw [abs_sub_comm x]; exact abs_sub_le _ _ _
  have : 1 / ((q : ℝ) * 3 ^ a) = 2 * (1 / (2 * q * 3 ^ a)) := by field_simp
  linarith


/-- **Ball mass (Frostman bound for the coin point).**  Confidence 90%.

English proof.  The depth-`n` cylinders of the point (fixing the free coins below `n`) are
intervals `[P/3ⁿ, P/3ⁿ + 3^{−n}]`, `P` with ternary digits in `{0,2}`; two distinct ones are
separated by a gap `≥ 3^{−n}`.  An open interval of length `2r ≤ 2·3^{−(n+1)} < 3^{−n}` meets at
most one of them, and each has coin mass `2^{−F(n)}` (or `0`). -/
theorem coins_ball_le (free : ℕ → Bool) (y r : ℝ) (n : ℕ) (hr : r ≤ 1 / 3 ^ (n + 1)) :
    coins.real {ω | |pt free ω - y| < r} ≤ 2 * (1 / 2 : ℝ) ^ freeCount free n := by
  have := CantorExpGeneric.ball_le free y r n hr
  have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ freeCount free n := by positivity
  linarith

open Classical in
/-- **Trivial count of numerators near the support.**  Confidence 90%.

English proof.  The support lies in the `≤ 2^{F(m)}` depth-`m` cylinders, intervals of length
`3^{−m} ≤ 1/q`.  The `r`-neighbourhood (`r ≤ 1/q`) of one has length `≤ 3/q`, so holds at most
`4` fractions `p/q`. -/
theorem card_near_le (free : ℕ → Bool) (q m : ℕ) (hq : 0 < q) (hqm : q ≤ 3 ^ m) (r : ℝ)
    (hr : r ≤ 1 / q) :
    ((Finset.range (q + 1)).filter fun p : ℕ => ∃ ω, |pt free ω - p / q| < r).card ≤
      4 * 2 ^ freeCount free m := by
  have := CantorExpGeneric.card_near_le' free q m hq hqm r hr
  omega

/-! ## The window count -/

section Window

open CantorExpGeneric

variable {μ₀ : ℚ}

theorem cast_expRunStart_succ (μ₀ : ℚ) (k : ℕ) :
    (expRunStart μ₀ (k + 1) : ℝ) = ((k : ℝ) + 2) * expRunEnd μ₀ (expRunStart μ₀ k) := by
  rw [expRunStart_succ]; push_cast; ring

/-- Free count of `[m, n)` against the gap `[E_k, a_{k+1})`, from any `x ≥ max(m, E_k)`. -/
theorem fc_gap_ge (hμ : 1 < μ₀) (k x m n : ℕ) (hx : expRunEnd μ₀ (expRunStart μ₀ k) ≤ x)
    (hmx : m ≤ x) :
    (min n (expRunStart μ₀ (k + 1)) : ℝ) - x ≤ fc (expFree μ₀) m n := by
  rcases le_total (min n (expRunStart μ₀ (k + 1))) x with h | h
  · have : (min n (expRunStart μ₀ (k + 1)) : ℝ) ≤ x := by exact_mod_cast h
    have : (0 : ℝ) ≤ fc (expFree μ₀) m n := by positivity
    linarith
  · have h1 := fc_mono (expFree μ₀) hmx (min_le_left n (expRunStart μ₀ (k + 1)))
    have h2 : fc (expFree μ₀) x (min n (expRunStart μ₀ (k + 1))) =
        min n (expRunStart μ₀ (k + 1)) - x :=
      fc_of_free _ fun i hi1 hi2 => expFree_of_gap hμ (hx.trans hi1)
        (lt_of_lt_of_le hi2 (min_le_right _ _))
    rw [h2] at h1
    have : ((min n (expRunStart μ₀ (k + 1)) - x : ℕ) : ℝ) = (min n (expRunStart μ₀ (k + 1)) : ℝ) - x := by
      rw [Nat.cast_sub h, Nat.cast_min]
    have h1' : ((min n (expRunStart μ₀ (k + 1)) - x : ℕ) : ℝ) ≤ fc (expFree μ₀) m n := by
      exact_mod_cast h1
    linarith

/-- **Core window lemma**, uniform in the exponent `σ ∈ [μ₀, μ₀+1]`. -/
theorem window_core (hμ : 2 < μ₀) : ∃ C : ℝ, ∀ σ : ℝ, (μ₀ : ℝ) ≤ σ → σ ≤ μ₀ + 1 →
    ∀ k m n : ℕ, (expRunEnd μ₀ (expRunStart μ₀ k) : ℝ) ≤ m + expRunStart μ₀ k + 2 →
      (σ - 1) * m ≤ expRunStart μ₀ (k + 1) + 4 → σ * m - 4 ≤ n →
      ((μ₀ : ℝ) - 2) * m ≤ fc (expFree μ₀) m n + C := by
  have hμ1 : (1 : ℚ) < μ₀ := by linarith
  set μ : ℝ := (μ₀ : ℝ) with hμdef
  have hμR : (2 : ℝ) < μ := by rw [hμdef]; exact_mod_cast hμ
  set K₀ : ℕ := ⌈μ₀⌉₊
  set A : ℝ := (expRunStart μ₀ K₀ : ℝ)
  set B₁ : ℝ := (A + 4) / (μ - 1)
  have hB₁ : 0 ≤ B₁ := div_nonneg (by positivity) (by linarith)
  refine ⟨(μ - 2) * B₁ + 3 * μ + 12, fun σ hσ1 hσ2 k m n h1 h2 h3 => ?_⟩
  have hfc0 : (0 : ℝ) ≤ fc (expFree μ₀) m n := by positivity
  have hm0 : (0 : ℝ) ≤ m := by positivity
  set a : ℝ := (expRunStart μ₀ k : ℝ) with ha
  set E : ℝ := (expRunEnd μ₀ (expRunStart μ₀ k) : ℝ) with hE
  set a' : ℝ := (expRunStart μ₀ (k + 1) : ℝ) with ha'
  have hEa : μ * a ≤ E := expRunEnd_ge_r μ₀ _
  have hEa1 : E < μ * a + 1 := expRunEnd_lt_r hμ1 _
  have ha0 : 0 ≤ a := by positivity
  have hstep : a' = ((k : ℝ) + 2) * E := cast_expRunStart_succ μ₀ k
  rcases lt_or_ge k K₀ with hk | hk
  · -- small `k`: `m` is bounded
    have hmono : a' ≤ A := by
      simp only [ha', A]; exact_mod_cast (expRunStart_strictMono hμ1).monotone (by omega)
    have hm : m ≤ B₁ := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    nlinarith
  · have hkμ : μ ≤ k := by
      have : (μ₀ : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast Nat.le_ceil μ₀
      have : (K₀ : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    rcases le_or_gt (expRunEnd μ₀ (expRunStart μ₀ k)) m with hmE | hmE
    · have g := fc_gap_ge hμ1 k m m n hmE le_rfl
      have hmin : (σ - 1) * m - 4 ≤ (min n (expRunStart μ₀ (k + 1)) : ℝ) := by
        push_cast; refine le_min ?_ ?_ <;> [nlinarith; linarith]
      nlinarith
    · have g := fc_gap_ge hμ1 k _ m n le_rfl hmE.le
      have hmE' : (m : ℝ) < E := by rw [hE]; exact_mod_cast hmE
      rcases le_or_gt E (n : ℝ) with hnE | hnE
      · have hmin : min ((μ - 2) * m - 8) ((k + 1) * E) ≤ (min n (expRunStart μ₀ (k + 1)) : ℝ) - E := by
          push_cast
          rcases le_total (n : ℝ) a' with hn | hn
          · rw [min_eq_left hn]
            refine (min_le_left _ _).trans ?_
            nlinarith
          · rw [min_eq_right hn]
            refine (min_le_right _ _).trans ?_
            rw [hstep]; linarith
        rcases le_total ((μ - 2) * m - 8) ((k + 1) * E) with hh | hh
        · rw [min_eq_left hh] at hmin; nlinarith
        · rw [min_eq_right hh] at hmin
          have : (μ - 2) * m ≤ (k + 1) * E := by nlinarith
          nlinarith
      · -- `n < E`: then `a` and `m` are bounded
        have h4 : (σ - 1) * E < σ * a + 2 * σ + 4 := by nlinarith
        have h5 : (σ - 1) * (μ * a) ≤ (σ - 1) * E := mul_le_mul_of_nonneg_left hEa (by linarith)
        have h6 : a * (μ * (μ - 2)) ≤ 2 * μ + 6 := by nlinarith
        have h7 : (μ - 2) * m ≤ (μ - 2) * (μ * a + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
        nlinarith

end Window

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
  obtain ⟨C, hC⟩ := window_core hμ
  refine ⟨C, fun k m h1 h2 => ?_⟩
  have hτ2 : (2 : ℝ) < τ := lt_trans (by exact_mod_cast hμ) hτ
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hmn : m ≤ ⌈τ * m⌉₊ := by
    have : (m : ℝ) ≤ τ * m := by nlinarith
    exact_mod_cast this.trans (Nat.le_ceil _)
  rw [CantorExpGeneric.freeCount_sub _ hmn]
  push_cast
  have hσ := hC (min τ ((μ₀ : ℝ) + 1)) (le_min hτ.le (by linarith)) (min_le_right _ _) k m ⌈τ * m⌉₊
    (by exact_mod_cast h1)
    (by have : (min τ ((μ₀ : ℝ) + 1) - 1) * m ≤ (τ - 1) * m :=
          mul_le_mul_of_nonneg_right (by linarith [min_le_left τ ((μ₀ : ℝ) + 1)]) hm0
        linarith)
    (by have : min τ ((μ₀ : ℝ) + 1) * m ≤ τ * m :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hm0
        linarith [Nat.le_ceil (τ * m)])
  linarith

theorem rho_lt_one (μ₀ : ℝ) (hμ : threshold < μ₀) : 3 * (2 : ℝ) ^ (-(μ₀ - 2)) < 1 := by
  have h1 : (3 : ℝ) = 2 ^ Real.logb 2 3 := (Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)).symm
  rw [h1, ← Real.rpow_add (by norm_num)]
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  unfold threshold at hμ; linarith
/-- **Where the threshold enters.**  The trivial-count block costs `3ᵐ 2^{−(μ₀−2)m}` are summable
exactly above `2 + log₂ 3`.  Confidence 95%.

English proof.  `3 · 2^{−(μ₀−2)} < 1 ⇔ μ₀ − 2 > log₂ 3`; geometric series. -/
theorem summable_bc_of_threshold_lt (μ₀ : ℝ) (hμ : threshold < μ₀) :
    Summable fun m : ℕ => (3 : ℝ) ^ m * (2 : ℝ) ^ (-((μ₀ - 2) * m)) := by
  have hρ := rho_lt_one μ₀ hμ
  refine (summable_geometric_of_lt_one (by positivity) hρ).congr fun m => ?_
  rw [mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ (-(μ₀ - 2))), ← Real.rpow_mul (by norm_num)]
  ring_nf

/-! ## The sibling the mechanism must refuse -/

/-- **Structural cap at the entry of a run.**  If the window `(m, n]` reaches into the run
`[a', E')`, its free places are at most `a' − m`.  Confidence 95%.

English proof.  Places in `[a', n)` are forced; `freeCount` counts places `< n`. -/
theorem freeCount_window_le_of_run (μ₀ : ℚ) (k m n : ℕ) (hm : m ≤ expRunStart μ₀ k)
    (hn : n ≤ expRunEnd μ₀ (expRunStart μ₀ k)) :
    freeCount (expFree μ₀) n - freeCount (expFree μ₀) m ≤ expRunStart μ₀ k - m := by
  rcases le_total n m with hnm | hmn
  · have : freeCount (expFree μ₀) n ≤ freeCount (expFree μ₀) m := by
      unfold freeCount
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hnm))
    omega
  rw [CantorExpGeneric.freeCount_sub _ hmn, Nat.add_sub_cancel_left]
  by_cases hμ : 1 < μ₀
  · rcases le_total n (expRunStart μ₀ k) with h | h
    · exact (CantorExpGeneric.fc_le _ m n).trans (by omega)
    · rw [CantorExpGeneric.fc_add _ hm h]
      have h0 : CantorExpGeneric.fc (expFree μ₀) (expRunStart μ₀ k) n = 0 := by
        unfold CantorExpGeneric.fc
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i hi
        rw [Finset.mem_Ico] at hi
        rw [expFree_of_run hμ hi.1 (lt_of_lt_of_le hi.2 hn)]; simp
      rw [h0, add_zero]; exact CantorExpGeneric.fc_le _ _ _
  · -- `μ₀ ≤ 1`: the run `[a, ⌈μ₀ a⌉)` lies inside `[0, a]`, so `n ≤ a`
    push Not at hμ
    have hE : expRunEnd μ₀ (expRunStart μ₀ k) ≤ expRunStart μ₀ k := by
      unfold expRunEnd
      rcases le_or_gt μ₀ 0 with h0 | h0
      · have : μ₀ * (expRunStart μ₀ k : ℚ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0 (by positivity)
        rw [Nat.ceil_eq_zero.2 this]; exact Nat.zero_le _
      · refine Nat.ceil_le.2 ?_
        calc μ₀ * (expRunStart μ₀ k : ℚ) ≤ 1 * expRunStart μ₀ k := by gcongr
          _ = _ := one_mul _
    exact (CantorExpGeneric.fc_le _ m n).trans (by omega)

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
  open CantorExpGeneric in
  have hF_mono : ∀ x y, x ≤ y → freeCount (expFree μ₀) x ≤ freeCount (expFree μ₀) y := fun x y h => by
    rw [freeCount_sub _ h]; omega
  have hA : ∀ k, expRunStart μ₀ k ≤ 2 * freeCount (expFree μ₀) (expRunStart μ₀ k) := by
    intro k
    cases k with
    | zero =>
      rw [show expRunStart μ₀ 0 = 4 from rfl, freeCount_eq_fc,
        fc_of_free _ fun i _ hi => expFree_of_lt_four hμ hi]; norm_num
    | succ k =>
      have h1 := freeCount_sub (expFree μ₀) (end_lt_start_succ hμ k).le
      rw [fc_of_free _ fun i hi1 hi2 => expFree_of_gap hμ hi1 hi2] at h1
      rw [h1, expRunStart_succ]
      have : (k + 2) * expRunEnd μ₀ (expRunStart μ₀ k) - expRunEnd μ₀ (expRunStart μ₀ k) =
          (k + 1) * expRunEnd μ₀ (expRunStart μ₀ k) := by
        rw [show k + 2 = (k + 1) + 1 by ring, add_mul, one_mul, Nat.add_sub_cancel]
      rw [this]; nlinarith
  have hμR : (1 : ℝ) < (μ₀ : ℝ) := by exact_mod_cast hμ
  set μ : ℝ := (μ₀ : ℝ)
  refine ⟨1 / (2 * μ + 2), by positivity, fun M => ?_⟩
  have hc : (1 / (2 * μ + 2)) * (2 * μ + 2) = 1 := by field_simp
  have hF0 : (0 : ℝ) ≤ freeCount (expFree μ₀) M := by positivity
  rcases lt_or_ge M 4 with hM | hM
  · have : (M : ℝ) ≤ 4 := by exact_mod_cast hM.le
    have : 1 / (2 * μ + 2) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  have hex : ∃ j, M < expRunStart μ₀ j := ⟨M, lt_expRunStart hμ M⟩
  set j := Nat.find hex
  have hj : M < expRunStart μ₀ j := Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h; rw [h] at hj; simp [expRunStart] at hj; omega
  obtain ⟨k, hk1⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [hk1] at hj
  have hk : expRunStart μ₀ k ≤ M := by
    by_contra h; exact Nat.find_min hex (show k < Nat.find hex by omega) (by omega)
  have hAk := hA k
  have hAkR : (expRunStart μ₀ k : ℝ) ≤ 2 * freeCount (expFree μ₀) (expRunStart μ₀ k) := by
    exact_mod_cast hAk
  have hEa1 := expRunEnd_lt_r hμ (expRunStart μ₀ k)
  rcases lt_or_ge M (expRunEnd μ₀ (expRunStart μ₀ k)) with hME | hME
  · have hFm : (freeCount (expFree μ₀) (expRunStart μ₀ k) : ℝ) ≤ freeCount (expFree μ₀) M := by
      exact_mod_cast hF_mono _ _ hk
    have hMR : (M : ℝ) < μ * expRunStart μ₀ k + 1 := by
      have : (M : ℝ) < expRunEnd μ₀ (expRunStart μ₀ k) := by exact_mod_cast hME
      linarith
    have key : 1 / (2 * μ + 2) * M ≤ 1 / (2 * μ + 2) * (μ * expRunStart μ₀ k + 1) :=
      mul_le_mul_of_nonneg_left hMR.le (by positivity)
    have hA0 : (0 : ℝ) ≤ expRunStart μ₀ k := by positivity
    have : 1 / (2 * μ + 2) * (μ * expRunStart μ₀ k + 1) ≤ expRunStart μ₀ k / 2 + 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]; nlinarith
    linarith
  · have h1 := freeCount_sub (expFree μ₀) hME
    rw [fc_of_free _ fun i hi1 hi2 => expFree_of_gap hμ hi1 (lt_of_lt_of_le hi2 hj.le)] at h1
    have h2 : (freeCount (expFree μ₀) (expRunStart μ₀ k) : ℝ) ≤
        freeCount (expFree μ₀) (expRunEnd μ₀ (expRunStart μ₀ k)) := by
      exact_mod_cast hF_mono _ _ (le_expRunEnd hμ _)
    have h1R : (freeCount (expFree μ₀) M : ℝ) =
        freeCount (expFree μ₀) (expRunEnd μ₀ (expRunStart μ₀ k)) + M - expRunEnd μ₀ (expRunStart μ₀ k) := by
      rw [h1]; push_cast [Nat.cast_sub hME]; ring
    have hMR : (M : ℝ) - expRunEnd μ₀ (expRunStart μ₀ k) ≥ 0 := by
      have : (expRunEnd μ₀ (expRunStart μ₀ k) : ℝ) ≤ M := by exact_mod_cast hME
      linarith
    have hA0 : (0 : ℝ) ≤ expRunStart μ₀ k := by positivity
    have hc1 : 1 / (2 * μ + 2) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have k1 : 1 / (2 * μ + 2) * (expRunEnd μ₀ (expRunStart μ₀ k) : ℝ) ≤ expRunStart μ₀ k / 2 + 1 := by
      have : 1 / (2 * μ + 2) * (expRunEnd μ₀ (expRunStart μ₀ k) : ℝ) ≤
          1 / (2 * μ + 2) * (μ * expRunStart μ₀ k + 1) :=
        mul_le_mul_of_nonneg_left hEa1.le (by positivity)
      have : 1 / (2 * μ + 2) * (μ * expRunStart μ₀ k + 1) ≤ expRunStart μ₀ k / 2 + 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]; nlinarith
      linarith
    have k2 : 1 / (2 * μ + 2) * ((M : ℝ) - expRunEnd μ₀ (expRunStart μ₀ k)) ≤
        (M : ℝ) - expRunEnd μ₀ (expRunStart μ₀ k) := by
      nlinarith
    nlinarith

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
