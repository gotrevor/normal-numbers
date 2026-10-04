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

/-! ## Schedule structure, window counts, cylinders (helpers) -/

theorem le_expRunEnd (μ₀ : ℚ) (_hμ : 1 < μ₀) (a : ℕ) : (μ₀ : ℝ) * a ≤ expRunEnd μ₀ a := by
  unfold expRunEnd
  have := Nat.le_ceil (μ₀ * a)
  exact_mod_cast this

theorem expRunEnd_le (μ₀ : ℚ) (hμ : 1 < μ₀) (a : ℕ) : (expRunEnd μ₀ a : ℝ) < μ₀ * a + 1 := by
  unfold expRunEnd
  have := Nat.ceil_lt_add_one (show (0:ℚ) ≤ μ₀ * a by positivity)
  exact_mod_cast this

theorem lt_expRunEnd (μ₀ : ℚ) (hμ : 1 < μ₀) {a : ℕ} (ha : 1 ≤ a) : a < expRunEnd μ₀ a := by
  have h := le_expRunEnd μ₀ hμ a
  have : (a : ℝ) < μ₀ * a := by
    have : (1:ℝ) < μ₀ := by exact_mod_cast hμ
    have : (1:ℝ) ≤ a := by exact_mod_cast ha
    nlinarith
  exact_mod_cast this.trans_le h

theorem four_le_expRunStart (μ₀ : ℚ) (hμ : 1 < μ₀) (k : ℕ) : 4 ≤ expRunStart μ₀ k := by
  induction k with
  | zero => simp [expRunStart]
  | succ k ih =>
    simp only [expRunStart]
    have := lt_expRunEnd μ₀ hμ (a := expRunStart μ₀ k) (by omega)
    nlinarith

theorem expRunStart_succ (μ₀ : ℚ) (k : ℕ) :
    expRunStart μ₀ (k + 1) = (k + 2) * expRunEnd μ₀ (expRunStart μ₀ k) := rfl

theorem expRunEnd_lt_next (μ₀ : ℚ) (hμ : 1 < μ₀) (k : ℕ) :
    expRunEnd μ₀ (expRunStart μ₀ k) < expRunStart μ₀ (k + 1) := by
  rw [expRunStart_succ]
  have := lt_expRunEnd μ₀ hμ (a := expRunStart μ₀ k) (by have := four_le_expRunStart μ₀ hμ k; omega)
  nlinarith

theorem expRunStart_strictMono (μ₀ : ℚ) (hμ : 1 < μ₀) : StrictMono (expRunStart μ₀) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  have := lt_expRunEnd μ₀ hμ (a := expRunStart μ₀ k) (by have := four_le_expRunStart μ₀ hμ k; omega)
  exact this.trans (expRunEnd_lt_next μ₀ hμ k)

theorem lt_expRunStart (μ₀ : ℚ) (hμ : 1 < μ₀) (k : ℕ) : k < expRunStart μ₀ k := by
  induction k with
  | zero => have h4 := four_le_expRunStart μ₀ hμ 0; omega
  | succ k ih =>
    have := expRunStart_strictMono μ₀ hμ (Nat.lt_succ_self k)
    simp only [Nat.succ_eq_add_one] at this ⊢; omega

theorem expRunEnd_mono (μ₀ : ℚ) (hμ : 1 < μ₀) {a b : ℕ} (h : a ≤ b) :
    expRunEnd μ₀ a ≤ expRunEnd μ₀ b := by
  unfold expRunEnd
  apply Nat.ceil_mono
  have : (0:ℚ) ≤ μ₀ := by linarith
  gcongr

/-- Forced iff inside a run. -/
theorem expFree_eq_false_iff (μ₀ : ℚ) (hμ : 1 < μ₀) (i : ℕ) :
    expFree μ₀ i = false ↔ ∃ k, expRunStart μ₀ k ≤ i ∧ i < expRunEnd μ₀ (expRunStart μ₀ k) := by
  unfold expFree expForced
  simp only [Bool.not_eq_false', List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨k, -, h⟩; exact ⟨k, h⟩
  · rintro ⟨k, h⟩
    exact ⟨k, by have := lt_expRunStart μ₀ hμ k; omega, h⟩

theorem expFree_of_not_run (μ₀ : ℚ) (hμ : 1 < μ₀) {i : ℕ}
    (h : ∀ k, ¬ (expRunStart μ₀ k ≤ i ∧ i < expRunEnd μ₀ (expRunStart μ₀ k))) :
    expFree μ₀ i = true := by
  by_contra hc
  rw [Bool.not_eq_true, expFree_eq_false_iff μ₀ hμ] at hc
  obtain ⟨k, hk⟩ := hc
  exact h k hk

theorem expRunEnd_strictMono (μ₀ : ℚ) (hμ : 1 < μ₀) :
    StrictMono fun k => expRunEnd μ₀ (expRunStart μ₀ k) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  have h1 := expRunEnd_lt_next μ₀ hμ k
  have h2 := lt_expRunEnd μ₀ hμ (a := expRunStart μ₀ (k + 1))
    (by have := four_le_expRunStart μ₀ hμ (k+1); omega)
  exact h1.trans h2

/-- The gap `[E_k, a_{k+1})` is free. -/
theorem expFree_gap (μ₀ : ℚ) (hμ : 1 < μ₀) {k i : ℕ}
    (h1 : expRunEnd μ₀ (expRunStart μ₀ k) ≤ i) (h2 : i < expRunStart μ₀ (k + 1)) :
    expFree μ₀ i = true := by
  refine expFree_of_not_run μ₀ hμ fun j ⟨hj1, hj2⟩ => ?_
  rcases Nat.lt_or_ge k j with hjk | hjk
  · have := (expRunStart_strictMono μ₀ hμ).monotone (show k + 1 ≤ j by omega); omega
  · have := (expRunEnd_strictMono μ₀ hμ).monotone hjk; omega

theorem expFree_init (μ₀ : ℚ) (hμ : 1 < μ₀) {i : ℕ} (h : i < expRunStart μ₀ 0) :
    expFree μ₀ i = true := by
  refine expFree_of_not_run μ₀ hμ fun j ⟨hj1, _⟩ => ?_
  have := (expRunStart_strictMono μ₀ hμ).monotone (Nat.zero_le j); omega

theorem expFree_run (μ₀ : ℚ) {k i : ℕ}
    (h1 : expRunStart μ₀ k ≤ i) (h2 : i < expRunEnd μ₀ (expRunStart μ₀ k)) (hμ : 1 < μ₀) :
    expFree μ₀ i = false := (expFree_eq_false_iff μ₀ hμ i).2 ⟨k, h1, h2⟩

theorem freeCount_mono (free : ℕ → Bool) {m n : ℕ} (h : m ≤ n) :
    freeCount free m ≤ freeCount free n := by
  unfold freeCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

theorem freeCount_succ_le (free : ℕ → Bool) (n : ℕ) :
    freeCount free (n + 1) ≤ freeCount free n + 1 := by
  unfold freeCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs
  · exact (Finset.card_insert_le _ _)
  · omega

theorem freeCount_add_le (free : ℕ → Bool) (n d : ℕ) :
    freeCount free (n + d) ≤ freeCount free n + d := by
  induction d with
  | zero => simp
  | succ d ih => have := freeCount_succ_le free (n + d); rw [← add_assoc]; omega

/-- A free interval `[s, e)` inside `[m, n)` contributes `e − s` to the window count. -/
theorem le_freeCount_sub (free : ℕ → Bool) {m n s e : ℕ} (hmn : m ≤ n) (hms : m ≤ s)
    (hen : e ≤ n) (hf : ∀ i, s ≤ i → i < e → free i = true) :
    (e : ℝ) - s ≤ (freeCount free n : ℝ) - freeCount free m := by
  have hFm := freeCount_mono free hmn
  rcases Nat.lt_or_ge s e with hse | hse
  · have : freeCount free m + (e - s) ≤ freeCount free n := by
      unfold freeCount
      rw [← Nat.card_Ico s e, ← Finset.card_union_of_disjoint]
      · refine Finset.card_le_card fun i hi => ?_
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hi ⊢
        rcases hi with hi | hi
        · exact ⟨by omega, hi.2⟩
        · exact ⟨by omega, hf i hi.1 hi.2⟩
      · rw [Finset.disjoint_left]; intro i h1 h2
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
    have : ((freeCount free m + (e - s) : ℕ) : ℝ) ≤ freeCount free n := by exact_mod_cast this
    push_cast [hse.le] at this; linarith
  · have : (e : ℝ) ≤ s := by exact_mod_cast hse
    have : (freeCount free m : ℝ) ≤ freeCount free n := by exact_mod_cast hFm
    linarith

/-- **Window count, general form**: for `m` in the Borel–Cantelli range of run `k` (with `μ₀`)
and any window end `n ∈ [μ₀ m, Λ m + 1]`. -/
theorem window_ge_gen (μ₀ : ℚ) (hμ : 2 < μ₀) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, ∀ k m n : ℕ, expRunEnd μ₀ (expRunStart μ₀ k) ≤ m + expRunStart μ₀ k + 2 →
      ((μ₀ : ℝ) - 1) * m ≤ expRunStart μ₀ (k + 1) + 2 → (μ₀ : ℝ) * m ≤ n → (n : ℝ) ≤ Λ * m + 1 →
      ((μ₀ : ℝ) - 2) * m ≤ (freeCount (expFree μ₀) n : ℝ) - freeCount (expFree μ₀) m + C := by
  have hμ1 : (1 : ℚ) < μ₀ := by linarith
  have hμR : (2 : ℝ) < μ₀ := by exact_mod_cast hμ
  set K := ⌈Λ⌉₊
  set Ssum : ℝ := ∑ j ∈ Finset.range (K + 1), (expRunEnd μ₀ (expRunStart μ₀ j) : ℝ)
  have hS0 : 0 ≤ Ssum := Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨4 + μ₀ * Ssum, fun k m n hlo hhi hn1 hn2 => ?_⟩
  set a := expRunStart μ₀ k
  set E := expRunEnd μ₀ a
  set a' := expRunStart μ₀ (k + 1)
  have ha' : a' = (k + 2) * E := expRunStart_succ μ₀ k
  have hEa := le_expRunEnd μ₀ hμ1 a
  have hEa2 := expRunEnd_le μ₀ hμ1 a
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hW0 : (0 : ℝ) ≤ (freeCount (expFree μ₀) n : ℝ) - freeCount (expFree μ₀) m := by
    have : (freeCount (expFree μ₀) m : ℝ) ≤ freeCount (expFree μ₀) n := by
      exact_mod_cast freeCount_mono _ hmn
    linarith
  have hloR : (E : ℝ) ≤ m + a + 2 := by exact_mod_cast hlo
  have hμ0 : (0 : ℝ) ≤ μ₀ := by linarith
  have hμS : 0 ≤ (μ₀ : ℝ) * Ssum := mul_nonneg hμ0 hS0
  have e1 : ((μ₀ : ℝ) - 2) * m = μ₀ * m - 2 * m := by ring
  rcases Nat.lt_or_ge m a with hma | hma
  · -- `m` below the run start: bounded
    have hmaR : (m : ℝ) < a := by exact_mod_cast hma
    have h1 := mul_le_mul_of_nonneg_left hmaR.le (sub_nonneg.2 hμR.le)
    have e2 : ((μ₀ : ℝ) - 2) * a = μ₀ * a - 2 * a := by ring
    linarith
  have hmaR : (a : ℝ) ≤ m := by exact_mod_cast hma
  -- the free interval `[max m E, min n a')`
  have hfree : ∀ i, max m E ≤ i → i < min n a' → expFree μ₀ i = true := fun i h1 h2 =>
    expFree_gap μ₀ hμ1 (k := k) (le_of_max_le_right h1) (lt_of_lt_of_le h2 (min_le_right _ _))
  have hW := le_freeCount_sub (expFree μ₀) hmn (le_max_left m E) (min_le_left n a') hfree
  rcases le_total n a' with hna | hna <;> rcases le_total E m with hEm | hEm
  · rw [min_eq_left hna, max_eq_left hEm] at hW
    linarith
  · rw [min_eq_left hna, max_eq_right hEm] at hW
    linarith
  · rw [min_eq_right hna, max_eq_left hEm] at hW
    have e3 : ((μ₀ : ℝ) - 2) * m = (μ₀ - 1) * m - m := by ring
    linarith
  · -- window enters run `k+1` from inside run `k`: only `k < K`
    have hEmR : (m : ℝ) ≤ E := by exact_mod_cast hEm
    have hE1 : (1 : ℝ) ≤ E := by
      have := four_le_expRunStart μ₀ hμ1 k
      have : (4 : ℝ) ≤ a := by exact_mod_cast this
      nlinarith
    have hkK : k < K + 1 := by
      by_contra hc
      have hk : (K : ℝ) ≤ k := by exact_mod_cast (show K ≤ k by omega)
      have hΛK : Λ ≤ K := Nat.le_ceil Λ
      have hnaR : (a' : ℝ) ≤ n := by exact_mod_cast hna
      have ha'R : (a' : ℝ) = k * E + 2 * E := by rw [ha']; push_cast; ring
      have p1 := mul_le_mul_of_nonneg_left hEmR hΛ
      have p2 := mul_le_mul_of_nonneg_right hΛK (show (0:ℝ) ≤ E by linarith)
      have p3 := mul_le_mul_of_nonneg_right hk (show (0:ℝ) ≤ E by linarith)
      linarith
    have hES : (E : ℝ) ≤ Ssum :=
      Finset.single_le_sum (f := fun j => (expRunEnd μ₀ (expRunStart μ₀ j) : ℝ))
        (fun _ _ => by positivity) (Finset.mem_range.2 hkK)
    have p1 := mul_le_mul_of_nonneg_left hEmR hμ0
    have p2 := mul_le_mul_of_nonneg_left hES hμ0
    linarith

/-! ## Generic digit splitting and cylinders (any free set) -/

theorem ptDigit_le_two (free : ℕ → Bool) (ω : ℕ → Bool) (i : ℕ) : (ptDigit free ω i : ℝ) ≤ 2 := by
  have : ptDigit free ω i ≤ 2 := by unfold ptDigit; split_ifs <;> norm_num
  exact_mod_cast this

theorem geom_tail (n : ℕ) : ∑' i : ℕ, (2 : ℝ) / 3 ^ (i + n + 1) = 1 / 3 ^ n := by
  have : (fun i : ℕ => (2 : ℝ) / 3 ^ (i + n + 1)) = fun i => 2 / 3 ^ (n + 1) * (1 / 3) ^ i := by
    funext i; rw [one_div_pow, show i + n + 1 = i + (n + 1) by ring, pow_add]; field_simp
  rw [this, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num), pow_succ]
  field_simp; norm_num

theorem summable_geom_tail (n : ℕ) : Summable fun i : ℕ => (2 : ℝ) / 3 ^ (i + n + 1) := by
  have := (summable_geometric_of_lt_one (r := (1 / 3 : ℝ)) (by norm_num) (by norm_num)).mul_left
    (2 / 3 ^ (n + 1))
  refine this.congr fun i => ?_
  rw [one_div_pow]; field_simp; ring

/-- **Split at depth `n`**: head sum plus a tail in `[0, 3^{-n}]`. -/
theorem pt_split (free : ℕ → Bool) (ω : ℕ → Bool) (n : ℕ) :
    ∃ T : ℝ, 0 ≤ T ∧ T ≤ 1 / 3 ^ n ∧
      pt free ω = ∑ i ∈ Finset.range n, (ptDigit free ω i : ℝ) / 3 ^ (i + 1) + T := by
  have hs := summable_ptDigit free ω
  refine ⟨∑' k, (ptDigit free ω (k + n) : ℝ) / (3 : ℝ) ^ (k + n + 1),
    tsum_nonneg fun k => by positivity, ?_, ?_⟩
  · rw [← geom_tail n]
    refine (hs.comp_injective (add_left_injective n)).tsum_le_tsum (fun k => ?_)
      (summable_geom_tail n)
    exact div_le_div_of_nonneg_right (ptDigit_le_two _ _ _) (by positivity)
  · unfold pt realOfDigits
    simp only [Nat.cast_ofNat]
    exact (hs.sum_add_tsum_nat_add n).symm

/-- **Separation**: digits agreeing below `i` and differing at `i` put the points `≥ 3^{-(i+1)}`
apart. -/
theorem abs_pt_sub_ge (free : ℕ → Bool) (ω ω' : ℕ → Bool) (i : ℕ)
    (hlt : ∀ j < i, ptDigit free ω j = ptDigit free ω' j)
    (hne : ptDigit free ω i ≠ ptDigit free ω' i) :
    1 / (3 : ℝ) ^ (i + 1) ≤ |pt free ω - pt free ω'| := by
  obtain ⟨T, hT0, hT1, hx⟩ := pt_split free ω (i + 1)
  obtain ⟨T', hT0', hT1', hx'⟩ := pt_split free ω' (i + 1)
  rw [Finset.sum_range_succ] at hx hx'
  have hsum : ∑ j ∈ Finset.range i, (ptDigit free ω j : ℝ) / 3 ^ (j + 1) =
      ∑ j ∈ Finset.range i, (ptDigit free ω' j : ℝ) / 3 ^ (j + 1) :=
    Finset.sum_congr rfl fun j hj => by rw [hlt j (Finset.mem_range.1 hj)]
  have hd : ∀ (w : ℕ → Bool), ptDigit free w i = 0 ∨ ptDigit free w i = 2 := fun w => by
    unfold ptDigit; split_ifs <;> simp
  set u : ℝ := 1 / 3 ^ (i + 1)
  have hkey : pt free ω - pt free ω' =
      ((ptDigit free ω i : ℝ) - ptDigit free ω' i) * u + (T - T') := by
    rw [hx, hx', hsum]; simp only [u]; ring
  rw [hkey]
  rcases hd ω with h | h <;> rcases hd ω' with h' | h'
  · exact absurd (h.trans h'.symm) hne
  · rw [h, h']; push_cast; exact le_abs.2 (Or.inr (by linarith))
  · rw [h, h']; push_cast; exact le_abs.2 (Or.inl (by linarith))
  · exact absurd (h.trans h'.symm) hne

/-- Mass of a finite-coordinate cylinder. -/
theorem coins_cyl (S : Finset ℕ) (c : ℕ → Bool) :
    coins.real (Set.pi (S : Set ℕ) fun i => {c i}) = (1 / 2 : ℝ) ^ S.card := by
  rw [measureReal_def]
  have hm : coins (Set.pi (S : Set ℕ) fun i => {c i}) = (2⁻¹ : ENNReal) ^ S.card := by
    show ExplicitSquare.coinMeasure _ = _
    unfold ExplicitSquare.coinMeasure
    rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
    refine Finset.prod_eq_pow_card fun i _ => ?_
    rw [CantorSelfSimilar.uniform_apply]
    cases c i <;> simp
  rw [hm, ENNReal.toReal_pow, ENNReal.toReal_inv]
  simp

/-- **Ball mass** (generic form of `coins_ball_le`). -/
theorem coins_ball_le_gen (free : ℕ → Bool) (y r : ℝ) (n : ℕ) (hr : r ≤ 1 / 3 ^ (n + 1)) :
    coins.real {ω | |pt free ω - y| < r} ≤ (1 / 2 : ℝ) ^ freeCount free n := by
  classical
  set B := {ω | |pt free ω - y| < r}
  rcases Set.eq_empty_or_nonempty B with hB | ⟨ω₀, hω₀⟩
  · rw [hB]; simp
  set S := (Finset.range n).filter fun i => free i = true
  have hsub : B ⊆ Set.pi (S : Set ℕ) (fun i => {ω₀ i}) := by
    intro ω hω i hi
    simp only [Set.mem_singleton_iff]
    by_contra hne
    have hex : ∃ j, j ∈ S ∧ ω j ≠ ω₀ j := ⟨i, hi, hne⟩
    obtain ⟨j, ⟨hjS, hjne⟩, hjmin'⟩ : ∃ j, (j ∈ S ∧ ω j ≠ ω₀ j) ∧
        ∀ l < j, ¬ (l ∈ S ∧ ω l ≠ ω₀ l) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun l hl => Nat.find_min hex hl⟩
    have hjmin : ∀ l < j, l ∈ S → ω l = ω₀ l := fun l hl hlS => by
      by_contra h; exact hjmin' l hl ⟨hlS, h⟩
    have hjS' := hjS
    simp only [S, Finset.mem_filter, Finset.mem_range] at hjS'
    have hlt : ∀ l < j, ptDigit free ω l = ptDigit free ω₀ l := by
      intro l hl
      unfold ptDigit
      by_cases hf : free l = true
      · have hjn : j < n := hjS'.1
        rw [hjmin l hl (by simp only [S, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hf⟩)]
      · simp [hf]
    have hneD : ptDigit free ω j ≠ ptDigit free ω₀ j := by
      have hfj : free j = true := hjS'.2
      unfold ptDigit; rw [hfj]
      revert hjne; cases ω j <;> cases ω₀ j <;> simp
    have h1 := abs_pt_sub_ge free ω ω₀ j hlt hneD
    have hB1 : |pt free ω - y| < r := hω
    have hB2 : |pt free ω₀ - y| < r := hω₀
    have h2 : |pt free ω - pt free ω₀| < 2 * r := by
      calc |pt free ω - pt free ω₀| ≤ |pt free ω - y| + |y - pt free ω₀| := abs_sub_le _ _ _
        _ < r + r := by rw [abs_sub_comm y]; linarith
        _ = 2 * r := by ring
    have h3 : (1 : ℝ) / 3 ^ n ≤ 1 / 3 ^ (j + 1) :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by
        have : j < n := hjS'.1
        omega))
    have h4 : (1 : ℝ) / 3 ^ (n + 1) * 3 = 1 / 3 ^ n := by rw [pow_succ]; field_simp
    have h5 : (0 : ℝ) < 1 / 3 ^ (n + 1) := by positivity
    linarith
  have hcard : S.card = freeCount free n := rfl
  calc coins.real B ≤ coins.real (Set.pi (S : Set ℕ) (fun i => {ω₀ i})) := measureReal_mono hsub
    _ = _ := by rw [coins_cyl, hcard]

/-- The depth-`m` numerator of a set `U` of `2`-digits. -/
def headNum (m : ℕ) (U : Finset ℕ) : ℕ := ∑ i ∈ U, 2 * 3 ^ (m - 1 - i)

theorem head_eq (free : ℕ → Bool) (ω : ℕ → Bool) (m : ℕ) :
    ∑ i ∈ Finset.range m, (ptDigit free ω i : ℝ) / 3 ^ (i + 1) =
      (headNum m (((Finset.range m).filter fun i => free i = true).filter fun i => ω i = true) : ℝ)
        / 3 ^ m := by
  classical
  unfold headNum
  rw [Finset.filter_filter, Nat.cast_sum, Finset.sum_div, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  unfold ptDigit
  by_cases h : free i = true ∧ ω i = true
  · rw [if_pos h, if_pos (by simp [h.1, h.2])]
    push_cast
    have : (3 : ℝ) ^ m = 3 ^ (m - 1 - i) * 3 ^ (i + 1) := by rw [← pow_add]; congr 1; omega
    rw [this]; field_simp
  · rw [if_neg h, if_neg (by simpa using h)]; simp

open Classical in
/-- **Numerator count** (generic form of `card_near_le`). -/
theorem card_near_le_gen (free : ℕ → Bool) (q m : ℕ) (hq : 0 < q) (hqm : q ≤ 3 ^ m) (r : ℝ)
    (hr : r ≤ 1 / q) :
    ((Finset.range (q + 1)).filter fun p : ℕ => ∃ ω, |pt free ω - p / q| < r).card ≤
      3 * 2 ^ freeCount free m := by
  classical
  set S := (Finset.range m).filter fun i => free i = true
  set c : Finset ℕ → ℕ := fun U => ⌊(q : ℝ) * ((headNum m U : ℝ) / 3 ^ m)⌋₊
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqmR : (q : ℝ) ≤ 3 ^ m := by exact_mod_cast hqm
  have hsub : ((Finset.range (q + 1)).filter fun p : ℕ => ∃ ω, |pt free ω - p / q| < r) ⊆
      S.powerset.biUnion fun U => Finset.Icc (c U) (c U + 2) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨-, ω, hω⟩ := hp
    rw [Finset.mem_biUnion]
    refine ⟨S.filter fun i => ω i = true, Finset.mem_powerset.2 (Finset.filter_subset _ _), ?_⟩
    obtain ⟨T, hT0, hT1, hx⟩ := pt_split free ω m
    rw [head_eq] at hx
    set H : ℝ := (headNum m (S.filter fun i => ω i = true) : ℝ) / 3 ^ m
    have hH0 : 0 ≤ H := by positivity
    set z := (q : ℝ) * H
    have hz0 : 0 ≤ z := by positivity
    have hab := abs_lt.1 hω
    have hqT : (q : ℝ) * T ≤ 1 := by
      calc (q : ℝ) * T ≤ q * (1 / 3 ^ m) := by gcongr
        _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; exact hqmR
    have hqT0 : 0 ≤ (q : ℝ) * T := by positivity
    have hp1 : (p : ℝ) / q < H + T + 1 / q := by rw [hx] at hab; linarith
    have hp2 : H + T - 1 / q < (p : ℝ) / q := by rw [hx] at hab; linarith
    have e1 : (q : ℝ) * ((p : ℝ) / q) = p := by field_simp
    have e2 : (q : ℝ) * (1 / q) = 1 := by field_simp
    have hp1' := mul_lt_mul_of_pos_left hp1 hqR
    have hp2' := mul_lt_mul_of_pos_left hp2 hqR
    rw [e1, mul_add, mul_add, e2] at hp1'
    rw [e1, mul_sub, mul_add, e2] at hp2'
    have hfl := Nat.floor_le hz0
    have hfl2 := Nat.lt_floor_add_one z
    rw [Finset.mem_Icc]
    constructor
    · have : (⌊z⌋₊ : ℝ) < p + 1 := by linarith
      have : ⌊z⌋₊ < p + 1 := by exact_mod_cast this
      show ⌊z⌋₊ ≤ p; omega
    · have : (p : ℝ) < ⌊z⌋₊ + 3 := by linarith
      have : p < ⌊z⌋₊ + 3 := by exact_mod_cast this
      show p ≤ ⌊z⌋₊ + 2; omega
  calc _ ≤ (S.powerset.biUnion fun U => Finset.Icc (c U) (c U + 2)).card := Finset.card_le_card hsub
    _ ≤ ∑ U ∈ S.powerset, (Finset.Icc (c U) (c U + 2)).card := Finset.card_biUnion_le
    _ = ∑ U ∈ S.powerset, 3 := Finset.sum_congr rfl fun U _ => by rw [Nat.card_Icc]; omega
    _ = 3 * 2 ^ freeCount free m := by
      rw [Finset.sum_const, Finset.card_powerset, smul_eq_mul, mul_comm]; rfl

/-- Forced positions recur (each run start is forced).  Confidence 95%.

English proof.  `k < expRunStart μ₀ k` (induction; the factor `k+2` and `⌈μ₀ a⌉ ≥ a`), and
`expRunStart μ₀ k < ⌈μ₀ · expRunStart μ₀ k⌉` as `μ₀ > 1` and `a ≥ 4`, so `i = expRunStart μ₀ N`
is forced, with `N ≤ i`. -/
theorem expForced_recur (μ₀ : ℚ) (hμ : 1 < μ₀) (N : ℕ) :
    ∃ i, N ≤ i ∧ expFree μ₀ i = false := by
  exact ⟨expRunStart μ₀ N, (lt_expRunStart μ₀ hμ N).le, expFree_run μ₀ le_rfl
    (lt_expRunEnd μ₀ hμ (by have := four_le_expRunStart μ₀ hμ N; omega)) hμ⟩

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
  classical
  refine ⟨2, Filter.frequently_atTop.2 fun N => ?_⟩
  set a := expRunStart μ₀ N
  set E := expRunEnd μ₀ a
  set f : ℕ → ℝ := fun i => (ptDigit (expFree μ₀) ω i : ℝ) / 3 ^ (i + 1)
  have haN := lt_expRunStart μ₀ hμ N
  have haE : a ≤ E := (lt_expRunEnd μ₀ hμ (a := a) (by omega)).le
  obtain ⟨T, hT0, hT1, hx⟩ := pt_split (expFree μ₀) ω E
  have hrun : ∑ i ∈ Finset.Ico a E, f i = 0 := Finset.sum_eq_zero fun i hi => by
    simp only [Finset.mem_Ico] at hi
    simp [f, ptDigit, expFree_run μ₀ (k := N) hi.1 hi.2 hμ]
  have hsplit : ∑ i ∈ Finset.range E, f i = ∑ i ∈ Finset.range a, f i := by
    rw [← Finset.sum_range_add_sum_Ico _ haE, hrun, add_zero]
  set H := headNum a (((Finset.range a).filter fun i => expFree μ₀ i = true).filter
    fun i => ω i = true)
  have hhead := head_eq (expFree μ₀) ω a
  have hxe : cantorExpReal μ₀ ω = (H : ℝ) / 3 ^ a + T := by
    unfold cantorExpReal; rw [hx]; simp only [f] at hsplit; rw [hsplit, hhead]
  -- the tail is positive
  obtain ⟨i, hiE, hfi, hωi⟩ := hf E
  have hTpos : 0 < T := by
    obtain ⟨T', hT0', -, hx'⟩ := pt_split (expFree μ₀) ω (i + 1)
    have h1 : ∑ j ∈ Finset.range (i + 1), f j = ∑ j ∈ Finset.range E, f j +
        ∑ j ∈ Finset.Ico E (i + 1), f j := (Finset.sum_range_add_sum_Ico _ (by omega)).symm
    have h2 : f i ≤ ∑ j ∈ Finset.Ico E (i + 1), f j :=
      Finset.single_le_sum (f := f) (fun j _ => by positivity)
        (Finset.mem_Ico.2 ⟨hiE, Nat.lt_succ_self i⟩)
    have h3 : 0 < f i := by simp [f, ptDigit, hfi, hωi]
    simp only [f] at h1 h2 h3
    linarith
  refine ⟨3 ^ a, ?_, (H : ℤ), ?_, ?_⟩
  · have : N < 3 ^ a := haN.trans (Nat.lt_pow_self (by norm_num))
    omega
  · push_cast; rw [hxe]; intro h; linarith
  · push_cast
    rw [hxe, add_sub_cancel_left, abs_of_pos hTpos]
    have hpow : ((3 : ℝ) ^ a) ^ (μ₀ : ℝ) ≤ 3 ^ E := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast 3 E]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by rw [mul_comm]; exact le_expRunEnd μ₀ hμ a)
    have hp0 : (0 : ℝ) < ((3 : ℝ) ^ a) ^ (μ₀ : ℝ) := by positivity
    calc T ≤ 1 / 3 ^ E := hT1
      _ ≤ 1 / ((3 : ℝ) ^ a) ^ (μ₀ : ℝ) := one_div_le_one_div_of_le hp0 hpow
      _ < 2 / ((3 : ℝ) ^ a) ^ (μ₀ : ℝ) := by gcongr; norm_num

/-- Almost surely free `2`-digits recur.  Confidence 95%.

English proof.  As `CantorLiouville.ae_frequently_free`: the free places `[⌈μ₀ a k⌉, a (k+1))`
form infinitely many disjoint nonempty blocks, so by Borel–Cantelli (or independence) a.s.
infinitely many carry a coin `true`. -/
theorem ae_frequently_two (μ₀ : ℚ) (hμ : 1 < μ₀) :
    ∀ᵐ ω ∂coins, ∀ N, ∃ i, N ≤ i ∧ expFree μ₀ i = true ∧ ω i = true := by
  rw [ae_all_iff]
  intro n
  set p : ℕ → ℕ := fun k => expRunEnd μ₀ (expRunStart μ₀ k)
  have hp : StrictMono p := expRunEnd_strictMono μ₀ hμ
  have hpn : ∀ k, k ≤ p k := fun k => hp.id_le k
  have hpfree : ∀ k, expFree μ₀ (p k) = true := fun k =>
    expFree_gap μ₀ hμ le_rfl (expRunEnd_lt_next μ₀ hμ k)
  rw [ae_iff]
  set E := {ω : ℕ → Bool | ¬∃ i, n ≤ i ∧ expFree μ₀ i = true ∧ ω i = true}
  have hle : ∀ L : ℕ, coins E ≤ (2⁻¹ : ENNReal) ^ L := by
    intro L
    set S := (Finset.Ico n (n + L)).image p
    have hsub : E ⊆ Set.pi (S : Set ℕ) (fun _ => {false}) := by
      intro ω hω i hi
      simp only [S, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_Ico] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      simp only [E, Set.mem_setOf_eq, not_exists, not_and] at hω
      simp only [Set.mem_singleton_iff]
      have := hω (p k) ((hpn k).trans' hk.1) (hpfree k)
      simpa using this
    refine (measure_mono hsub).trans (le_of_eq ?_)
    show ExplicitSquare.coinMeasure _ = _
    unfold ExplicitSquare.coinMeasure
    rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
    rw [Finset.prod_congr rfl (fun i _ => by rw [CantorSelfSimilar.uniform_apply])]
    rw [Finset.prod_const, Finset.card_image_of_injective _ hp.injective, Nat.card_Ico]
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
  set z : ℤ := p * 3 ^ a - P * q
  have e : (p : ℝ) / q - P / 3 ^ a = (z : ℝ) / ((q : ℝ) * 3 ^ a) := by
    simp only [z]; push_cast; field_simp
  have hz : z ≠ 0 := by
    intro h0; apply hne
    have : (p : ℝ) / q - P / 3 ^ a = 0 := by rw [e, h0]; simp
    linarith
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hz
  have hD : (0 : ℝ) < (q : ℝ) * 3 ^ a := by positivity
  have hfar : 1 / ((q : ℝ) * 3 ^ a) ≤ |(p : ℝ) / q - P / 3 ^ a| := by
    rw [e, abs_div, abs_of_pos hD]; exact div_le_div_of_nonneg_right hz1 hD.le
  have hE : (1 : ℝ) / 3 ^ E ≤ 1 / (2 * q * 3 ^ a) := by
    apply one_div_le_one_div_of_le (by positivity); exact_mod_cast hqE
  have htri : |(p : ℝ) / q - P / 3 ^ a| ≤ |x - p / q| + |x - P / 3 ^ a| := by
    calc |(p : ℝ) / q - P / 3 ^ a| = |(x - P / 3 ^ a) - (x - p / q)| := by ring_nf
      _ ≤ |x - P / 3 ^ a| + |x - p / q| := abs_sub _ _
      _ = _ := add_comm _ _
  have e2 : 1 / (2 * (q : ℝ) * 3 ^ a) = 1 / ((q : ℝ) * 3 ^ a) / 2 := by field_simp
  rw [e2]; rw [e2] at hE
  linarith

/-- **Ball mass (Frostman bound for the coin point).**  Confidence 90%.

English proof.  The depth-`n` cylinders of the point (fixing the free coins below `n`) are
intervals `[P/3ⁿ, P/3ⁿ + 3^{−n}]`, `P` with ternary digits in `{0,2}`; two distinct ones are
separated by a gap `≥ 3^{−n}`.  An open interval of length `2r ≤ 2·3^{−(n+1)} < 3^{−n}` meets at
most one of them, and each has coin mass `2^{−F(n)}` (or `0`). -/
theorem coins_ball_le (free : ℕ → Bool) (y r : ℝ) (n : ℕ) (hr : r ≤ 1 / 3 ^ (n + 1)) :
    coins.real {ω | |pt free ω - y| < r} ≤ 2 * (1 / 2 : ℝ) ^ freeCount free n := by
  have := coins_ball_le_gen free y r n hr
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
  have := card_near_le_gen free q m hq hqm r hr
  have h0 := Nat.mul_le_mul_right (2 ^ freeCount free m) (show 3 ≤ 4 by norm_num)
  convert this.trans h0

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
  have hμR : (2 : ℝ) < μ₀ := by exact_mod_cast hμ
  obtain ⟨C, hC⟩ := window_ge_gen μ₀ hμ τ (by linarith)
  refine ⟨C, fun k m h1 h2 => hC k m _ h1 ?_ ?_ ?_⟩
  · have : ((μ₀ : ℝ) - 1) * m ≤ (τ - 1) * m :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  · have h1 : (μ₀ : ℝ) * m ≤ τ * m := mul_le_mul_of_nonneg_right hτ.le (by positivity)
    exact h1.trans (Nat.le_ceil _)
  · have := Nat.ceil_lt_add_one (show 0 ≤ τ * (m : ℝ) by
      have : (0:ℝ) ≤ m := by positivity
      nlinarith)
    exact this.le

/-- **Where the threshold enters.**  The trivial-count block costs `3ᵐ 2^{−(μ₀−2)m}` are summable
exactly above `2 + log₂ 3`.  Confidence 95%.

English proof.  `3 · 2^{−(μ₀−2)} < 1 ⇔ μ₀ − 2 > log₂ 3`; geometric series. -/
theorem summable_bc_of_threshold_lt (μ₀ : ℝ) (hμ : threshold < μ₀) :
    Summable fun m : ℕ => (3 : ℝ) ^ m * (2 : ℝ) ^ (-((μ₀ - 2) * m)) := by
  have hlog : Real.logb 2 3 < μ₀ - 2 := by unfold threshold at hμ; linarith
  have h3 : (3 : ℝ) < 2 ^ (μ₀ - 2) := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) hlog
    rwa [Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)] at this
  have hpos : (0 : ℝ) < 2 ^ (μ₀ - 2) := by positivity
  set ρ : ℝ := 3 * (2 : ℝ) ^ (-(μ₀ - 2))
  have hρ : ρ < 1 := by
    simp only [ρ]; rw [Real.rpow_neg (by norm_num), ← div_eq_mul_inv, div_lt_one hpos]; exact h3
  have hρ0 : 0 ≤ ρ := by positivity
  refine (summable_geometric_of_lt_one hρ0 hρ).congr fun m => ?_
  simp only [ρ]
  rw [mul_pow, ← Real.rpow_natCast ((2:ℝ) ^ (-(μ₀ - 2))), ← Real.rpow_mul (by norm_num)]
  ring_nf

/-! ## The sibling the mechanism must refuse -/

/-- **Structural cap at the entry of a run.**  If the window `(m, n]` reaches into the run
`[a', E')`, its free places are at most `a' − m`.  Confidence 95%.

English proof.  Places in `[a', n)` are forced; `freeCount` counts places `< n`. -/
theorem freeCount_window_le_of_run (μ₀ : ℚ) (k m n : ℕ) (hm : m ≤ expRunStart μ₀ k)
    (hn : n ≤ expRunEnd μ₀ (expRunStart μ₀ k)) :
    freeCount (expFree μ₀) n - freeCount (expFree μ₀) m ≤ expRunStart μ₀ k - m := by
  classical
  set a := expRunStart μ₀ k
  have hka : ∀ i, a ≤ i → i < n → expFree μ₀ i = false := by
    intro i h1 h2
    have hiE : i < expRunEnd μ₀ a := lt_of_lt_of_le h2 hn
    unfold expFree expForced
    simp only [Bool.not_eq_false', List.any_eq_true, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq]
    refine ⟨k, ?_, h1, hiE⟩
    rcases k with _ | k
    · omega
    · have ha0 : a ≠ 0 := by
        intro h0
        simp only [expRunEnd, h0, Nat.cast_zero, mul_zero, Nat.ceil_zero] at hiE
        omega
      have : a = (k + 2) * expRunEnd μ₀ (expRunStart μ₀ k) := rfl
      have hE : 1 ≤ expRunEnd μ₀ (expRunStart μ₀ k) := by
        rcases Nat.eq_zero_or_pos (expRunEnd μ₀ (expRunStart μ₀ k)) with h | h
        · rw [h, mul_zero] at this; exact absurd this ha0
        · exact h
      have : k + 2 ≤ a := by rw [this]; nlinarith
      omega
  have : freeCount (expFree μ₀) n ≤ freeCount (expFree μ₀) m + (a - m) := by
    unfold freeCount
    rw [← Nat.card_Ico m a]
    refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    rcases Nat.lt_or_ge i m with him | him
    · exact Or.inl ⟨him, hi.2⟩
    · right; refine ⟨him, ?_⟩
      by_contra hc
      have := hka i (by omega) hi.1
      rw [hi.2] at this; exact absurd this (by decide)
  omega

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

/-! ## Prefix tests for the exponent

One family of Borel–Cantelli tests `T1 m` (depth `⌈μ₀ m⌉ + √m + 3`, on the Borel–Cantelli range
of `μ₀`) serves every exponent `τ > μ₀` at once; `T2 k` excludes the forced approximation
`P/3^{a_k}` itself (with trailing zeros of `P`); `T3 k` gives the free `2`s. -/

section Tests

variable (μ₀ : ℚ)

/-- Ternary digit `i` read from a coin prefix. -/
def dgt (p : List Bool) (i : ℕ) : ℕ := bif expFree μ₀ i && p.getD i false then 2 else 0

/-- `3ⁿ ·` (head of the point on the first `n` digits). -/
def pnum (p : List Bool) (n : ℕ) : ℕ :=
  ((List.range n).map fun i => dgt μ₀ p i * 3 ^ (n - 1 - i)).sum

/-- Depth of the `m`-th Borel–Cantelli test. -/
def depth (m : ℕ) : ℕ := ⌈μ₀ * m⌉₊ + Nat.sqrt m + 3

/-- Some `r/q`, `q ∈ [3^m, 3^{m+1})`, lies within `2·3^{-n}` of the depth-`n` head. -/
def hitP (m : ℕ) (p : List Bool) : Prop :=
  ∃ q ∈ Finset.Ico (3 ^ m) (3 ^ (m + 1)), ∃ r ∈ Finset.range (q + 1),
    pnum μ₀ p (depth μ₀ m) * q ≤ r * 3 ^ depth μ₀ m + 2 * q ∧
      r * 3 ^ depth μ₀ m ≤ pnum μ₀ p (depth μ₀ m) * q + 2 * q

theorem dgt_pre (ω : ℕ → Bool) {D i : ℕ} (hi : i < D) :
    dgt μ₀ (pre ω D) i = ptDigit (expFree μ₀) ω i := by
  unfold dgt ptDigit; rw [getD_pre ω hi]; cases expFree μ₀ i && ω i <;> rfl

theorem pnum_pre (ω : ℕ → Bool) {D n : ℕ} (hn : n ≤ D) :
    (pnum μ₀ (pre ω D) n : ℝ) / 3 ^ n =
      ∑ i ∈ Finset.range n, (ptDigit (expFree μ₀) ω i : ℝ) / 3 ^ (i + 1) := by
  rw [pnum, ComputableNormalB.list_sum_range_map, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [dgt_pre μ₀ ω (by omega)]; push_cast
  rw [div_eq_div_iff (by positivity) (by positivity), mul_assoc, ← pow_add,
    show n - 1 - i + (i + 1) = n by omega]

theorem pt_le_one (free : ℕ → Bool) (ω : ℕ → Bool) : pt free ω ≤ 1 := by
  obtain ⟨T, -, hT, hx⟩ := pt_split free ω 0
  simp at hx hT; linarith

theorem pt_nonneg (free : ℕ → Bool) (ω : ℕ → Bool) : 0 ≤ pt free ω := by
  obtain ⟨T, hT, -, hx⟩ := pt_split free ω 0
  simp at hx; linarith

theorem le_depth (m : ℕ) (hμ : 1 < μ₀) : m + 3 ≤ depth μ₀ m := by
  have : (m : ℚ) ≤ μ₀ * m := by
    have : (0 : ℚ) ≤ m := by positivity
    nlinarith
  have : m ≤ ⌈μ₀ * m⌉₊ := by exact_mod_cast this.trans (Nat.le_ceil _)
  unfold depth; omega

/-- **A close rational fires the test.** -/
theorem hitP_of_close (hμ : 1 < μ₀) (ω : ℕ → Bool) (m D : ℕ) (hD : depth μ₀ m ≤ D) (q : ℕ)
    (hq : q ∈ Finset.Ico (3 ^ m) (3 ^ (m + 1))) (r : ℤ)
    (h : |cantorExpReal μ₀ ω - r / q| < 1 / 3 ^ depth μ₀ m) : hitP μ₀ m (pre ω D) := by
  set n := depth μ₀ m
  set N := pnum μ₀ (pre ω D) n
  obtain ⟨hq1, hq2⟩ := Finset.mem_Ico.1 hq
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hn := le_depth μ₀ m hμ
  have hqn : q ≤ 3 ^ n := hq2.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hqnR : (q : ℝ) ≤ 3 ^ n := by exact_mod_cast hqn
  have h3n : (0 : ℝ) < 3 ^ n := by positivity
  obtain ⟨T, hT0, hT1, hx⟩ := pt_split (expFree μ₀) ω n
  rw [← pnum_pre μ₀ ω hD] at hx
  have hx' : cantorExpReal μ₀ ω = N / 3 ^ n + T := hx
  have hx0 := pt_nonneg (expFree μ₀) ω
  have hx1 := pt_le_one (expFree μ₀) ω
  have hxe : cantorExpReal μ₀ ω = pt (expFree μ₀) ω := rfl
  have hab := abs_lt.1 h
  have hinv : 1 / (3 : ℝ) ^ n ≤ 1 / q := one_div_le_one_div_of_le hqR hqnR
  -- `0 ≤ r ≤ q`
  have e1 : (q : ℝ) * ((r : ℝ) / q) = r := by field_simp
  have hr0 : 0 ≤ r := by
    have : -(1 / (q : ℝ)) < r / q := by linarith
    have := mul_lt_mul_of_pos_left this hqR
    rw [e1, mul_neg, mul_one_div_cancel hqR.ne'] at this
    have : (-1 : ℤ) < r := by exact_mod_cast this
    omega
  have hrq : r ≤ q := by
    have : (r : ℝ) / q < 1 + 1 / q := by linarith
    have := mul_lt_mul_of_pos_left this hqR
    rw [e1, mul_add, mul_one, mul_one_div_cancel hqR.ne'] at this
    have : r < (q : ℤ) + 1 := by exact_mod_cast this
    omega
  obtain ⟨r', rfl⟩ := Int.eq_ofNat_of_zero_le hr0
  have e2n : (2 : ℝ) / 3 ^ n = 2 * (1 / 3 ^ n) := by ring
  refine ⟨q, hq, r', Finset.mem_range.2 (by omega), ?_, ?_⟩
  · -- `N q ≤ r 3ⁿ + 2q`
    have : (N : ℝ) / 3 ^ n < r' / q + 2 / 3 ^ n := by push_cast at hab; linarith
    have e2 : (N : ℝ) * q = (q * 3 ^ n) * (N / 3 ^ n) := by field_simp
    have e3 : (q * 3 ^ n : ℝ) * (r' / q + 2 / 3 ^ n) = r' * 3 ^ n + 2 * q := by field_simp
    have := mul_lt_mul_of_pos_left this (by positivity : (0:ℝ) < q * 3 ^ n)
    rw [← e2, e3] at this
    exact_mod_cast this.le
  · have : (r' : ℝ) / q < N / 3 ^ n + 2 / 3 ^ n := by push_cast at hab; linarith
    have e2 : (r' : ℝ) * 3 ^ n = (q * 3 ^ n) * (r' / q) := by field_simp
    have e3 : (q * 3 ^ n : ℝ) * (N / 3 ^ n + 2 / 3 ^ n) = N * q + 2 * q := by field_simp
    have := mul_lt_mul_of_pos_left this (by positivity : (0:ℝ) < q * 3 ^ n)
    rw [← e2, e3] at this
    exact_mod_cast this.le

end Tests

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

theorem expRunStart_le_two_freeCount (μ₀ : ℚ) (hμ : 1 < μ₀) (k : ℕ) :
    (expRunStart μ₀ k : ℝ) ≤ 2 * freeCount (expFree μ₀) (expRunStart μ₀ k) := by
  have hF0 : freeCount (expFree μ₀) 0 = 0 := by simp [freeCount]
  rcases k with _ | k
  · have h := le_freeCount_sub (expFree μ₀) (m := 0) (n := expRunStart μ₀ 0) (s := 0)
      (e := expRunStart μ₀ 0) (Nat.zero_le _) le_rfl le_rfl
      (fun i _ hi => expFree_init μ₀ hμ hi)
    rw [hF0] at h; push_cast at h; linarith
  · have h := le_freeCount_sub (expFree μ₀) (m := 0) (n := expRunStart μ₀ (k + 1))
      (s := expRunEnd μ₀ (expRunStart μ₀ k)) (e := expRunStart μ₀ (k + 1)) (Nat.zero_le _)
      (Nat.zero_le _) le_rfl (fun i h1 h2 => expFree_gap μ₀ hμ h1 h2)
    rw [hF0] at h
    have e : (expRunStart μ₀ (k + 1) : ℝ) = (k + 2) * expRunEnd μ₀ (expRunStart μ₀ k) := by
      rw [expRunStart_succ]; push_cast; ring
    have hk : (0 : ℝ) ≤ k * expRunEnd μ₀ (expRunStart μ₀ k) := by positivity
    push_cast at h; rw [e] at h ⊢; nlinarith

/-- **Linear free count.**  Confidence 90%.

English proof.  Below `M`, the forced places lie in runs `[a_j, E_j)` with `E_j ≤ μ₀ a_j + 1`
and `a_{j+1} ≥ (j+2) E_j`; the free places `[E_{j}, a_{j+1})` before the last run reached
outnumber all earlier forced places by the factor `j+1`, so `F(M) ≥ M/(2μ₀ + 4) − 4`. -/
theorem le_freeCount_exp (μ₀ : ℚ) (hμ : 1 < μ₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, c * M ≤ freeCount (expFree μ₀) M + 4 := by
  classical
  have hμR : (1 : ℝ) < μ₀ := by exact_mod_cast hμ
  refine ⟨1 / (2 * μ₀), by positivity, fun M => ?_⟩
  have hF0 : (0 : ℝ) ≤ freeCount (expFree μ₀) M := by positivity
  have hc : 1 / (2 * (μ₀ : ℝ)) * M = (M : ℝ) / (2 * μ₀) := by ring
  rw [hc]
  rcases Nat.lt_or_ge M (expRunStart μ₀ 0) with hM | hM
  · have hM4 : M < 4 := by simpa [expRunStart] using hM
    have : (M : ℝ) < 4 := by exact_mod_cast hM4
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hex : ∃ k, M < expRunStart μ₀ (k + 1) :=
    ⟨M, lt_of_lt_of_le (lt_expRunStart μ₀ hμ (M + 1)) le_rfl |>.trans' (by omega)⟩
  set k := Nat.find hex
  have hk1 : M < expRunStart μ₀ (k + 1) := Nat.find_spec hex
  have hk0 : expRunStart μ₀ k ≤ M := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]; exact hM
    · have hm : ¬ M < expRunStart μ₀ (k - 1 + 1) := Nat.find_min hex (by omega)
      rw [Nat.sub_add_cancel hpos] at hm; omega
  set a := expRunStart μ₀ k
  set E := expRunEnd μ₀ a
  have hEa2 := expRunEnd_le μ₀ hμ a
  have hga := expRunStart_le_two_freeCount μ₀ hμ k
  have hmono : ∀ {x y : ℕ}, x ≤ y → (freeCount (expFree μ₀) x : ℝ) ≤ freeCount (expFree μ₀) y :=
    fun h => by exact_mod_cast freeCount_mono _ h
  have h2μ : (0 : ℝ) < 2 * μ₀ := by positivity
  rw [div_le_iff₀ h2μ]
  rcases le_total M E with hME | hME
  · have h1 := hmono hk0
    have hMR : (M : ℝ) ≤ E := by exact_mod_cast hME
    nlinarith
  · have h1 := le_freeCount_sub (expFree μ₀) hME le_rfl le_rfl
      (fun i h1 h2 => expFree_gap μ₀ hμ (k := k) h1 (lt_of_lt_of_le h2 hk1.le))
    have h2 := hmono (show a ≤ E from (lt_expRunEnd μ₀ hμ (a := a)
      (by have := four_le_expRunStart μ₀ hμ k; omega)).le)
    have hMR : (E : ℝ) ≤ M := by exact_mod_cast hME
    nlinarith

theorem summable_exp_neg_sqrt {α : ℝ} (hα : 0 < α) :
    Summable fun j : ℕ => Real.exp (-α * Real.sqrt j) := by
  have hB := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (ev_log_le (r := 1 / 2)
    (ε := α / 2) (by norm_num) (by positivity))
  refine Summable.of_norm_bounded_eventually summable_inv_sq_nat ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hB, eventually_ge_atTop 1] with j hjB hj1
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← exp_neg_two_log j hj1]
  apply Real.exp_le_exp.2
  rw [Real.sqrt_eq_rpow]; nlinarith

/-- The Cassels bound is summable along `sched` for the exponent schedule. -/
theorem summable_sched_bound_exp (μ₀ : ℚ) (hμ : 1 < μ₀) (C c : ℝ) (hc : 0 < c) :
    Summable fun j => C * (Real.exp (-c * freeCount (expFree μ₀) (Nat.log 3 (sched j) / 2)) +
      (sched j : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨c', hc', hF⟩ := le_freeCount_exp μ₀ hμ
  refine Summable.mul_left C (Summable.add ?_ ?_)
  · have hs := (summable_exp_neg_sqrt (α := c * c' / 4) (by positivity)).mul_left
      (Real.exp (4 * c))
    refine Summable.of_norm_bounded_eventually hs ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [ev_M_ge] with j hj
    set L := Nat.log 3 (sched j) / 2
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 := hF L
    have h2 : c' * (Real.sqrt j / 4) ≤ c' * L := mul_le_mul_of_nonneg_left hj hc'.le
    have h3 : c * (c' * (Real.sqrt j / 4)) ≤ c * (freeCount (expFree μ₀) L + 4) :=
      mul_le_mul_of_nonneg_left (h2.trans h1) hc.le
    nlinarith
  · have := (summable_sched_bound 1 1 one_pos one_pos)
    refine this.of_nonneg_of_le (fun j => by positivity) fun j => ?_
    have : 0 ≤ Real.exp (-1 * (freeCount isFree (Nat.log 3 (sched j) / 2) : ℝ)) := by positivity
    linarith

/-- **Normal to every base prime to 3, a.e.**  Confidence 90%.

English proof.  `CantorLiouvilleAll.ae_isNormal_of_coprime_three` verbatim with `isFree`
replaced by `expFree μ₀`: `secondMoment_le_b (expFree μ₀)` with the linear free count of
`le_freeCount_exp` (stronger than `CantorLiouville.le_freeCount`) makes the bound summable along
`CantorLiouville.sched`, and `ae_isNormal_of_secondMoment` concludes. -/
theorem ae_isNormal_of_coprime_three (μ₀ : ℚ) (hμ : 1 < μ₀) :
    ∀ᵐ ω ∂coins, ∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → IsNormal b (cantorExpReal μ₀ ω) := by
  have hone : ∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → ∀ᵐ ω ∂coins, IsNormal b (cantorExpReal μ₀ ω) := by
    intro b hb h3
    refine CantorLiouvilleAll.ae_isNormal_of_secondMoment coins hb _ (measurable_pt _) sched
      sched_strictMono sched_ratio ?_
    intro h hh
    have hC : (0 : ℝ) < 16 * (b : ℝ) ^ 6 * |(h : ℝ)| := by
      have : (h : ℝ) ≠ 0 := by exact_mod_cast hh
      positivity
    have hl : 0 < Real.log (3 / 2) / 2 := by
      have := Real.log_pos (by norm_num : (1:ℝ) < 3 / 2); linarith
    refine (summable_sched_bound_exp μ₀ hμ (16 * (b : ℝ) ^ 6 * |(h : ℝ)|) _ hl).of_nonneg_of_le
      (fun j => div_nonneg (integral_nonneg fun ω => by positivity) (by positivity))
      (fun j => ?_)
    have hN : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
    rw [div_le_iff₀ (by positivity)]
    calc _ ≤ _ := CantorLiouvilleAll.secondMoment_le_b (expFree μ₀) hb h3 h hh (sched j)
          (one_le_sched j)
      _ = _ := by ring
  rw [ae_all_iff]
  intro b
  by_cases hb : 2 ≤ b
  · by_cases h3 : 3 ∣ b
    · exact Eventually.of_forall fun ω _ h => absurd h3 h
    · filter_upwards [hone b hb h3] with ω hω _ _ using hω
  · exact Eventually.of_forall fun ω h => absurd h hb

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
