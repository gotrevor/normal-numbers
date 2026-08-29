/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.ConditionalDisjunctive

/-!
# Digit runs of `ln 2` and the kick mechanism (Track D, the run tower)

Companion to `docs/lnTwo-kick-blueprint.md`.  The Bailey–Crandall surrogate
`x_{n+1} = fract (2·x_n + 1/(n+1))` differs from the raw doubling orbit by
the **kick** `1/(n+1)` and the strictly positive scaled tail
`τ_n = 2^n·(ln 2 − Σ_{k<n}) ∈ [1/(2(n+1)), 1/(n+1)]`.  This forces
unconditional structure on the binary digits of `ln 2`:

* **Run dictionary** (`occursAt_replicate_zero_iff` / `_one_iff`): a run of
  `k` zeros (ones) at position `n` is exactly the doubling orbit landing in
  `[0, 2⁻ᵏ)` (`[1 − 2⁻ᵏ, 1)`).
* **Sliver dichotomy** (`lnTwoOrbit_top_sliver_of_zeroRun` / `_of_oneRun`,
  sorry-free): any run longer than `log₂ n + 1` pins the *surrogate* to the
  top sliver `x_n ≥ 1 − 2/(n+1)` — the τ-floor kills the bottom channel.
  Probe (2026-08-29, `experiments/lntwo_runs.py`): record runs to 200 000
  bits track `log₂ n` with ratio ≈ 1.0, and every record coincides with a
  surrogate top-sliver visit.
* **Separation interface** (`LnTwoDyadicSep`, `dyadicSep_run_bound`): any
  lower bound `‖2ⁿ·ln 2‖ ≥ f n` caps both run types at `log₂ (1 / f n)`.
  Two instantiations are named, neither proved here:
  `LnTwoExpSep` (Tier 1: exponential separation = an effective dyadic
  irrationality measure; citable, Marcovecchio 2009 gives β ≈ 2.58) and
  `LnTwoPolySep` (Tier 2: polynomial separation, the Mahler-class open
  crux the probe says is true with C ≈ 1).

Everything proved in this file is sorry-free; the two tier hypotheses are
`Prop`s in the repo's named-hypothesis discipline, not axioms.
-/

namespace NormalNumbers

open Filter Set

/-! ### The tail floor -/

/-- **Tail lower bound**: the scaled tail is at least its first term,
`2ⁿ·(ln 2 − Σ_{k<n}) ≥ 1/(2(n+1))`.  Together with `lnTwoTail_le` this
traps `τ_n ∈ [1/(2(n+1)), 1/(n+1)]`. -/
theorem lnTwoTail_ge (n : ℕ) : 1 / (2 * ((n : ℝ) + 1)) ≤ 2 ^ n * lnTwoTail n := by
  set f : ℕ → ℝ := fun k : ℕ => 1 / ((k + 1 : ℝ) * 2 ^ (k + 1)) with hf
  have hsummable : Summable f := hasSum_lnTwoSeries.summable
  have key := hsummable.sum_add_tsum_nat_add n
  have htail : lnTwoTail n = ∑' i : ℕ, f (i + n) := by
    have hpart : lnTwoPartial n = ∑ i ∈ Finset.range n, f i := rfl
    have hlog : Real.log 2 = ∑' i, f i := hasSum_lnTwoSeries.tsum_eq.symm
    rw [lnTwoTail, hpart, hlog, ← key]
    ring
  have hs1 : Summable fun i : ℕ => f (i + n) := (summable_nat_add_iff n).mpr hsummable
  have hterm : f (0 + n) ≤ ∑' i, f (i + n) := by
    refine hs1.le_tsum 0 (fun i _ => ?_)
    simp only [hf]
    positivity
  have hval : f (0 + n) = 1 / (((n : ℝ) + 1) * 2 ^ (n + 1)) := by
    simp [hf]
  rw [htail]
  have hstep : 1 / (2 * ((n : ℝ) + 1)) = 2 ^ n * (1 / (((n : ℝ) + 1) * 2 ^ (n + 1))) := by
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((2 : ℝ) ^ (n + 1)) ≠ 0 := by positivity
    field_simp
    ring
  rw [hstep]
  exact mul_le_mul_of_nonneg_left (hval ▸ hterm) (by positivity)

/-! ### The run dictionary -/

theorem blockNatVal_replicate_zero (b k : ℕ) :
    blockNatVal b (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, blockNatVal_cons, ih]; simp

theorem blockNatVal_replicate_one (k : ℕ) :
    blockNatVal 2 (List.replicate k 1) = 2 ^ k - 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, blockNatVal_cons, ih, List.length_replicate]
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega

private theorem replicate_digits_lt (k d : ℕ) (hd : d < 2) :
    ∀ e ∈ List.replicate k d, e < 2 := by
  intro e he
  rw [List.eq_of_mem_replicate he]
  exact hd

/-- **A run of `k` zeros at position `n` is an orbit visit to `[0, 2⁻ᵏ)`.** -/
theorem occursAt_replicate_zero_iff (x : ℝ) (n k : ℕ) :
    OccursAt 2 x (List.replicate k 0) n ↔
      orbit 2 x n ∈ Set.Ico (0 : ℝ) (1 / 2 ^ k) := by
  rw [occursAt_iff_orbit_mem 2 le_rfl x _ (replicate_digits_lt k 0 (by norm_num)) n,
    blockNatVal_replicate_zero, List.length_replicate]
  norm_num

/-- **A run of `k` ones at position `n` is an orbit visit to `[1 − 2⁻ᵏ, 1)`.** -/
theorem occursAt_replicate_one_iff (x : ℝ) (n k : ℕ) :
    OccursAt 2 x (List.replicate k 1) n ↔
      orbit 2 x n ∈ Set.Ico (1 - 1 / 2 ^ k : ℝ) 1 := by
  rw [occursAt_iff_orbit_mem 2 le_rfl x _ (replicate_digits_lt k 1 (by norm_num)) n,
    blockNatVal_replicate_one, List.length_replicate]
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hcast : ((2 ^ k - 1 : ℕ) : ℝ) = 2 ^ k - 1 := by
    push_cast [h1]
    ring
  have hpow : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  rw [hcast]
  have e1 : ((2 : ℝ) ^ k - 1) / ((2 : ℕ) : ℝ) ^ k = 1 - 1 / 2 ^ k := by
    push_cast
    field_simp
  have e2 : (((2 : ℝ) ^ k - 1) + 1) / ((2 : ℕ) : ℝ) ^ k = 1 := by
    push_cast
    rw [sub_add_cancel]
    exact div_self (by positivity)
  rw [e1, e2]

/-! ### The sliver dichotomy (sorry-free) -/

/-- **Zero-run dichotomy**: a run of `k` zeros at position `n` with
`2ᵏ > 2(n+1)` forces the surrogate into the top sliver
`x_n ≥ 1 − 1/(n+1)`.  (Without the wraparound the orbit point is
`x_n + τ_n ≥ τ_n ≥ 1/(2(n+1))`, too large for the run.) -/
theorem lnTwoOrbit_top_sliver_of_zeroRun {n k : ℕ}
    (hk : 2 * ((n : ℝ) + 1) < 2 ^ k)
    (h : OccursAt 2 (Real.log 2) (List.replicate k 0) n) :
    1 - 1 / ((n : ℝ) + 1) ≤ lnTwoOrbit n := by
  rw [occursAt_replicate_zero_iff, orbit_log_two_eq] at h
  set x := lnTwoOrbit n with hx_def
  set τ := 2 ^ n * lnTwoTail n with hτ_def
  have hτ0 : 0 ≤ τ := pow_mul_lnTwoTail_nonneg n
  have hτle : τ ≤ 1 / ((n : ℝ) + 1) := lnTwoTail_le n
  have hτge : 1 / (2 * ((n : ℝ) + 1)) ≤ τ := lnTwoTail_ge n
  have hx01 := lnTwoOrbit_mem_Ico n
  rcases lt_or_ge (x + τ) 1 with hlt | hge
  · exfalso
    rw [Int.fract_eq_self.mpr ⟨add_nonneg hx01.1 hτ0, hlt⟩] at h
    have hsmall : (1 : ℝ) / 2 ^ k < 1 / (2 * ((n : ℝ) + 1)) :=
      one_div_lt_one_div_of_lt (by positivity) hk
    linarith [h.2, hx01.1]
  · linarith

/-- **One-run dichotomy**: for `n ≥ 1`, a run of `k` ones at position `n`
with `2ᵏ > 2(n+1)` forces the surrogate into the top sliver
`x_n ≥ 1 − 2/(n+1)`.  (A wraparound would leave the orbit point at
`≤ τ_n ≤ 1/(n+1)`, too small for the run; without one,
`x_n = orbit − τ_n` is within `2/(n+1)` of `1`.) -/
theorem lnTwoOrbit_top_sliver_of_oneRun {n k : ℕ} (hn : 1 ≤ n)
    (hk : 2 * ((n : ℝ) + 1) < 2 ^ k)
    (h : OccursAt 2 (Real.log 2) (List.replicate k 1) n) :
    1 - 2 / ((n : ℝ) + 1) ≤ lnTwoOrbit n := by
  rw [occursAt_replicate_one_iff, orbit_log_two_eq] at h
  set x := lnTwoOrbit n with hx_def
  set τ := 2 ^ n * lnTwoTail n with hτ_def
  have hτ0 : 0 ≤ τ := pow_mul_lnTwoTail_nonneg n
  have hτle : τ ≤ 1 / ((n : ℝ) + 1) := lnTwoTail_le n
  have hx01 := lnTwoOrbit_mem_Ico n
  have hsmall : (1 : ℝ) / 2 ^ k < 1 / (2 * ((n : ℝ) + 1)) :=
    one_div_lt_one_div_of_lt (by positivity) hk
  have hhalf : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 / ((n : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have htwo : 2 / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1)) := by ring
  rcases lt_or_ge (x + τ) 1 with hlt | hge
  · rw [Int.fract_eq_self.mpr ⟨add_nonneg hx01.1 hτ0, hlt⟩] at h
    have h1 : 1 - 1 / 2 ^ k ≤ x + τ := h.1
    linarith
  · exfalso
    have hn1 : (2 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hq : 1 / ((n : ℝ) + 1) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hn1
    have hfr : Int.fract (x + τ) = x + τ - 1 := by
      have hlt2 : x + τ - 1 < 1 := by linarith [hx01.2, hτle, hq]
      have h2 : x + τ - 1 + ((1 : ℤ) : ℝ) = x + τ := by push_cast; ring
      rw [← h2, Int.fract_add_intCast,
        Int.fract_eq_self.mpr ⟨by linarith, hlt2⟩]
      push_cast
      ring
    rw [hfr] at h
    have h1 : 1 - 1 / 2 ^ k ≤ x + τ - 1 := h.1
    have hub : x + τ - 1 ≤ 1 / ((n : ℝ) + 1) := by linarith [hx01.2]
    have hq2 : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 / 4 := by
      apply one_div_le_one_div_of_le (by norm_num)
      linarith
    linarith

/-! ### The separation interface and the two frozen tiers -/

/-- `‖2ⁿ·ln 2‖`: the distance of the doubling orbit of `ln 2` to the wrap
point — equivalently the distance of `2ⁿ·ln 2` to the nearest integer. -/
noncomputable def lnTwoNorm (n : ℕ) : ℝ :=
  min (orbit 2 (Real.log 2) n) (1 - orbit 2 (Real.log 2) n)

/-- A dyadic separation bound for `ln 2`: `‖2ⁿ·ln 2‖ ≥ f n` for `n ≥ N₀`.
The interface every run-length theorem consumes. -/
def LnTwoDyadicSep (f : ℕ → ℝ) (N₀ : ℕ) : Prop :=
  ∀ n, N₀ ≤ n → f n ≤ lnTwoNorm n

/-- **Wiring**: a dyadic separation bound caps both run types — a run of
`k` zeros or ones at position `n ≥ N₀` forces `f n ≤ 2⁻ᵏ`, i.e.
`k ≤ log₂ (1 / f n)`. -/
theorem dyadicSep_run_bound {f : ℕ → ℝ} {N₀ : ℕ}
    (hsep : LnTwoDyadicSep f N₀) {n k : ℕ} (hn : N₀ ≤ n)
    (h : OccursAt 2 (Real.log 2) (List.replicate k 0) n ∨
         OccursAt 2 (Real.log 2) (List.replicate k 1) n) :
    f n ≤ 1 / 2 ^ k := by
  have hs := hsep n hn
  rcases h with h | h
  · rw [occursAt_replicate_zero_iff] at h
    exact hs.trans ((min_le_left _ _).trans h.2.le)
  · rw [occursAt_replicate_one_iff] at h
    refine hs.trans ((min_le_right _ _).trans ?_)
    linarith [h.1]

/-- **Tier 1 (Diophantine; believed citable, NOT proved here).**
Exponential dyadic separation `‖2ⁿ·ln 2‖ ≥ 2^(−βn)` — the dyadic shadow of
an effective irrationality measure `μ(ln 2) ≤ 1 + β`.  Marcovecchio 2009
(`μ(ln 2) ≤ 3.5746`) makes `β = 2.58` admissible for some `N₀`; the
Alladi–Robinson / shifted-Legendre construction (already partially built in
`collatz-moonshot`'s `FrontA/Legendre.lean`) reaches `β ≈ 3.63` and is a
candidate for an in-house proof.  Consequence (`dyadicSep_run_bound`): runs
at position `n` have length `≤ βn + O(1)` — apparently the first
quantitative digit statement for `ln 2` beyond irrationality (novelty
unswept). -/
def LnTwoExpSep (β : ℝ) (N₀ : ℕ) : Prop :=
  LnTwoDyadicSep (fun n => (2 : ℝ) ^ (-(β * n))) N₀

/-- **Tier 2 (the run crux — Mahler-class, OPEN).**
Polynomial dyadic separation `‖2ⁿ·ln 2‖ ≥ (n+2)^(−C)`.  Empirically true
with `C ≈ 1`: the 200 000-bit probe's record runs track `log₂ n` at ratio
≈ 1.0 (`experiments/lntwo_runs.py`, 2026-08-29).  This is the same family
as Mahler's `‖(3/2)ⁿ‖` problem and is NOT reachable from any irrationality
measure (those give only Tier 1).  Consequence: every run at position `n`
has length `≤ C·log₂ n + O(1)` — the random-like run behavior the data
shows. -/
def LnTwoPolySep (C : ℝ) (N₀ : ℕ) : Prop :=
  LnTwoDyadicSep (fun n => ((n : ℝ) + 2) ^ (-C)) N₀

/-- Tier 1 consequence in closed form: runs are linearly bounded,
`k ≤ β·n`, once `n ≥ max N₀ 1`. -/
theorem run_le_of_expSep {β : ℝ} {N₀ : ℕ}
    (hsep : LnTwoExpSep β N₀) {n k : ℕ} (hn : N₀ ≤ n)
    (h : OccursAt 2 (Real.log 2) (List.replicate k 0) n ∨
         OccursAt 2 (Real.log 2) (List.replicate k 1) n) :
    (k : ℝ) ≤ β * n := by
  have hb := dyadicSep_run_bound hsep hn h
  have e2 : (1 : ℝ) / 2 ^ k = (2 : ℝ) ^ (-(k : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    exact (one_div _)
  rw [e2] at hb
  have := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hb
  linarith

/-- Tier 2 consequence in closed form: runs are logarithmically bounded,
`k ≤ C·log₂(n+2)`. -/
theorem run_le_of_polySep {C : ℝ} {N₀ : ℕ}
    (hsep : LnTwoPolySep C N₀) {n k : ℕ} (hn : N₀ ≤ n)
    (h : OccursAt 2 (Real.log 2) (List.replicate k 0) n ∨
         OccursAt 2 (Real.log 2) (List.replicate k 1) n) :
    (k : ℝ) ≤ C * Real.logb 2 ((n : ℝ) + 2) := by
  have hb := dyadicSep_run_bound hsep hn h
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have e1 : ((n : ℝ) + 2) ^ (-C)
      = (2 : ℝ) ^ (Real.logb 2 ((n : ℝ) + 2) * (-C)) := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num) (by norm_num) hn2]
  have e2 : (1 : ℝ) / 2 ^ k = (2 : ℝ) ^ (-(k : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    exact (one_div _)
  rw [e1, e2] at hb
  have hexp := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hb
  nlinarith [hexp]

end NormalNumbers
