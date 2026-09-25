/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.SwingC3Mean
import NormalNumbers.PrimeLambertTail

/-!
# The shape of the C3 crux: a `log log N`-point correlation, not an `N`-point one

`weylLambertTwist_holds` (`SwingC3Leaf.lean`) is the open leaf

    (1/N) ∑_{n<N} e(jn/Q) · e(h · L_P · b^n)  →  0,      L_P = ∑_{p>P} 1/(b^p − 1).

By `ee_tailLarge_eq_ee_orbit` the exponential is `e(h · tailLarge P b n)` with

    tailLarge P b n = ∑_{i≥0} ω_{>P}(n+i+1) / b^{i+1}                       (`SwingC3Split`)

a **vertical** sum over digit depth `i`.  All earlier laps truncated *horizontally*, at a prime
cutoff `K` (`tailTrunc`), which buys `∏_{P<p≤K} p`-periodicity but costs discarded mass
`≍ N ∑_{K<p} 1/p`; `sum_range_tailTrunc_sub_le` prices that, and the resulting window
`log N ≪ K ≪ N` is what the leaf's docstring records as missing.

This file makes the **orthogonal** truncation, at digit depth `D`, and prices it.  The point:

> the depth-`D` truncation error is `≪ (log N + D)/b^D` **pointwise** on `n < N`, so depth
> `D ≍ log_b log N` is already free.

That collapses the required correlation length from `N` to `log log N`:

* `tailLarge_sub_tailDepth_le` / `tailLarge_sub_tailDepth_le_of_lt` — the pointwise price.
* `ee_tailDepth_eq_prod` — at depth `D` the phase is *exactly* a `D`-point root-of-unity
  correlation `∏_{i<D} ζ_i^{ω_{>P}(n+i+1)}`, `ζ_i = e(h/b^{i+1})`, of the multiplicative
  functions `ζ_i^{ω_{>P}}`.
* `DepthElliott` — the named Prop this reduces the leaf to: an Elliott-type bound for that
  twisted `D`-point correlation, needed only along a depth schedule `D = D_N → ∞` with
  `b^{D_N} ≥ (log₂ N + 1)^2`, i.e. `D_N = O(log log N)`.
* `weylLambertTwist_of_depthElliott` — the reduction.

## Why the twist `e(jn/Q)` is not the source of cancellation

`ζ_0^{ω_{>P}}` has, on every prime `p > P`, the constant value `ζ_0 = e(h/b) ≠ 1` (for
`b ∤ h`), so `∑_p (1 − Re ζ_0)/p = ∞`: it is non-pretentious in the Halász sense, and
Selberg–Delange already gives `(1/N)∑_{n≤N} ζ_0^{ω_{>P}(n)} ≍ (log N)^{Re ζ_0 − 1} → 0`.
The predicted decay of the *full* phase is therefore

    (log N)^{−a(b,h)},   a(b,h) = ∑_{i≥1} (1 − cos(2π h / b^i)) < ∞,

a finite positive constant because `1 − cos(2πh/b^i) ≍ b^{−2i}`.  This matches the measured
`(log N)^{−a}`, `a ≈ 1.3–3.7`, of `probes/swingc3_weyl_lambert_twist.py`.  So the hypothesis
`0 < j < Q` is **not** load-bearing: the leaf should be true at `j = 0` as well, and no
CRT/periodicity argument in `Q` can supply the cancellation.  The cancellation is entirely
non-pretentiousness of `ζ_0^{ω_{>P}}`, and the obstruction is the *joint* behaviour of the
`D` shifted copies — an Elliott correlation.
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

open PrimeLambert

/-! ### `ω_{>P}` is at most `log₂` -/

lemma omegaLarge_le_card (P m : ℕ) : omegaLarge P m ≤ m.primeFactors.card :=
  Finset.card_filter_le _ _

lemma omegaLarge_le_log (P m : ℕ) : omegaLarge P m ≤ Nat.log 2 m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [omegaLarge]
  exact (omegaLarge_le_card P m).trans (card_primeFactors_le_log m hm)

/-- `log₂(n + i + 1) ≤ log₂(n+1) + i`: the digit at depth `i` above `n` is only `i` bits
deeper than the one at `n`. -/
lemma log_two_shift_le (n i : ℕ) : Nat.log 2 (n + i + 1) ≤ Nat.log 2 (n + 1) + i := by
  have hlt : n + 1 < 2 ^ (Nat.log 2 (n + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hstep : n + i + 1 < 2 ^ (Nat.log 2 (n + 1) + i + 1) := by
    have hi : i + 1 ≤ 2 ^ i := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
    have h1 : n + i + 1 ≤ (n + 1) * 2 ^ i := by
      calc n + i + 1 ≤ (n + 1) * (i + 1) := by nlinarith
        _ ≤ (n + 1) * 2 ^ i := Nat.mul_le_mul_left _ hi
    have h2 : (n + 1) * 2 ^ i < 2 ^ (Nat.log 2 (n + 1) + 1) * 2 ^ i :=
      mul_lt_mul_of_pos_right hlt (pow_pos (by norm_num : (0:ℕ) < 2) i)
    calc n + i + 1 ≤ (n + 1) * 2 ^ i := h1
      _ < 2 ^ (Nat.log 2 (n + 1) + 1) * 2 ^ i := h2
      _ = 2 ^ (Nat.log 2 (n + 1) + i + 1) := by rw [← pow_add]; ring_nf
  have := Nat.log_lt_of_lt_pow (y := n + i + 1) (by omega) hstep
  omega

/-! ### The vertical truncation and its price -/

/-- **Vertical truncation**: the large-prime tail cut at digit depth `D`. -/
noncomputable def tailDepth (P b D n : ℕ) : ℝ :=
  ∑ i ∈ range D, (omegaLarge P (n + i + 1) : ℝ) / (b : ℝ) ^ (i + 1)

lemma tailLarge_sub_tailDepth_eq {b : ℕ} (hb : 2 ≤ b) (P D n : ℕ) :
    tailLarge P b n - tailDepth P b D n
      = ∑' i : ℕ, (omegaLarge P (n + (i + D) + 1) : ℝ) / (b : ℝ) ^ ((i + D) + 1) := by
  have hs := summable_tailLarge hb P n
  have := hs.sum_add_tsum_nat_add D
  rw [tailLarge, tailDepth, ← this]
  ring

/-- **The price of the vertical truncation.**  Cutting the large-prime tail at digit depth `D`
costs at most `(log₂(n+1) + D + 1)/((b−2) b^D)` — *pointwise* in `n`, and only logarithmically
in `n`.  Contrast `sum_range_tailTrunc_sub_le`, the horizontal (prime-cutoff) price, which is
`≍ N ∑_{K<p} 1/p` and forces `K ≳ N`. -/
theorem tailLarge_sub_tailDepth_le {b : ℕ} (hb : 3 ≤ b) (P D n : ℕ) :
    tailLarge P b n - tailDepth P b D n
      ≤ ((Nat.log 2 (n + 1) : ℝ) + D + 1) / (((b : ℝ) - 2) * (b : ℝ) ^ D) := by
  have hb2 : 2 ≤ b := by omega
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  set L : ℕ := Nat.log 2 (n + 1) with hL
  set c : ℝ := ((L : ℝ) + D + 1) / (b : ℝ) ^ (D + 1) with hc
  have hcpos : 0 ≤ c := by
    rw [hc]; positivity
  have hr : (0 : ℝ) ≤ 2 / (b : ℝ) := by positivity
  have hr1 : 2 / (b : ℝ) < 1 := by
    rw [div_lt_one hb0]; linarith
  have hgsum : Summable (fun i : ℕ => c * (2 / (b : ℝ)) ^ i) :=
    (summable_geometric_of_lt_one hr hr1).mul_left c
  have hfsum : Summable (fun i : ℕ =>
      (omegaLarge P (n + (i + D) + 1) : ℝ) / (b : ℝ) ^ ((i + D) + 1)) := by
    have := (summable_nat_add_iff D).2 (summable_tailLarge hb2 P n)
    exact this.congr fun i => by ring_nf
  have hterm : ∀ i : ℕ, (omegaLarge P (n + (i + D) + 1) : ℝ) / (b : ℝ) ^ ((i + D) + 1)
      ≤ c * (2 / (b : ℝ)) ^ i := by
    intro i
    have h1 : omegaLarge P (n + (i + D) + 1) ≤ L + (i + D) := by
      refine (omegaLarge_le_log P _).trans ?_
      have := log_two_shift_le n (i + D)
      omega
    have h2 : ((L : ℝ) + (i + D)) ≤ ((L : ℝ) + D + 1) * 2 ^ i := by
      have hi : ((i : ℝ) + 1) ≤ 2 ^ i := by
        have hn : i + 1 ≤ 2 ^ i := Nat.succ_le_of_lt Nat.lt_two_pow_self
        calc ((i : ℝ) + 1) = ((i + 1 : ℕ) : ℝ) := by push_cast; ring
          _ ≤ ((2 ^ i : ℕ) : ℝ) := by exact_mod_cast hn
          _ = (2 : ℝ) ^ i := by push_cast; ring
      have hLD : (0 : ℝ) ≤ (L : ℝ) + D := by positivity
      nlinarith [hLD, hi]
    have h3 : (omegaLarge P (n + (i + D) + 1) : ℝ) ≤ ((L : ℝ) + D + 1) * 2 ^ i := by
      refine le_trans ?_ h2
      have : (omegaLarge P (n + (i + D) + 1) : ℝ) ≤ ((L + (i + D) : ℕ) : ℝ) := by
        exact_mod_cast h1
      push_cast at this ⊢; linarith
    have hpow : (b : ℝ) ^ ((i + D) + 1) = (b : ℝ) ^ (D + 1) * (b : ℝ) ^ i := by
      rw [← pow_add]; ring_nf
    have hrhs : ((L : ℝ) + D + 1) / (b : ℝ) ^ (D + 1) * ((2 : ℝ) / (b : ℝ)) ^ i
        = (((L : ℝ) + D + 1) * 2 ^ i) / ((b : ℝ) ^ (D + 1) * (b : ℝ) ^ i) := by
      rw [div_pow, div_mul_div_comm]
    rw [hc, hpow, hrhs]
    exact (div_le_div_iff_of_pos_right (by positivity)).2 h3
  rw [tailLarge_sub_tailDepth_eq hb2 P D n]
  calc ∑' i : ℕ, (omegaLarge P (n + (i + D) + 1) : ℝ) / (b : ℝ) ^ ((i + D) + 1)
      ≤ ∑' i : ℕ, c * (2 / (b : ℝ)) ^ i := hfsum.tsum_le_tsum hterm hgsum
    _ = c * (1 - 2 / (b : ℝ))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr1]
    _ = ((L : ℝ) + D + 1) / (((b : ℝ) - 2) * (b : ℝ) ^ D) := by
        rw [hc]
        have hne : (b : ℝ) - 2 ≠ 0 := by linarith
        field_simp
        ring

/-- The price, uniform over the window `n < N`. -/
theorem tailLarge_sub_tailDepth_le_of_lt {b : ℕ} (hb : 3 ≤ b) (P D N n : ℕ) (hn : n < N) :
    tailLarge P b n - tailDepth P b D n
      ≤ ((Nat.log 2 N : ℝ) + D + 1) / (((b : ℝ) - 2) * (b : ℝ) ^ D) := by
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  refine (tailLarge_sub_tailDepth_le hb P D n).trans ?_
  have hmono : Nat.log 2 (n + 1) ≤ Nat.log 2 N := Nat.log_mono_right (by omega)
  have : ((Nat.log 2 (n + 1) : ℝ)) ≤ (Nat.log 2 N : ℝ) := by exact_mod_cast hmono
  have hd : (0 : ℝ) < ((b : ℝ) - 2) * (b : ℝ) ^ D := mul_pos (by linarith) (by positivity)
  exact (div_le_div_iff_of_pos_right hd).2 (by linarith)

theorem tailLarge_sub_tailDepth_nonneg {b : ℕ} (hb : 2 ≤ b) (P D n : ℕ) :
    0 ≤ tailLarge P b n - tailDepth P b D n := by
  rw [tailLarge_sub_tailDepth_eq hb P D n]
  refine tsum_nonneg fun i => by positivity

/-! ### At depth `D` the phase is exactly a `D`-point root-of-unity correlation -/

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ee (∑ i ∈ s, f i) = ∏ i ∈ s, ee (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [ee_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ee_add, ih]

lemma ee_nat_mul (k : ℕ) (x : ℂ) : ee ((k : ℂ) * x) = ee x ^ k := by
  induction k with
  | zero => simp [ee_zero]
  | succ k ih => push_cast; rw [add_mul, ee_add, ih, one_mul]; ring

/-- `ζ_i = e(h / b^{i+1})`: the root of unity carried by the digit at depth `i`. -/
noncomputable def depthRoot (b : ℕ) (h : ℤ) (i : ℕ) : ℂ :=
  ee ((((h : ℝ) / (b : ℝ) ^ (i + 1) : ℝ) : ℂ))

/-- **The depth-`D` phase is a `D`-point correlation of the multiplicative functions
`ζ_i^{ω_{>P}}` along the `D` consecutive shifts `n+1, …, n+D`.**  This is the machine-checked
identification of the C3 crux as an Elliott-type correlation. -/
theorem ee_tailDepth_eq_prod (b P D n : ℕ) (h : ℤ) :
    ee ((((h : ℝ) * tailDepth P b D n : ℝ) : ℂ))
      = ∏ i ∈ range D, depthRoot b h i ^ omegaLarge P (n + i + 1) := by
  have hpush : (((h : ℝ) * tailDepth P b D n : ℝ) : ℂ)
      = ∑ i ∈ range D, ((omegaLarge P (n + i + 1) : ℂ)
          * (((h : ℝ) / (b : ℝ) ^ (i + 1) : ℝ) : ℂ)) := by
    rw [tailDepth, Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hpush, ee_sum]
  exact Finset.prod_congr rfl fun i _ => by rw [ee_nat_mul]; rfl

/-! ### The depth schedule: `D_N ≍ log_b log N`, and the truncation error along it -/

/-- `D_N = 2(⌊log_b(log₂ N + 1)⌋ + 1)`: the depth schedule.  It is `O(log log N)` and satisfies
`b^{D_N} ≥ (log₂ N + 1)²`, which is what makes the truncation error `O(1/log N)`. -/
def depthSchedule (b N : ℕ) : ℕ := 2 * (Nat.log b (Nat.log 2 N + 1) + 1)

lemma sq_log_le_pow_depthSchedule {b : ℕ} (hb : 3 ≤ b) (N : ℕ) :
    ((Nat.log 2 N : ℝ) + 1) ^ 2 ≤ (b : ℝ) ^ depthSchedule b N := by
  have hb1 : 1 < b := by omega
  have key : Nat.log 2 N + 1 < b ^ (Nat.log b (Nat.log 2 N + 1) + 1) :=
    Nat.lt_pow_succ_log_self hb1 _
  have keyR : ((Nat.log 2 N : ℝ) + 1) ≤ (b : ℝ) ^ (Nat.log b (Nat.log 2 N + 1) + 1) := by
    have : ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ ((b ^ (Nat.log b (Nat.log 2 N + 1) + 1) : ℕ) : ℝ) := by
      exact_mod_cast key.le
    push_cast at this; linarith
  have hnn : (0 : ℝ) ≤ (Nat.log 2 N : ℝ) + 1 := by positivity
  calc ((Nat.log 2 N : ℝ) + 1) ^ 2
      ≤ ((b : ℝ) ^ (Nat.log b (Nat.log 2 N + 1) + 1)) ^ 2 := by gcongr
    _ = (b : ℝ) ^ depthSchedule b N := by
        rw [depthSchedule, ← pow_mul]; ring_nf

/-- **The truncation error along the schedule is `O(1/log N)`.** -/
theorem depthSchedule_err_le {b : ℕ} (hb : 3 ≤ b) (N : ℕ) :
    ((Nat.log 2 N : ℝ) + depthSchedule b N + 1)
        / (((b : ℝ) - 2) * (b : ℝ) ^ depthSchedule b N)
      ≤ 3 / ((Nat.log 2 N : ℝ) + 1) := by
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  set L : ℕ := Nat.log 2 N with hLdef
  set D : ℕ := depthSchedule b N with hDdef
  have hD : D ≤ 2 * (L + 1) := by
    rw [hDdef, depthSchedule, ← hLdef]
    have := Nat.log_lt_self b (show L + 1 ≠ 0 by omega)
    omega
  have hDR : (D : ℝ) ≤ 2 * ((L : ℝ) + 1) := by
    have : ((D : ℕ) : ℝ) ≤ ((2 * (L + 1) : ℕ) : ℝ) := by exact_mod_cast hD
    push_cast at this; linarith
  have hnum : (L : ℝ) + D + 1 ≤ 3 * ((L : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (L : ℝ) := by positivity
    linarith
  have hsq : ((L : ℝ) + 1) ^ 2 ≤ (b : ℝ) ^ D := by
    rw [hDdef, hLdef]; exact sq_log_le_pow_depthSchedule hb N
  have hden : ((L : ℝ) + 1) ^ 2 ≤ ((b : ℝ) - 2) * (b : ℝ) ^ D := by
    nlinarith [pow_pos (show (0:ℝ) < (b:ℝ) by linarith) D]
  have hL1 : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  calc ((L : ℝ) + D + 1) / (((b : ℝ) - 2) * (b : ℝ) ^ D)
      ≤ ((L : ℝ) + D + 1) / (((L : ℝ) + 1) ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ ≤ (3 * ((L : ℝ) + 1)) / (((L : ℝ) + 1) ^ 2) :=
        (div_le_div_iff_of_pos_right (by positivity)).2 hnum
    _ = 3 / ((L : ℝ) + 1) := by
        rw [sq]; field_simp

/-! ### The named reduction target -/

/-- The depth-`D` twisted correlation average. -/
noncomputable def depthAvg (b P Q j : ℕ) (h : ℤ) (D N : ℕ) : ℂ :=
  (∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ) : ℂ))
    * ee ((((h : ℝ) * tailDepth P b D n : ℝ) : ℂ))) / N

/-- **What the C3 crux needs.**  An Elliott-type bound for the twisted `D`-point correlation
`(1/N) ∑_{n<N} e(jn/Q) ∏_{i<D} ζ_i^{ω_{>P}(n+i+1)}`, `ζ_i = e(h/b^{i+1})`, along the depth
schedule `D = D_N = O(log log N)`.

This is *not* a fixed-`D` statement, and it cannot be: for fixed `D` the discarded phase
`h ∑_{i≥D} ω_{>P}(n+i+1)/b^{i+1}` has typical size `≍ log log N / b^D → ∞`, so no bounded number
of points suffices.  What is needed is Elliott's conjecture **with uniformity in the number of
points**, the number growing like `log log N`.  Tao's `unitCircleLogElliott` (two points, log
density) and Tao–Teräväinen (odd order, log density) give fixed point counts only; that gap —
uniformity in `k` — is precisely the remaining obstruction. -/
def DepthElliott (b : ℕ) : Prop :=
  ∀ (P Q j : ℕ) (h : ℤ), 0 < Q → 0 < j → j < Q →
    Tendsto (fun N : ℕ => depthAvg b P Q j h (depthSchedule b N) N) atTop (𝓝 0)

private lemma tendsto_log_two_atTop : Tendsto (fun N : ℕ => Nat.log 2 N) atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  refine eventually_atTop.2 ⟨2 ^ M, fun N hN => ?_⟩
  exact Nat.le_log_of_pow_le (by norm_num) hN

private lemma tendsto_depthErr {b : ℕ} (hb : 3 ≤ b) (C : ℝ) :
    Tendsto (fun N : ℕ => C * (((Nat.log 2 N : ℝ) + depthSchedule b N + 1)
      / (((b : ℝ) - 2) * (b : ℝ) ^ depthSchedule b N))) atTop (𝓝 0) := by
  have h3 : Tendsto (fun N : ℕ => C * (3 / ((Nat.log 2 N : ℝ) + 1))) atTop (𝓝 0) := by
    have hbase : Tendsto (fun N : ℕ => 3 / ((Nat.log 2 N : ℝ) + 1)) atTop (𝓝 0) := by
      have : Tendsto (fun N : ℕ => ((Nat.log 2 N : ℝ) + 1)) atTop atTop := by
        refine tendsto_atTop_add_const_right _ 1 ?_
        exact tendsto_natCast_atTop_atTop.comp tendsto_log_two_atTop
      simpa [div_eq_mul_inv, mul_comm] using this.inv_tendsto_atTop.const_mul (3 : ℝ)
    simpa using hbase.const_mul C
  refine squeeze_zero_norm' ?_ (by simpa using h3.norm)
  filter_upwards [] with N
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hnn : (0 : ℝ) ≤ ((Nat.log 2 N : ℝ) + depthSchedule b N + 1)
      / (((b : ℝ) - 2) * (b : ℝ) ^ depthSchedule b N) := by
    have : (0 : ℝ) < ((b : ℝ) - 2) * (b : ℝ) ^ depthSchedule b N :=
      mul_pos (by linarith) (by positivity)
    positivity
  have hle := depthSchedule_err_le hb N
  have h3nn : (0 : ℝ) ≤ 3 / ((Nat.log 2 N : ℝ) + 1) := by positivity
  have habs : |((Nat.log 2 N : ℝ) + 1)| = (Nat.log 2 N : ℝ) + 1 :=
    abs_of_nonneg (by positivity)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn, habs]
  exact mul_le_mul_of_nonneg_left hle (abs_nonneg C)

/-- **The reduction.**  `DepthElliott b` implies the C3 crux `WeylLambertTwist b`. -/
theorem weylLambertTwist_of_depthElliott {b : ℕ} (hb : 3 ≤ b) (H : DepthElliott b) :
    WeylLambertTwist b := by
  intro P Q j h hQ hj0 hjQ
  have hb2 : 2 ≤ b := by omega
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  set E : ℕ → ℝ := fun N => ((Nat.log 2 N : ℝ) + depthSchedule b N + 1)
    / (((b : ℝ) - 2) * (b : ℝ) ^ depthSchedule b N) with hE
  have hEnn : ∀ N, 0 ≤ E N := by
    intro N
    have : (0 : ℝ) < ((b : ℝ) - 2) * (b : ℝ) ^ depthSchedule b N :=
      mul_pos (by linarith) (by positivity)
    rw [hE]; positivity
  set A : ℕ → ℂ := fun N => (∑ n ∈ range N, ee ((((j : ℝ) * n / Q : ℝ) : ℂ))
    * ee ((((h : ℝ) * tailLarge P b n : ℝ) : ℂ))) / N with hA
  have hnorm : ∀ N : ℕ, ‖A N - depthAvg b P Q j h (depthSchedule b N) N‖
      ≤ 16 * |(h : ℝ)| * E N := by
    intro N
    have hterm : ∀ n ∈ range N,
        ‖ee ((((j : ℝ) * n / Q : ℝ) : ℂ)) * ee ((((h : ℝ) * tailLarge P b n : ℝ) : ℂ))
          - ee ((((j : ℝ) * n / Q : ℝ) : ℂ))
            * ee ((((h : ℝ) * tailDepth P b (depthSchedule b N) n : ℝ) : ℂ))‖
        ≤ 16 * |(h : ℝ)| * E N := by
      intro n hn
      have hnN : n < N := Finset.mem_range.1 hn
      rw [← mul_sub, norm_mul, norm_ee_real, one_mul]
      refine (norm_ee_sub_ee_le _ _).trans ?_
      have hnn := tailLarge_sub_tailDepth_nonneg hb2 P (depthSchedule b N) n
      have hbd := tailLarge_sub_tailDepth_le_of_lt hb P (depthSchedule b N) N n hnN
      have habs : |(h : ℝ) * tailLarge P b n
          - (h : ℝ) * tailDepth P b (depthSchedule b N) n|
          = |(h : ℝ)| * (tailLarge P b n - tailDepth P b (depthSchedule b N) n) := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hnn]
      rw [habs, ← mul_assoc, mul_comm (16 : ℝ) |(h : ℝ)|, mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left (by simp only [hE]; linarith) (abs_nonneg _)
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [hA, depthAvg, range_zero, Finset.sum_empty, Nat.cast_zero, div_zero,
        sub_zero, norm_zero]
      have := hEnn 0
      positivity
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hsub : A N - depthAvg b P Q j h (depthSchedule b N) N
        = (∑ n ∈ range N, (ee ((((j : ℝ) * n / Q : ℝ) : ℂ))
            * ee ((((h : ℝ) * tailLarge P b n : ℝ) : ℂ))
          - ee ((((j : ℝ) * n / Q : ℝ) : ℂ))
            * ee ((((h : ℝ) * tailDepth P b (depthSchedule b N) n : ℝ) : ℂ)))) / N := by
      rw [hA, depthAvg, div_sub_div_same, Finset.sum_sub_distrib]
    rw [hsub, norm_div, Complex.norm_natCast]
    rw [div_le_iff₀ hNR]
    calc ‖∑ n ∈ range N, (ee ((((j : ℝ) * n / Q : ℝ) : ℂ))
            * ee ((((h : ℝ) * tailLarge P b n : ℝ) : ℂ))
          - ee ((((j : ℝ) * n / Q : ℝ) : ℂ))
            * ee ((((h : ℝ) * tailDepth P b (depthSchedule b N) n : ℝ) : ℂ)))‖
        ≤ ∑ n ∈ range N, (16 * |(h : ℝ)| * E N) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
      _ = 16 * |(h : ℝ)| * E N * N := by
          rw [Finset.sum_const, card_range]; ring
  have hdiff : Tendsto (fun N : ℕ => A N - depthAvg b P Q j h (depthSchedule b N) N)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm hnorm ?_
    simpa [hE] using tendsto_depthErr hb (16 * |(h : ℝ)|)
  have hAt : Tendsto A atTop (𝓝 0) := by
    have := hdiff.add (H P Q j h hQ hj0 hjQ)
    simpa using this
  refine hAt.congr fun N => ?_
  simp only [hA]
  congr 1
  exact Finset.sum_congr rfl fun n _ => by rw [ee_tailLarge_eq_ee_orbit hb2 P n h]

end CastingOut

end NormalNumbers
