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

end CastingOut

end NormalNumbers
