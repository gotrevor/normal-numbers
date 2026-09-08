/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerLowerBoundGeneral
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# The smooth-divisor lower bound and the sharpness of the constant `1` 🧮

`MahlerLowerBoundGeneral.lean` proves `M(g,k) ≥ t(gᵏ − 1)` for every
factorization `g = t·c`.  The multiplier `B = c` works because the last
base-`g` digit of `m·c = q·g + r·c` is `r·c ≤ g − 2`, so a run of `(g−1)`s
must live in `q`.

This file lifts the construction one level: it is enough that `t` divide some
**power** of `g` — with `t·c = g^j` and `t < g`, ALL `j` low digits of
`r·c` (`r < t`) are `≤ g − 2` (`digit_le_of_smooth`), so again a run of
`(g−1)`s must live in `q = ⌊m/t⌋`, and

    **`t ∣ g^j`, `t < g`  ⟹  `M(g,k) ≥ t·(gᵏ − 1)`**    (`mahler_lower_bound_smooth`).

The divisor bound is the case `j = 1`.  The gain is that `t` may now be any
`g`-smooth number below `g`, so `t/g` can be pushed to `1` whenever `g` has
two distinct prime factors: `g = 630`, `t = 625 = 5⁴ ∣ 630⁴` gives
`M(630,1) ≥ 393125 = 0.9905·630²`, and `g = 26250`, `t = 26244 = 2²·3⁸`
gives `M(26250,1) ≥ 0.99973·26250²` (`mahler_lower_bound_630`,
`mahler_lower_bound_26250`).

Pushing this to the limit: by Dirichlet's approximation theorem there are
`a, b` with `|b·log 3 − a·log 2|` arbitrarily small, i.e. `2^a` and `3^b`
within a factor `1 + δ` of each other.  With `g = 2^a·3^b·L` and `t` the
square of the smaller one times `L`, `t ∣ g²`, `t < g`, `t/g ≥ 1 − δ`, so

    **for every `k ≥ 1` and `ε > 0`, some base `g` has `M(g,k) ≥ (1−ε)·g^(k+1)`**
                                                       (`mahler_constant_one_sharp`).

Against `mahler_multiplier_lt` (`M(g,k) < g^(k+1)`) this shows the constant
`1` there is **sharp**: `sup_g M(g,k)/g^(k+1) = 1`, not attained.  The base
can be taken as large as desired.

The construction is the `a = 0` burst family of `MahlerLowerBoundBackground`;
host evidence `docs/mahler-universal-constant-is-one-2026-09-07.md` found the
closed form `(g−1)g/δ*(g)` numerically and checked it against the exact census
(`g ≤ 32`) and direct simulation (`g = 630, 810, 2310`).
-/

namespace NormalNumbers.Mahler

open LiouvilleNumber
open scoped Nat

/-! ### Digits of `r·c` when `t·c = g^j` -/

/-- With `t·c = g^j` and `t < g`, every digit `i < j` of `r·c` is at most
`g − 2` (for EVERY `r` — the low digits of any multiple of `c` avoid `g − 1`).  Indeed `⌊r c / gⁱ⌋ = ⌊r g s / t⌋` with `s = g^(j−i−1)`, and
`⌊r g s/t⌋ mod g = ⌊v g/t⌋` with `v = (r s) mod t ≤ t − 1`, which is
`< g − 1` exactly because `t < g`. -/
theorem digit_le_of_smooth (g t c j r i : ℕ) (hg : 2 ≤ g) (ht : 1 ≤ t) (htg : t < g)
    (hc : t * c = g ^ j) (hi : i < j) :
    (r * c / g ^ i) % g + 2 ≤ g := by
  have hg0 : 0 < g := by omega
  have hgi : 0 < g ^ i := by positivity
  set s := g ^ (j - i - 1) with hs
  have hgj : g ^ j = g * g ^ i * s := by
    rw [hs, ← pow_succ', ← pow_add]; congr 1; omega
  -- `r c t = r g s gⁱ`
  have hkey : r * c * t = r * g * s * g ^ i := by
    calc r * c * t = r * (t * c) := by ring
      _ = r * (g * g ^ i * s) := by rw [hc, hgj]
      _ = r * g * s * g ^ i := by ring
  set q0 := r * g * s / t with hq0
  have hlo : q0 * t ≤ r * g * s := Nat.div_mul_le_self _ _
  have hhi : r * g * s < (q0 + 1) * t := by
    have := Nat.lt_div_mul_add (a := r * g * s) (b := t) (by omega)
    rw [← hq0] at this; linarith
  have hdiv : r * c / g ^ i = q0 := by
    apply Nat.div_eq_of_lt_le
    · apply Nat.le_of_mul_le_mul_right (c := t) _ (by omega)
      calc q0 * g ^ i * t = q0 * t * g ^ i := by ring
        _ ≤ r * g * s * g ^ i := Nat.mul_le_mul_right _ hlo
        _ = r * c * t := hkey.symm
    · apply Nat.lt_of_mul_lt_mul_right (a := t)
      calc r * c * t = r * g * s * g ^ i := hkey
        _ < (q0 + 1) * t * g ^ i := Nat.mul_lt_mul_of_pos_right hhi hgi
        _ = (q0 + 1) * g ^ i * t := by ring
  rw [hdiv]
  -- `q0 = u g + ⌊v g / t⌋` with `v = (r s) % t`
  set u := r * s / t with hu
  set v := r * s % t with hv
  have hrs : r * s = v + u * t := by rw [hv, hu]; exact (Nat.mod_add_div' (r * s) t).symm
  have hq0' : q0 = v * g / t + u * g := by
    rw [hq0]
    have : r * g * s = v * g + (u * g) * t := by rw [show r * g * s = (r * s) * g by ring, hrs]; ring
    rw [this, Nat.add_mul_div_right _ _ (by omega)]
  have hvt : v < t := Nat.mod_lt _ (by omega)
  have hvg : v * g / t < g - 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have h1 : (v + 1) * g ≤ t * g := Nat.mul_le_mul_right g hvt
    have h2 : (g - 1) * t = g * t - t := by rw [Nat.sub_mul, one_mul]
    rw [h2, Nat.lt_sub_iff_add_lt]
    nlinarith [h1, htg]
  have hvg' : v * g / t < g := by omega
  rw [hq0', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hvg']
  omega

/-- If `W < gᵏ` and the last digit of `W` is not `g − 1`, then `W ≤ gᵏ − 2`. -/
theorem le_pred_pred_of_mod (g k W : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k) (hW : W < g ^ k)
    (hmod : W % g + 2 ≤ g) : W + 2 ≤ g ^ k := by
  have hg0 : 0 < g := by omega
  have hgk : g ^ k = g * g ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  have hW' : W = g * (W / g) + W % g := (Nat.div_add_mod W g).symm
  have hu : W / g < g ^ (k - 1) := by
    apply Nat.lt_of_mul_lt_mul_left (a := g)
    calc g * (W / g) ≤ W := by omega
      _ < g ^ k := hW
      _ = g * g ^ (k - 1) := hgk
  have := Nat.mul_le_mul_left g hu
  rw [hgk]; nlinarith

/-- **Window lemma.**  If `N = e + q·g^j` with `e < g^j`, every digit of `e`
below position `j` is `≤ g − 2`, and `q ≤ gᵏ − 2`, then `N` has no `k`
consecutive `(g−1)` digits (in the arithmetic form used by
`mahler_lower_bound_general`). -/
theorem avoid_of_split (g j k N e q : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k)
    (hN : N = e + q * g ^ j) (he : e < g ^ j)
    (hdig : ∀ i, i < j → (e / g ^ i) % g + 2 ≤ g) (hq : q + 2 ≤ g ^ k) :
    ∀ d, k ≤ d → N % g ^ d + g ^ (d - k) + 1 ≤ g ^ d := by
  intro d hkd
  have hg0 : 0 < g := by omega
  set P := g ^ (d - k) with hP
  have hP0 : 0 < P := by positivity
  have hgd : g ^ d = P * g ^ k := by rw [hP, ← pow_add]; congr 1; omega
  set W := N / P % g ^ k with hW
  have hsplit : N % g ^ d = N % P + P * W := by rw [hgd, Nat.mod_mul]
  have hWlt : W < g ^ k := Nat.mod_lt _ (by positivity)
  have hNP : N % P < P := Nat.mod_lt _ hP0
  -- the `k`-digit window at position `d − k` is at most `gᵏ − 2`
  have hWle : W + 2 ≤ g ^ k := by
    rcases Nat.lt_or_ge (d - k) j with hdj | hdj
    · -- the window contains digit `d − k` of `e`, which is `≤ g − 2`
      apply le_pred_pred_of_mod g k W hg hk hWlt
      have hdvd : g ∣ g ^ k := dvd_pow_self g (by omega)
      rw [hW, Nat.mod_mod_of_dvd _ hdvd]
      have hgj : g ^ j = P * (g * g ^ (j - (d - k) - 1)) := by
        rw [hP, ← pow_succ', ← pow_add]; congr 1; omega
      have hNdiv : N / P = e / P + q * (g * g ^ (j - (d - k) - 1)) := by
        rw [hN, hgj, show e + q * (P * (g * g ^ (j - (d - k) - 1))) =
          e + (q * (g * g ^ (j - (d - k) - 1))) * P by ring,
          Nat.add_mul_div_right _ _ hP0]
      rw [hNdiv, show e / P + q * (g * g ^ (j - (d - k) - 1)) =
        e / P + (q * g ^ (j - (d - k) - 1)) * g by ring, Nat.add_mul_mod_self_right]
      exact hdig _ hdj
    · -- the window sits inside `q`
      have hgP : P = g ^ j * g ^ (d - k - j) := by rw [hP, ← pow_add]; congr 1; omega
      have hNdiv : N / P = q / g ^ (d - k - j) := by
        rw [hgP, ← Nat.div_div_eq_div_mul, hN, Nat.add_mul_div_right _ _ (by positivity),
          Nat.div_eq_of_lt he, zero_add]
      have : W ≤ q := by
        rw [hW, hNdiv]
        exact le_trans (Nat.mod_le _ _) (Nat.div_le_self _ _)
      omega
  have h1 : (W + 2) * P ≤ g ^ k * P := Nat.mul_le_mul_right P hWle
  rw [hsplit, hgd]; nlinarith

/-! ### The smooth-divisor bound -/

/-- The arithmetic heart: with `t·c = g^j`, `t < g`, no `k` consecutive
`(g−1)` digits in `m·c` for every `m < t(gᵏ − 1)`. -/
theorem avoid_of_smooth (g t c j k m : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (htg : t < g) (hc : t * c = g ^ j) (hmlt : m + 1 ≤ t * (g ^ k - 1)) :
    ∀ d, k ≤ d → (m * c) % g ^ d + g ^ (d - k) + 1 ≤ g ^ d := by
  obtain ⟨q, r, hqr, hr⟩ : ∃ q r : ℕ, m = t * q + r ∧ r < t :=
    ⟨m / t, m % t, (Nat.div_add_mod m t).symm, Nat.mod_lt _ (by omega)⟩
  have hmc : m * c = r * c + q * g ^ j := by rw [hqr, ← hc]; ring
  have he : r * c < g ^ j := by
    rw [← hc]; exact Nat.mul_lt_mul_of_pos_right hr (by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · subst h0; simp at hc; exact absurd hc (by positivity)
      · exact h0)
  have hq : q + 2 ≤ g ^ k := by
    have h2 : t * q < t * (g ^ k - 1) := by omega
    have h3 : q < g ^ k - 1 := lt_of_mul_lt_mul_left h2 (Nat.zero_le t)
    have hgk1 : 1 ≤ g ^ k := Nat.one_le_pow _ _ (by omega)
    omega
  exact avoid_of_split g j k (m * c) (r * c) q hg hk hmc he
    (fun i hi => digit_le_of_smooth g t c j r i hg ht htg hc hi) hq

/-- **`M(g,k) ≥ t·(gᵏ − 1)` whenever `t < g` divides a power of `g`.**
There are an irrational `α` and a `k`-digit block `w` such that no multiplier
`1 ≤ m < t(gᵏ − 1)` has `w` occurring infinitely often in `m·α`.  Witnesses:
`α = (g^j/t) · liouvilleNumber g`, `w = (g−1)ᵏ`.  `j = 1` is
`mahler_lower_bound_divisor`. -/
theorem mahler_lower_bound_smooth (g t j k : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (htg : t < g) (hdvd : t ∣ g ^ j) :
    ∃ (α : ℝ) (w : List ℕ), Irrational α ∧ w.length = k ∧ (∀ d ∈ w, d < g) ∧
      ∀ m : ℕ, 1 ≤ m → m + 1 ≤ t * (g ^ k - 1) →
        ∃ N, ∀ n, N ≤ n → ¬ OccursAt g ((m : ℝ) * α) w n := by
  obtain ⟨c, hc⟩ := hdvd
  have hc : t * c = g ^ j := hc.symm
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at hc; exact absurd hc (by positivity)
    · exact h0
  set M := t * (g ^ k - 1) - 1 with hMdef
  have hgk2 : 2 ≤ g ^ k := by
    calc 2 ≤ g := hg
      _ = g ^ 1 := (pow_one g).symm
      _ ≤ g ^ k := Nat.pow_le_pow_right (by omega) hk
  have hMpos : 1 ≤ t * (g ^ k - 1) := by
    have := Nat.mul_le_mul ht (show 1 ≤ g ^ k - 1 by omega)
    simpa using this
  have hMK : M * c ≤ g ^ (j + k) := by
    calc M * c ≤ t * (g ^ k - 1) * c := Nat.mul_le_mul_right c (by omega)
      _ = (t * c) * (g ^ k - 1) := by ring
      _ = g ^ j * (g ^ k - 1) := by rw [hc]
      _ ≤ g ^ j * g ^ k := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = g ^ (j + k) := (pow_add g j k).symm
  obtain ⟨α, w, hirr, hlen, hdig, hmain⟩ :=
    mahler_lower_bound_general g hg k hk c hc1 M (j + k) hMK
      (fun m hm1 hmM => avoid_of_smooth g t c j k m hg hk ht htg hc (by omega))
  exact ⟨α, w, hirr, hlen, hdig, fun m hm1 hm2 => hmain m hm1 (by omega)⟩

/-! ### Explicit bases near the ceiling -/

/-- `M(630, 1) ≥ 393125 = 629·625`, i.e. `> 0.99·630²`: `625 = 5⁴` divides
`630⁴`.  (Host simulation: the burst witness gives exactly `393125`.) -/
theorem mahler_lower_bound_630 :
    ∃ (α : ℝ) (w : List ℕ), Irrational α ∧ w.length = 1 ∧ (∀ d ∈ w, d < 630) ∧
      ∀ m : ℕ, 1 ≤ m → m ≤ 393124 →
        ∃ N, ∀ n, N ≤ n → ¬ OccursAt 630 ((m : ℝ) * α) w n := by
  obtain ⟨α, w, hirr, hlen, hdig, hmain⟩ :=
    mahler_lower_bound_smooth 630 625 4 1 (by norm_num) le_rfl (by norm_num) (by norm_num)
      (by decide)
  exact ⟨α, w, hirr, hlen, hdig, fun m hm1 hm2 => hmain m hm1 (by norm_num; omega)⟩

/-- `M(26250, 1) ≥ 688878756 = 26249·26244`, i.e. `> 0.9997·26250²`:
`26244 = 2²·3⁸` divides `26250⁸`. -/
theorem mahler_lower_bound_26250 :
    ∃ (α : ℝ) (w : List ℕ), Irrational α ∧ w.length = 1 ∧ (∀ d ∈ w, d < 26250) ∧
      ∀ m : ℕ, 1 ≤ m → m ≤ 688878755 →
        ∃ N, ∀ n, N ≤ n → ¬ OccursAt 26250 ((m : ℝ) * α) w n := by
  obtain ⟨α, w, hirr, hlen, hdig, hmain⟩ :=
    mahler_lower_bound_smooth 26250 26244 8 1 (by norm_num) le_rfl (by norm_num) (by norm_num)
      (by decide)
  exact ⟨α, w, hirr, hlen, hdig, fun m hm1 hm2 => hmain m hm1 (by norm_num; omega)⟩

/-! ### The constant `1` is sharp -/

/-- `|log x − log y| ≤ δ` forces `(1 − δ)·y ≤ x`. -/
theorem ratio_ge_of_log_close (x y δ : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : |Real.log x - Real.log y| ≤ δ) : (1 - δ) * y ≤ x := by
  have h1 : -δ ≤ Real.log x - Real.log y := by
    have := (abs_le.1 h).1; linarith
  have h2 : Real.exp (-δ) ≤ x / y := by
    rw [← Real.exp_log hx, ← Real.exp_log hy, ← Real.exp_sub]
    exact Real.exp_le_exp.2 h1
  have h3 : 1 - δ ≤ x / y := by linarith [Real.add_one_le_exp (-δ)]
  rwa [le_div_iff₀ hy] at h3

/-- **Dirichlet on `log 3 / log 2`.**  For every `δ > 0` there are `a` and
`b ≥ 1` with `|log(3^b) − log(2^a)| ≤ δ`. -/
theorem exists_pow_two_three_close (δ : ℝ) (hδ : 0 < δ) :
    ∃ a b : ℕ, 1 ≤ b ∧ |Real.log ((3 : ℝ) ^ b) - Real.log ((2 : ℝ) ^ a)| ≤ δ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  set n : ℕ := ⌈Real.log 2 / δ⌉₊ + 1 with hn
  have hn0 : 0 < n := by omega
  obtain ⟨j, k, hk0, hkn, hjk⟩ :=
    Real.exists_int_int_abs_mul_sub_le (Real.log 3 / Real.log 2) hn0
  have hn1 : (1 : ℝ) / (n + 1) ≤ δ / Real.log 2 := by
    rw [div_le_div_iff₀ (by positivity) hl2]
    have : Real.log 2 / δ ≤ ⌈Real.log 2 / δ⌉₊ := Nat.le_ceil _
    have hn' : (n : ℝ) = ⌈Real.log 2 / δ⌉₊ + 1 := by rw [hn]; push_cast; ring
    rw [div_le_iff₀ hδ] at this
    rw [hn']; nlinarith
  have hn2 : (1 : ℝ) / (n + 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    linarith
  -- `k ≥ 1`, `j ≥ 1`
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  have hξ : 1 < Real.log 3 / Real.log 2 := by rw [lt_div_iff₀ hl2]; linarith
  have hj1 : (1 : ℤ) ≤ j := by
    by_contra hcon
    have hj0 : (j : ℝ) ≤ 0 := by exact_mod_cast (by omega : j ≤ 0)
    have hkξ : 1 < (k : ℝ) * (Real.log 3 / Real.log 2) := by nlinarith
    have := (abs_le.1 hjk).2
    linarith
  refine ⟨j.toNat, k.toNat, by omega, ?_⟩
  have hjc : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by
    rw [show ((j.toNat : ℕ) : ℝ) = ((j.toNat : ℤ) : ℝ) from (Int.cast_natCast _).symm,
      Int.toNat_of_nonneg (by omega)]
  have hkc : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
    rw [show ((k.toNat : ℕ) : ℝ) = ((k.toNat : ℤ) : ℝ) from (Int.cast_natCast _).symm,
      Int.toNat_of_nonneg (by omega)]
  rw [Real.log_pow, Real.log_pow, hjc, hkc]
  have hmul : (k : ℝ) * Real.log 3 - (j : ℝ) * Real.log 2 =
      ((k : ℝ) * (Real.log 3 / Real.log 2) - j) * Real.log 2 := by
    field_simp
  rw [hmul, abs_mul, abs_of_pos hl2]
  calc |(k : ℝ) * (Real.log 3 / Real.log 2) - j| * Real.log 2
      ≤ 1 / (n + 1) * Real.log 2 := by gcongr
    _ ≤ δ / Real.log 2 * Real.log 2 := by gcongr
    _ = δ := by field_simp

/-- A base `g ≥ L` with a smooth `t ∣ g²`, `t < g`, `t ≥ (1 − δ)·g`: take
`g = 2^a·3^b·L` and `t = (min)²·L`. -/
theorem exists_smooth_base (δ : ℝ) (hδ : 0 < δ) (L : ℕ) (hL : 1 ≤ L) :
    ∃ g t : ℕ, L ≤ g ∧ 2 ≤ g ∧ 1 ≤ t ∧ t < g ∧ t ∣ g ^ 2 ∧ (1 - δ) * (g : ℝ) ≤ t := by
  obtain ⟨a, b, hb, hab⟩ := exists_pow_two_three_close δ hδ
  set A : ℕ := 2 ^ a with hA
  set B : ℕ := 3 ^ b with hB
  have hA0 : 1 ≤ A := Nat.one_le_pow _ _ (by norm_num)
  have hB3 : 3 ≤ B := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hAr : ((A : ℕ) : ℝ) = (2 : ℝ) ^ a := by rw [hA]; push_cast; ring
  have hBr : ((B : ℕ) : ℝ) = (3 : ℝ) ^ b := by rw [hB]; push_cast; ring
  have hAB : A ≠ B := by
    intro h
    have hodd : Odd B := Odd.pow (by decide : Odd 3)
    rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha] at hA; simp [hA] at h; omega
    · have heven : Even A := (Nat.even_pow.2 ⟨even_two, by omega⟩)
      rw [h] at heven
      exact (Nat.not_even_iff_odd.2 hodd) heven
  have hAr0 : (0 : ℝ) < A := by exact_mod_cast hA0
  have hBr0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hBA : (1 - δ) * (A : ℝ) ≤ B := by
    apply ratio_ge_of_log_close _ _ δ hBr0 hAr0; rwa [hAr, hBr]
  have hAB' : (1 - δ) * (B : ℝ) ≤ A := by
    apply ratio_ge_of_log_close _ _ δ hAr0 hBr0; rw [hAr, hBr, abs_sub_comm]; exact hab
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  rcases lt_or_gt_of_ne hAB with hlt | hlt
  · -- `A < B`: `g = A B L`, `t = A² L`
    refine ⟨A * B * L, A * A * L, ?_, ?_, ?_, ?_, ⟨B * B * L, by ring⟩, ?_⟩
    · calc L = 1 * 1 * L := by ring
        _ ≤ A * B * L := by gcongr; omega
    · calc 2 ≤ 1 * 3 * 1 := by norm_num
        _ ≤ A * B * L := by gcongr
    · calc 1 = 1 * 1 * 1 := by norm_num
        _ ≤ A * A * L := by gcongr
    · have := Nat.mul_lt_mul_of_pos_left hlt (by omega : 0 < A)
      exact Nat.mul_lt_mul_of_pos_right this (by omega)
    · push_cast
      have := mul_le_mul_of_nonneg_right hAB' (le_of_lt (mul_pos hAr0 hL0))
      nlinarith
  · -- `B < A`: `g = A B L`, `t = B² L`
    refine ⟨A * B * L, B * B * L, ?_, ?_, ?_, ?_, ⟨A * A * L, by ring⟩, ?_⟩
    · calc L = 1 * 1 * L := by ring
        _ ≤ A * B * L := by gcongr; omega
    · calc 2 ≤ 1 * 3 * 1 := by norm_num
        _ ≤ A * B * L := by gcongr
    · calc 1 = 1 * 1 * 1 := by norm_num
        _ ≤ B * B * L := by gcongr <;> omega
    · have := Nat.mul_lt_mul_of_pos_right hlt (by omega : 0 < B)
      exact Nat.mul_lt_mul_of_pos_right this (by omega)
    · push_cast
      have := mul_le_mul_of_nonneg_right hBA (le_of_lt (mul_pos hBr0 hL0))
      nlinarith

/-- **The constant `1` in `M(g,k) < g^(k+1)` is sharp.**  For every block
length `k ≥ 1`, every `ε > 0` and every `L`, there is a base `g ≥ L` with an
irrational `α` and a `k`-block `w` such that no multiplier
`1 ≤ m < (1 − ε)·g^(k+1)` has `w` infinitely often in `m·α`; that is,
`M(g,k) ≥ (1 − ε)·g^(k+1)`.  Together with `mahler_multiplier_lt`:
`sup_g M(g,k)/g^(k+1) = 1`, and the supremum is not attained. -/
theorem mahler_constant_one_sharp (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (L : ℕ) :
    ∃ g : ℕ, L ≤ g ∧ 2 ≤ g ∧
      ∃ (α : ℝ) (w : List ℕ), Irrational α ∧ w.length = k ∧ (∀ d ∈ w, d < g) ∧
        ∀ m : ℕ, 1 ≤ m → (m : ℝ) + 1 ≤ (1 - ε) * (g : ℝ) ^ (k + 1) →
          ∃ N, ∀ n, N ≤ n → ¬ OccursAt g ((m : ℝ) * α) w n := by
  -- reduce to `ε ≤ 1`
  suffices h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ g : ℕ, L ≤ g ∧ 2 ≤ g ∧
      ∃ (α : ℝ) (w : List ℕ), Irrational α ∧ w.length = k ∧ (∀ d ∈ w, d < g) ∧
        ∀ m : ℕ, 1 ≤ m → (m : ℝ) + 1 ≤ (1 - ε) * (g : ℝ) ^ (k + 1) →
          ∃ N, ∀ n, N ≤ n → ¬ OccursAt g ((m : ℝ) * α) w n by
    obtain ⟨g, hLg, hg, α, w, hirr, hlen, hdig, hmain⟩ := h (min ε 1) (by positivity) (min_le_right _ _)
    refine ⟨g, hLg, hg, α, w, hirr, hlen, hdig, fun m hm1 hm2 => hmain m hm1 ?_⟩
    have hmin : min ε 1 ≤ ε := min_le_left _ _
    have hgp : (0 : ℝ) ≤ (g : ℝ) ^ (k + 1) := by positivity
    nlinarith
  intro ε hε hε1
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨g, t, hLg, hg, ht, htg, hdvd, hratio⟩ :=
    exists_smooth_base δ hδ0 (L + ⌈2 / ε⌉₊ + 1) (by omega)
  refine ⟨g, by omega, hg, ?_⟩
  obtain ⟨α, w, hirr, hlen, hdig, hmain⟩ := mahler_lower_bound_smooth g t 2 k hg hk ht htg hdvd
  refine ⟨α, w, hirr, hlen, hdig, fun m hm1 hm2 => hmain m hm1 ?_⟩
  -- real estimate: `(1 − ε) g^(k+1) ≤ t (gᵏ − 1)`
  have hgr : (2 : ℝ) / ε ≤ g := by
    have h1 : (2 / ε : ℝ) ≤ ⌈2 / ε⌉₊ := Nat.le_ceil _
    have h2 : (⌈2 / ε⌉₊ : ℝ) ≤ g := by exact_mod_cast (by omega : ⌈2 / ε⌉₊ ≤ g)
    linarith
  have hgr0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hδg : 1 ≤ δ * g := by
    rw [hδ]; rw [div_le_iff₀ hε] at hgr; linarith
  have hgk1 : (g : ℝ) ≤ (g : ℝ) ^ k := by
    calc (g : ℝ) = (g : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (g : ℝ) ^ k := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ g)) hk
  have hgk0 : (0 : ℝ) ≤ (g : ℝ) ^ k := by positivity
  have hδ1 : 0 ≤ 1 - δ := by rw [hδ]; linarith
  have hA : (1 - δ) * (g : ℝ) ^ k ≤ (g : ℝ) ^ k - 1 := by nlinarith
  have hB : (1 - δ) * (g : ℝ) * ((1 - δ) * (g : ℝ) ^ k) ≤ (t : ℝ) * ((g : ℝ) ^ k - 1) :=
    mul_le_mul hratio hA (by positivity) (by positivity)
  have hC : (1 - ε) * (g : ℝ) ^ (k + 1) ≤ (1 - δ) * (g : ℝ) * ((1 - δ) * (g : ℝ) ^ k) := by
    rw [show (1 - δ) * (g : ℝ) * ((1 - δ) * (g : ℝ) ^ k) = (1 - δ) ^ 2 * (g : ℝ) ^ (k + 1) by ring]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [hδ]; nlinarith [sq_nonneg ε]
  have hnat : ((t * (g ^ k - 1) : ℕ) : ℝ) = (t : ℝ) * ((g : ℝ) ^ k - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]; push_cast; ring
  have : (m : ℝ) + 1 ≤ ((t * (g ^ k - 1) : ℕ) : ℝ) := by rw [hnat]; linarith
  exact_mod_cast this

end NormalNumbers.Mahler
