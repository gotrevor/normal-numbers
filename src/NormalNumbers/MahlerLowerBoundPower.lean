/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerLowerBoundGeneral

/-!
# Mahler lower bound: the prime-power multiplier `t·c = g^L` 🧮

`MahlerLowerBoundGeneral.lean` proves `M(g,k) ≥ t(gᵏ − 1)` for a factorization
`g = t·c` with `c ≥ 2` (Berend–Boshernitzan 1994, Thm 3.1).  Its mechanism is
that the *last* base-`g` digit of `m·c` is never `g − 1`, so a run of `k` of
them must live in `q = ⌊m/t⌋`.

This file replaces `g` by `g^L`: for any factorization

    t · c = g^L        with every `s·c`, `s < t`, free of the digit `g − 1`

the same argument runs with an `L`-digit guard block instead of a one-digit
one, giving **`M(g,k) ≥ t(gᵏ − 1)`** for a `t` that can far exceed the largest
proper divisor of `g`.  `L = 1` recovers the divisor family exactly.

The point of the generalisation is **base 10**:

    8 · 125 = 10³,   {0, 125, 250, 375, 500, 625, 750, 875}  has no digit 9

gives `M(10,k) ≥ 8(10ᵏ − 1)` (`mahler_lower_bound_base10`), against the
divisor family's `5(10ᵏ − 1)` and the upper bound `10^(k+1)`.  At `k = 1`:
`72 ≤ M(10,1) ≤ 100`, a factor `1.39`; and `72` is the *exact* value reported
by the adder machine, so base 10 joins base 5 in being pinned from below by a
witness that is known to be optimal.

## The digit lemma

Everything rests on one arithmetic fact (`window_lt_of_digit`): *if any digit
of `N` inside the window `[d−k, d)` is not `g − 1`, then
`N % g^d + g^(d−k) + 1 ≤ g^d`* — i.e. the window is not the all-`(g−1)` block.
The converse direction (`N % g^d ≥ g^d − g^(d−k)` forces every digit in the
window to be `g − 1`) is what makes the guard block work.
-/

namespace NormalNumbers.Mahler

/-- `(g^k − 1) / g^i` has last base-`g` digit `g − 1`, for `i < k`. -/
theorem pred_pow_div_mod (g k i : ℕ) (hg : 2 ≤ g) (hik : i < k) :
    (g ^ k - 1) / g ^ i % g = g - 1 := by
  have h1 : 1 ≤ g ^ i := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ g ^ (k - i) := Nat.one_le_pow _ _ (by omega)
  have hsplit : g ^ k = g ^ i * g ^ (k - i) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hik)]
  have hrw : g ^ k - 1 = g ^ i * (g ^ (k - i) - 1) + (g ^ i - 1) := by
    have : g ^ i * (g ^ (k - i) - 1) = g ^ i * g ^ (k - i) - g ^ i := by
      rw [Nat.mul_sub, mul_one]
    have hge : g ^ i ≤ g ^ i * g ^ (k - i) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  rw [hrw, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  -- `(g^(k−i) − 1) % g = g − 1` since `k − i ≥ 1`
  have h3 : 1 ≤ g ^ (k - i - 1) := Nat.one_le_pow _ _ (by omega)
  have hpk : g ^ (k - i) = g * g ^ (k - i - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  have hge : g ≤ g * g ^ (k - i - 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hrw2 : g ^ (k - i) - 1 = (g - 1) + g * (g ^ (k - i - 1) - 1) := by
    have : g * (g ^ (k - i - 1) - 1) = g * g ^ (k - i - 1) - g := by
      rw [Nat.mul_sub, mul_one]
    omega
  rw [hrw2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- **The digit lemma.**  If some digit of `N` in the window `[d−k, d)` is not
`g − 1`, the window is not the all-`(g−1)` block. -/
theorem window_lt_of_digit (g k d p N : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k) (hkd : k ≤ d)
    (hdp : d - k ≤ p) (hpd : p < d) (hdig : N / g ^ p % g + 1 < g) :
    N % g ^ d + g ^ (d - k) + 1 ≤ g ^ d := by
  by_contra hcon
  push_neg at hcon
  have hgp : 0 < g ^ p := by positivity
  have hgd : 0 < g ^ d := by positivity
  set A := N % g ^ d with hAdef
  have hAlt : A < g ^ d := Nat.mod_lt _ hgd
  set Q := g ^ (d - k) with hQdef
  have hQ : 0 < Q := by positivity
  have hQk : Q * g ^ k = g ^ d := by
    rw [hQdef, ← pow_add, Nat.sub_add_cancel hkd]
  -- the window value is forced to `g^k − 1`
  have hone : 1 ≤ g ^ k := Nat.one_le_pow _ _ (by omega)
  have hQle : Q ≤ g ^ d := by rw [← hQk]; exact Nat.le_mul_of_pos_right _ (by positivity)
  have hAQ : A / Q = g ^ k - 1 := by
    have hge : (g ^ k - 1) * Q ≤ A := by
      have hid : (g ^ k - 1) * Q = g ^ d - Q := by
        rw [Nat.sub_mul, one_mul, ← hQk]; ring_nf
      omega
    have hlt : A < (g ^ k - 1 + 1) * Q := by
      rw [show g ^ k - 1 + 1 = g ^ k by omega, show g ^ k * Q = Q * g ^ k by ring, hQk]
      exact hAlt
    exact Nat.div_eq_of_lt_le hge hlt
  -- digit `p` of `N` equals digit `p` of `A`
  have hpdvd : g ^ p ∣ g ^ d := pow_dvd_pow g (le_of_lt hpd)
  obtain ⟨u, hu⟩ : ∃ u, N = g ^ d * u + A := ⟨N / g ^ d, by rw [hAdef]; exact (Nat.div_add_mod N (g ^ d)).symm⟩
  have hdp1 : 1 ≤ d - p := by omega
  have hgdp : g ^ d = g ^ p * (g * g ^ (d - p - 1)) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  have hNdig : N / g ^ p % g = A / g ^ p % g := by
    rw [hu, hgdp, show g ^ p * (g * g ^ (d - p - 1)) * u = g ^ p * (g * (g ^ (d - p - 1) * u)) by
      ring, Nat.mul_add_div hgp, Nat.mul_add_mod]
  -- but digit `p` of `A` is `g − 1`
  obtain ⟨i, hi, hip⟩ : ∃ i, i < k ∧ p = (d - k) + i := ⟨p - (d - k), by omega, by omega⟩
  have hApi : A / g ^ p = (g ^ k - 1) / g ^ i := by
    rw [hip, pow_add, ← Nat.div_div_eq_div_mul, ← hQdef, hAQ]
  rw [hNdig, hApi, pred_pow_div_mod g k i hg hi] at hdig
  omega

/-- Split for the power family: `m·c = q·g^L + s·c` with `q ≤ gᵏ − 2` and
`s·c < g^L`. -/
theorem power_split (g t c k L m : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hL : 1 ≤ L) (hc : t * c = g ^ L) (hc1 : 1 ≤ c) (hmlt : m + 1 ≤ t * (g ^ k - 1)) :
    ∃ q s : ℕ, m * c = q * g ^ L + s * c ∧ s < t ∧ s * c + c ≤ g ^ L ∧ q + 2 ≤ g ^ k := by
  have hgk1 : 1 ≤ g ^ k := Nat.one_le_pow _ _ (by omega)
  refine ⟨m / t, m % t, ?_, Nat.mod_lt _ (by omega), ?_, ?_⟩
  · have hd : t * (m / t) + m % t = m := Nat.div_add_mod m t
    calc m * c = (t * (m / t) + m % t) * c := by rw [hd]
      _ = (m / t) * (t * c) + (m % t) * c := by ring
      _ = (m / t) * g ^ L + (m % t) * c := by rw [hc]
  · have hlt : m % t < t := Nat.mod_lt _ (by omega)
    calc m % t * c + c = (m % t + 1) * c := by ring
      _ ≤ t * c := Nat.mul_le_mul_right c (by omega)
      _ = g ^ L := hc
  · have h2 : t * (m / t) ≤ m := Nat.mul_div_le m t
    have h3 : t * (m / t) < t * (g ^ k - 1) := by omega
    have h4 : m / t < g ^ k - 1 := lt_of_mul_lt_mul_left h3 (Nat.zero_le t)
    omega

/-- **The power family avoidance certificate.**  If every guard block `s·c`
(`s < t`) is free of the digit `g − 1` in its `L` base-`g` digits, then `m·c`
has no `k` consecutive `(g−1)` digits, for every `1 ≤ m < t(gᵏ − 1)`. -/
theorem avoid_of_power (g t c k L m : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hL : 1 ≤ L) (hc : t * c = g ^ L) (hc2 : 2 ≤ c)
    (hguard : ∀ s, s < t → ∀ i, i < L → s * c / g ^ i % g + 1 < g)
    (hmlt : m + 1 ≤ t * (g ^ k - 1)) :
    ∀ d, k ≤ d → (m * c) % g ^ d + g ^ (d - k) + 1 ≤ g ^ d := by
  obtain ⟨q, s, hmc, hst, hsc, hq2⟩ := power_split g t c k L m hg hk ht hL hc (by omega) hmlt
  have hgL : 0 < g ^ L := by positivity
  intro d hkd
  rcases le_or_gt d (L + k - 1) with hsmall | hbig
  · -- the window meets the guard block: use digit `p = min (d−1) (L−1)`
    set p := min (d - 1) (L - 1) with hpdef
    have hpd : p < d := by omega
    have hpL : p < L := by omega
    have hdp : d - k ≤ p := by omega
    have hdigN : m * c / g ^ p % g = s * c / g ^ p % g := by
      have hLp : 1 ≤ L - p := by omega
      have hgLp : g ^ L = g ^ p * (g * g ^ (L - p - 1)) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      rw [hmc, hgLp, show q * (g ^ p * (g * g ^ (L - p - 1))) + s * c
          = g ^ p * (g * (g ^ (L - p - 1) * q)) + s * c by ring,
        Nat.mul_add_div (by positivity), Nat.mul_add_mod]
    have := hguard s hst p hpL
    exact window_lt_of_digit g k d p (m * c) hg hk hkd hdp hpd (by rw [hdigN]; exact this)
  · -- the window sits above the guard block: the size bound suffices
    have hdLk : L + k ≤ d := by omega
    have hsize : m * c + 2 ≤ g ^ (L + k) := by
      have h1 : q * g ^ L ≤ (g ^ k - 2) * g ^ L := Nat.mul_le_mul_right _ (by omega)
      have h2 : (g ^ k - 2) * g ^ L = g ^ k * g ^ L - 2 * g ^ L := by rw [Nat.sub_mul]
      have h3 : 2 * g ^ L ≤ g ^ k * g ^ L :=
        Nat.mul_le_mul_right _ (by have := Nat.one_le_pow k g (show 0 < g by omega); omega)
      have h4 : g ^ (L + k) = g ^ k * g ^ L := by rw [pow_add]; ring
      omega
    have hmlt' : m * c < g ^ d := by
      have : g ^ (L + k) ≤ g ^ d := Nat.pow_le_pow_right (by omega) hdLk
      omega
    rw [Nat.mod_eq_of_lt hmlt']
    rcases eq_or_lt_of_le hdLk with hd1 | hd2
    · -- `d = L + k`: the slack is exactly the guard block
      have hdk : d - k = L := by omega
      rw [hdk]
      have hq : q * g ^ L + s * c + c ≤ (g ^ k - 2) * g ^ L + g ^ L := by
        have h1 : q * g ^ L ≤ (g ^ k - 2) * g ^ L := Nat.mul_le_mul_right _ (by omega)
        omega
      have h2 : (g ^ k - 2) * g ^ L + g ^ L = g ^ k * g ^ L - g ^ L := by
        rw [Nat.sub_mul]
        have h3 : 2 * g ^ L ≤ g ^ k * g ^ L :=
          Nat.mul_le_mul_right _ (by have := Nat.one_le_pow k g (show 0 < g by omega); omega)
        omega
      have h4 : g ^ d = g ^ k * g ^ L := by rw [← hd1, pow_add]; ring
      omega
    · -- `d > L + k`: crude size bound
      have h1 : g ^ (L + k) ≤ g ^ (d - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : g ^ (d - k) ≤ g ^ (d - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : g ^ d = g ^ (d - 1) * g := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      have h4 : 2 * g ^ (d - 1) ≤ g ^ (d - 1) * g := by
        have := Nat.mul_le_mul_left (g ^ (d - 1)) hg
        omega
      omega

/-- **`M(g,k) ≥ t·(gᵏ − 1)` for every `t·c = g^L` with digit-`(g−1)`-free
guard blocks.**  `L = 1` is `mahler_lower_bound_divisor`; `L > 1` admits `t`
larger than any proper divisor of `g`. -/
theorem mahler_lower_bound_power (g t c k L : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hL : 1 ≤ L) (hc : t * c = g ^ L) (hc2 : 2 ≤ c)
    (hguard : ∀ s, s < t → ∀ i, i < L → s * c / g ^ i % g + 1 < g) :
    ∃ (α : ℝ) (w : List ℕ), Irrational α ∧ w.length = k ∧ (∀ d ∈ w, d < g) ∧
      ∀ m : ℕ, 1 ≤ m → m + 1 ≤ t * (g ^ k - 1) →
        ∃ N, ∀ n, N ≤ n → ¬ OccursAt g ((m : ℝ) * α) w n := by
  set M := t * (g ^ k - 1) - 1 with hMdef
  have hgk2 : 2 ≤ g ^ k := by
    calc 2 ≤ g := hg
      _ = g ^ 1 := (pow_one g).symm
      _ ≤ g ^ k := Nat.pow_le_pow_right (by omega) hk
  have hMpos : 1 ≤ t * (g ^ k - 1) := by
    have := Nat.mul_le_mul ht (show 1 ≤ g ^ k - 1 by omega)
    simpa using this
  have hMK : M * c ≤ g ^ (L + k) := by
    obtain ⟨q, s, hmc, hst, hsc, hq2⟩ :=
      power_split g t c k L M hg hk ht hL hc (by omega) (by omega)
    have h1 : q * g ^ L ≤ (g ^ k - 2) * g ^ L := Nat.mul_le_mul_right _ (by omega)
    have h2 : (g ^ k - 2) * g ^ L = g ^ k * g ^ L - 2 * g ^ L := by rw [Nat.sub_mul]
    have h3 : 2 * g ^ L ≤ g ^ k * g ^ L :=
      Nat.mul_le_mul_right _ (by have := Nat.one_le_pow k g (show 0 < g by omega); omega)
    have h4 : g ^ (L + k) = g ^ k * g ^ L := by rw [pow_add]; ring
    omega
  obtain ⟨α, w, hirr, hlen, hdig, hmain⟩ :=
    mahler_lower_bound_general g hg k hk c (by omega) M (L + k) hMK
      (fun m hm1 hmM => avoid_of_power g t c k L m hg hk ht hL hc hc2 hguard (by omega))
  exact ⟨α, w, hirr, hlen, hdig, fun m hm1 hm2 => hmain m hm1 (by omega)⟩

/-- **`M(10,k) ≥ 8(10ᵏ − 1)`.**  `8 · 125 = 10³` and the guard blocks
`0, 125, 250, 375, 500, 625, 750, 875` contain no digit `9`.  At `k = 1` this is
`M(10,1) ≥ 72`, the exact adder-machine value, against the upper bound `100`
and the divisor family's `45`. -/
theorem mahler_lower_bound_base10 (k : ℕ) (hk : 1 ≤ k) :
    ∃ (α : ℝ) (w : List ℕ), Irrational α ∧ w.length = k ∧ (∀ d ∈ w, d < 10) ∧
      ∀ m : ℕ, 1 ≤ m → m + 1 ≤ 8 * (10 ^ k - 1) →
        ∃ N, ∀ n, N ≤ n → ¬ OccursAt 10 ((m : ℝ) * α) w n :=
  mahler_lower_bound_power 10 8 125 k 3 (by norm_num) hk (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide)

end NormalNumbers.Mahler
