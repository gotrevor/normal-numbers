/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerLowerBoundBackground

/-!
# The burst as an ADDER: the `k = 1` background certificate, digit by digit 🧮

`MahlerLowerBoundBackground.lean` states the `k = 1` certificate in *window*
form: for every distance `d ≥ 1`, the leading digit of

    ρ(d) = (b·S_d + N) mod g^d      (`bgResidue`,  b = m a mod (g−1), N = m B)

must miss the target digit `W`.  That form is fine for `decide`, but it is the
wrong shape for a proof that is **uniform in `g`**: each `d` re-derives the same
long addition from scratch.

This file gives the equivalent **adder form**.  Adding the constant background
string `b b b …` to `N` is a school long addition, so define the carry into
position `i` and the digit emitted there by

    bgCarry i+1 = (b + Nᵢ + bgCarry i) / g,   bgDigit i = (b + Nᵢ + bgCarry i) % g

(`Nᵢ = N / gⁱ % g`).  Then (`bgResidue_div_eq_bgDigit`)

    ρ(i+1) / gⁱ = bgDigit i,

so the whole infinite family of window conditions is exactly "no emitted digit
is `W`".  Two consequences:

* the certificate `mahler_lower_bound_bg_adder` needs only `m B < g^D` in place
  of the old `hstab` (background-plus-burst fits in `D` digits): once `N` runs
  out the carry dies and the emitted digits are `b` or `b + 1`, so `hback`
  closes the tail by itself;
* the conditions become **one affine congruence per digit position**, which is
  what a uniform-in-`g` family needs.

The first uniform brick is `bgDigit_zero_ne` : for odd `g ≥ 5`, `Q = (g−1)/2`
and a burst with `B ≡ −4 (mod g)`, the position-`0` digit misses `g − 1` for
**every** `m < Q²`.  Writing `m = u Q + r` the digit sum is
`2r + m B ≡ 2r − 4m ≡ 2(u − r) (mod g)`, and `2(u−r) ≡ −1 (mod g)` forces
`u − r ≡ Q`, i.e. `u ≥ Q`, i.e. `m ≥ Q²`.  That `Q²` is exactly the census
value `M(p,1) ≈ ⌊p/2⌋²`, and `B ≡ −4 (mod g)` is the law satisfied by every
extremal burst found by search (`experiments/mahler_burst_tower.py`).
-/

namespace NormalNumbers.Mahler

/-- Peeling one base-`g` digit off a residue. -/
theorem mod_pow_succ_split (g N d : ℕ) (hg : 2 ≤ g) :
    N % g ^ (d + 1) = N % g ^ d + (N / g ^ d % g) * g ^ d := by
  have hA : 0 < g ^ d := by positivity
  have e1 : g ^ d * (N / g ^ d) + N % g ^ d = N := Nat.div_add_mod N (g ^ d)
  have e2 : g * (N / g ^ d / g) + N / g ^ d % g = N / g ^ d := Nat.div_add_mod _ _
  have e3 : N / g ^ d / g = N / g ^ (d + 1) := by
    rw [Nat.div_div_eq_div_mul, ← pow_succ]
  rw [e3] at e2
  have h1 : N = g ^ (d + 1) * (N / g ^ (d + 1))
      + ((N / g ^ d % g) * g ^ d + N % g ^ d) := by
    calc N = g ^ d * (N / g ^ d) + N % g ^ d := e1.symm
      _ = g ^ d * (g * (N / g ^ (d + 1)) + N / g ^ d % g) + N % g ^ d := by rw [e2]
      _ = g ^ (d + 1) * (N / g ^ (d + 1)) + ((N / g ^ d % g) * g ^ d + N % g ^ d) := by
          rw [pow_succ]; ring
  have hlt : (N / g ^ d % g) * g ^ d + N % g ^ d < g ^ (d + 1) := by
    have h4 : N / g ^ d % g < g := Nat.mod_lt _ (by omega)
    have h5 : N % g ^ d < g ^ d := Nat.mod_lt _ hA
    calc (N / g ^ d % g) * g ^ d + N % g ^ d
        < (N / g ^ d % g) * g ^ d + g ^ d := by omega
      _ = (N / g ^ d % g + 1) * g ^ d := by ring
      _ ≤ g * g ^ d := Nat.mul_le_mul_right _ (by omega)
      _ = g ^ (d + 1) := by rw [pow_succ]; ring
  conv_lhs => rw [h1]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  omega

/-- The carry into position `i` of the long addition "constant digit `b` plus `N`". -/
def bgCarry (g b N : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => (b + N / g ^ i % g + bgCarry g b N i) / g

/-- The digit emitted at position `i` by "constant digit `b` plus `N`". -/
def bgDigit (g b N i : ℕ) : ℕ := (b + N / g ^ i % g + bgCarry g b N i) % g

theorem bgCarry_zero (g b N : ℕ) : bgCarry g b N 0 = 0 := rfl

theorem bgCarry_succ (g b N i : ℕ) :
    bgCarry g b N (i + 1) = (b + N / g ^ i % g + bgCarry g b N i) / g := rfl

/-- The carry never exceeds `1`. -/
theorem bgCarry_le_one (g b N : ℕ) (hg : 2 ≤ g) (hb : b < g) :
    ∀ i, bgCarry g b N i ≤ 1 := by
  intro i
  induction i with
  | zero => simp [bgCarry]
  | succ i ih =>
    rw [bgCarry_succ]
    have hn : N / g ^ i % g < g := Nat.mod_lt _ (by omega)
    have hsum : b + N / g ^ i % g + bgCarry g b N i < 2 * g := by omega
    have := (Nat.div_lt_iff_lt_mul (show 0 < g by omega)).2 hsum
    omega

theorem bgDigit_lt (g b N i : ℕ) (hg : 2 ≤ g) : bgDigit g b N i < g :=
  Nat.mod_lt _ (by omega)

/-- The reassembled low digits are below `g^d`. -/
theorem bg_sum_lt (g b N : ℕ) (hg : 2 ≤ g) :
    ∀ d, (∑ i ∈ Finset.range d, bgDigit g b N i * g ^ i) < g ^ d := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ]
    have hd : bgDigit g b N d < g := bgDigit_lt g b N d hg
    have hg0 : 0 < g ^ d := by positivity
    calc (∑ i ∈ Finset.range d, bgDigit g b N i * g ^ i) + bgDigit g b N d * g ^ d
        < g ^ d + bgDigit g b N d * g ^ d := by omega
      _ = (bgDigit g b N d + 1) * g ^ d := by ring
      _ ≤ g * g ^ d := Nat.mul_le_mul_right _ (by omega)
      _ = g ^ (d + 1) := by rw [pow_succ]; ring

/-- **The long addition.**  The low `d` digits of "constant `b` plus `N`", plus the
carry out, reassemble `b·S_d + (N mod g^d)`. -/
theorem bg_add_split (g b N : ℕ) (hg : 2 ≤ g) :
    ∀ d, b * repunit g d + N % g ^ d
      = (∑ i ∈ Finset.range d, bgDigit g b N i * g ^ i) + bgCarry g b N d * g ^ d := by
  intro d
  induction d with
  | zero => simp [repunit, bgCarry, Nat.mod_one]
  | succ d ih =>
    have hrep : repunit g (d + 1) = repunit g d + g ^ d := by
      simp [repunit, Finset.sum_range_succ]
    have hmod := mod_pow_succ_split g N d hg
    have hdiv : b + N / g ^ d % g + bgCarry g b N d
        = bgDigit g b N d + g * bgCarry g b N (d + 1) := by
      rw [bgDigit, bgCarry_succ]
      have := Nat.mod_add_div (b + N / g ^ d % g + bgCarry g b N d) g
      omega
    rw [hrep, Finset.sum_range_succ, hmod, Nat.mul_add,
      show b * repunit g d + b * g ^ d + (N % g ^ d + (N / g ^ d % g) * g ^ d)
        = (b * repunit g d + N % g ^ d) + (b + N / g ^ d % g) * g ^ d by ring, ih]
    calc (∑ i ∈ Finset.range d, bgDigit g b N i * g ^ i) + bgCarry g b N d * g ^ d
            + (b + N / g ^ d % g) * g ^ d
        = (∑ i ∈ Finset.range d, bgDigit g b N i * g ^ i)
            + (b + N / g ^ d % g + bgCarry g b N d) * g ^ d := by ring
      _ = (∑ i ∈ Finset.range d, bgDigit g b N i * g ^ i)
            + (bgDigit g b N d + g * bgCarry g b N (d + 1)) * g ^ d := by rw [hdiv]
      _ = (∑ i ∈ Finset.range d, bgDigit g b N i * g ^ i) + bgDigit g b N d * g ^ d
            + bgCarry g b N (d + 1) * g ^ (d + 1) := by rw [pow_succ]; ring

/-- **The bridge.**  The leading digit of the order-`(i+1)` residue is the digit the
adder emits at position `i`. -/
theorem bgResidue_div_eq_bgDigit (g a B m i : ℕ) (hg : 2 ≤ g) :
    bgResidue g a B m (i + 1) / g ^ i = bgDigit g (m * a % (g - 1)) (m * B) i := by
  set b := m * a % (g - 1) with hb
  set N := m * B with hN
  have hsplit := bg_add_split g b N hg (i + 1)
  have hlt := bg_sum_lt g b N hg (i + 1)
  have h1 : (b * repunit g (i + 1) + N) % g ^ (i + 1)
      = (b * repunit g (i + 1) + N % g ^ (i + 1)) % g ^ (i + 1) := by
    conv_lhs => rw [Nat.add_mod]
    conv_rhs => rw [Nat.add_mod]
    simp [Nat.mod_mod]
  have hmod : (b * repunit g (i + 1) + N) % g ^ (i + 1)
      = ∑ j ∈ Finset.range (i + 1), bgDigit g b N j * g ^ j := by
    rw [h1, hsplit, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  rw [bgResidue, ← hb, ← hN, hmod, Finset.sum_range_succ]
  have hg0 : 0 < g ^ i := by positivity
  have hlt' := bg_sum_lt g b N hg i
  rw [Nat.add_mul_div_right _ _ hg0, Nat.div_eq_of_lt hlt']
  omega

/-- Once `N` has run out, the emitted digit is the background `b` or `b + 1`. -/
theorem bgDigit_of_lt (g b N i : ℕ) (hg : 2 ≤ g) (hb : b + 1 < g) (hN : N < g ^ i) :
    bgDigit g b N i = b ∨ bgDigit g b N i = b + 1 := by
  have hz : N / g ^ i % g = 0 := by rw [Nat.div_eq_of_lt hN]; simp
  have hc := bgCarry_le_one g b N hg (by omega) i
  rw [bgDigit, hz]
  interval_cases h : bgCarry g b N i
  · left; simp [Nat.mod_eq_of_lt (show b < g by omega)]
  · right; simp [Nat.mod_eq_of_lt hb]

/-! ### The certificate in adder form -/

/-- Every window digit is an emitted adder digit. -/
theorem bgResidue_all_ne (g a B M W D : ℕ) (hg : 2 ≤ g) (ha : a + 2 ≤ g)
    (hlen : ∀ m, m ≤ M → m * B < g ^ D)
    (hdig : ∀ m, m ≤ M → ∀ i, i < D → bgDigit g (m * a % (g - 1)) (m * B) i ≠ W)
    (hback : ∀ m, m ≤ M → m * a % (g - 1) ≠ W ∧ m * a % (g - 1) + 1 ≠ W) :
    ∀ m, m ≤ M → ∀ d, 1 ≤ d → bgResidue g a B m d / g ^ (d - 1) ≠ W := by
  intro m hm d hd
  obtain ⟨i, rfl⟩ : ∃ i, d = i + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [bgResidue_div_eq_bgDigit g a B m i hg]
  rcases Nat.lt_or_ge i D with h | h
  · exact hdig m hm i h
  · have hb1 : m * a % (g - 1) + 1 < g := by
      have : m * a % (g - 1) < g - 1 := Nat.mod_lt _ (by omega)
      omega
    have hND : m * B < g ^ i :=
      lt_of_lt_of_le (hlen m hm) (Nat.pow_le_pow_right (by omega) h)
    rcases bgDigit_of_lt g (m * a % (g - 1)) (m * B) i hg hb1 hND with h' | h'
    · rw [h']; exact (hback m hm).1
    · rw [h']; exact (hback m hm).2

/-- **`k = 1` lower bound, adder form.**  The hypotheses are one condition per
emitted digit position (`hdig`, for `i < D`), the length bound `m B < g^D`, and
the background condition `hback`.  No `hstab`: once the burst runs out the carry
dies on its own. -/
theorem mahler_lower_bound_bg_adder (g a B M W D K : ℕ) (hg : 2 ≤ g) (ha : a + 2 ≤ g)
    (hB : 1 ≤ B) (hW : W < g) (hMK : M * B ≤ g ^ K)
    (hlen : ∀ m, m ≤ M → m * B < g ^ D)
    (hdig : ∀ m, m ≤ M → ∀ i, i < D → bgDigit g (m * a % (g - 1)) (m * B) i ≠ W)
    (hback : ∀ m, m ≤ M → m * a % (g - 1) ≠ W ∧ m * a % (g - 1) + 1 ≠ W) :
    Irrational (bgLiouville g a B) ∧ ∀ m : ℕ, 1 ≤ m → m ≤ M →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt g ((m : ℝ) * bgLiouville g a B) [W] n := by
  have hall := bgResidue_all_ne g a B M W D hg ha hlen hdig hback
  have hblk : blockNatVal g [W] = W := by simp [blockNatVal]
  refine mahler_lower_bound_bg g 1 a B M K hg le_rfl ha hB hMK [W] rfl
    (by intro e he; simp at he; omega) ?_
  intro m hm1 hmM d hd1
  have hgd1 : 0 < g ^ (d - 1) := by positivity
  have hpow : g ^ d = g ^ (d - 1) * g := by rw [← pow_succ, Nat.sub_add_cancel hd1]
  have hne := hall m hmM d hd1
  rw [hblk, pow_one]
  rcases lt_or_gt_of_ne hne with h | h
  · left
    have : bgResidue g a B m d < W * g ^ (d - 1) := by
      rw [Nat.div_lt_iff_lt_mul hgd1] at h; omega
    rw [hpow]
    calc (bgResidue g a B m d + 1) * g ≤ (W * g ^ (d - 1)) * g :=
          Nat.mul_le_mul_right g (by omega)
      _ = W * (g ^ (d - 1) * g) := by ring
  · right
    have : (W + 1) * g ^ (d - 1) ≤ bgResidue g a B m d := by
      have h' : W + 1 ≤ bgResidue g a B m d / g ^ (d - 1) := h
      rw [Nat.le_div_iff_mul_le hgd1] at h'; omega
    rw [hpow]
    calc (W + 1) * (g ^ (d - 1) * g) = ((W + 1) * g ^ (d - 1)) * g := by ring
      _ ≤ bgResidue g a B m d * g := Nat.mul_le_mul_right g this

/-! ### The first uniform brick: `B ≡ −4 (mod g)` clears position `0` up to `Q²` -/

/-- **Position `0` of the `a = 2` family, uniformly in `g`.**  For odd `g ≥ 5`,
`Q = (g−1)/2` and any burst with `B ≡ −4 (mod g)`, the digit the adder emits at
position `0` is never the target `g − 1`, for **every** `m < Q²`.

Writing `m = Q u + r` the digit sum is `2r + m B ≡ 2r − 4m ≡ 2(u − r) (mod g)`,
and `2(u − r) ≡ −1 (mod g)` would force `g ∣ 2(u−r) + 1`, an odd number of
absolute value at most `2Q − 1 = g − 2`.  The threshold `Q² = ⌊g/2⌋²` is exactly
the exact census value of `M(p,1)`. -/
theorem bgDigit_zero_ne (g B m : ℕ) (hg : 5 ≤ g) (hodd : g % 2 = 1)
    (hB : B % g = g - 4) (hlt : m < ((g - 1) / 2) * ((g - 1) / 2)) :
    bgDigit g (m * 2 % (g - 1)) (m * B) 0 ≠ g - 1 := by
  set Q := (g - 1) / 2 with hQdef
  have hgQ : g = 2 * Q + 1 := by omega
  have hQ2 : 2 ≤ Q := by omega
  have hb : m * 2 % (g - 1) = 2 * (m % Q) := by
    rw [show g - 1 = 2 * Q by omega, show m * 2 = 2 * m by ring, Nat.mul_mod_mul_left]
  have hd0 : bgDigit g (m * 2 % (g - 1)) (m * B) 0
      = (2 * (m % Q) + m * B % g) % g := by
    rw [bgDigit, hb, bgCarry_zero, pow_zero, Nat.div_one, Nat.add_zero]
  rw [hd0]
  intro hbad
  rw [Nat.add_mod_mod] at hbad
  -- divisibility form
  set X := 2 * (m % Q) + m * B with hX
  have hdvd : g ∣ X + 1 := by
    refine ⟨X / g + 1, ?_⟩
    have hdm := Nat.div_add_mod X g
    rw [hbad] at hdm
    calc X + 1 = g * (X / g) + (g - 1) + 1 := by omega
      _ = g * (X / g) + g := by omega
      _ = g * (X / g + 1) := by ring
  set u := m / Q with hu
  set r := m % Q with hr
  have hmqr : m = Q * u + r := (Nat.div_add_mod m Q).symm
  have hrQ : r < Q := Nat.mod_lt _ (by omega)
  have huQ : u < Q := by rw [hu, Nat.div_lt_iff_lt_mul (by omega)]; omega
  -- burst congruence
  have hB4 : (g : ℤ) ∣ (B : ℤ) + 4 := by
    obtain ⟨k, hk⟩ : ∃ k, B = g * k + (g - 4) :=
      ⟨B / g, by have := Nat.div_add_mod B g; omega⟩
    refine ⟨(k : ℤ) + 1, ?_⟩
    have hkZ : (B : ℤ) = (g : ℤ) * (k : ℤ) + ((g : ℤ) - 4) := by
      have h3 : ((g * k + (g - 4) : ℕ) : ℤ) = (B : ℤ) := by exact_mod_cast hk.symm
      push_cast [Nat.cast_sub (show 4 ≤ g by omega)] at h3
      linarith
    rw [hkZ]; ring
  have hdvdZ : (g : ℤ) ∣ 2 * (r : ℤ) + (m : ℤ) * (B : ℤ) + 1 := by
    have := Int.natCast_dvd_natCast.2 hdvd
    rw [hX] at this
    push_cast at this
    convert this using 2 <;> ring
  have hmZ : (m : ℤ) = (Q : ℤ) * (u : ℤ) + (r : ℤ) := by exact_mod_cast hmqr
  have hgZ : (g : ℤ) = 2 * (Q : ℤ) + 1 := by exact_mod_cast hgQ
  have hkey : (g : ℤ) ∣ 2 * (u : ℤ) - 2 * (r : ℤ) + 1 := by
    obtain ⟨c, hc⟩ := hB4
    obtain ⟨e, he⟩ := hdvdZ
    exact ⟨e - (m : ℤ) * c + 2 * (u : ℤ),
      by linear_combination he - (m : ℤ) * hc + 4 * hmZ - 2 * (u : ℤ) * hgZ⟩
  have habs : |2 * (u : ℤ) - 2 * (r : ℤ) + 1| < (g : ℤ) := by
    have h1 : (u : ℤ) < (Q : ℤ) := by exact_mod_cast huQ
    have h2 : (r : ℤ) < (Q : ℤ) := by exact_mod_cast hrQ
    have h3 : (0 : ℤ) ≤ (u : ℤ) := Int.natCast_nonneg _
    have h4 : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg _
    rw [abs_lt]; omega
  have := Int.eq_zero_of_abs_lt_dvd hkey habs
  omega

/-! ### Packaged witness, and an instance beyond the previous prime table -/

/-- Adder-form witness, packaged as `M(g,1) > M`. -/
theorem mahler_bg_adder_witness (g a B M W D K : ℕ) (hg : 2 ≤ g) (ha : a + 2 ≤ g)
    (hB : 1 ≤ B) (hW : W < g) (hMK : M * B ≤ g ^ K)
    (hlen : ∀ m, m ≤ M → m * B < g ^ D)
    (hdig : ∀ m, m ≤ M → ∀ i, i < D → bgDigit g (m * a % (g - 1)) (m * B) i ≠ W)
    (hback : ∀ m, m ≤ M → m * a % (g - 1) ≠ W ∧ m * a % (g - 1) + 1 ≠ W) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ M →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt g ((m : ℝ) * α) [W] n :=
  ⟨bgLiouville g a B,
    (mahler_lower_bound_bg_adder g a B M W D K hg ha hB hW hMK hlen hdig hback).1,
    (mahler_lower_bound_bg_adder g a B M W D K hg ha hB hW hMK hlen hdig hback).2⟩

/-- **`M(29,1) ≥ 140`**, a new point on the prime lower side, from the adder-form
certificate.  The burst `B = 3273893` was produced by the digit-by-digit search
(`experiments/mahler_burst_tower.py`); it satisfies the uniform law
`B ≡ −4 (mod 29)` of `bgDigit_zero_ne`, and `140 = 0.71·⌊29/2⌋²`. -/
theorem mahler_lower_bound_base29 :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 139 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 29 ((m : ℝ) * α) [28] n :=
  mahler_bg_adder_witness 29 2 3273893 139 28 6 6 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end NormalNumbers.Mahler
