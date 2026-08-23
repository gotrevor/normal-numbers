/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.RealDefs

/-!
# Stoneham's theorem

R. Stoneham (1973): `α₂,₃ = Σ_{m≥1} 1/(3ᵐ·2^(3ᵐ))` is normal in base 2 —
the only known normality proof for a number defined by an honest analytic
series rather than through its own digits.  (Contrast: Bailey–Borwein 2012
showed `α₂,₃` is *not* normal in base 6 — normality is a property of the
pair (number, base).)

## Proof plan (the self-similar cascade)

Write `W_M = [3^M, 3^(M+1))` for the `M`-th window of orbit times.  For
`n ∈ W_M`, the orbit point `2^n·α mod 1` equals `c_M(n)/3^M + ε_n` with
`0 < ε_n < 2/3^(M+1)` (`stonehamState_approx`), where the integer state
`c_M(n)` (`stonehamState`) doubles mod `3^M` at each step
(`stonehamState_succ`) from a *unit* seed (`stonehamState_unit`).

By `StonehamArith`, 2 generates the full unit group mod `3^M`, of order
`2·3^(M-1)`.  Since `|W_M| = 2·3^M` is exactly three periods, each window
traverses the unit cycle exactly three times: window visit counts to any
interval reduce to counting *units of `ℤ/3^M` in integer intervals*, which
is uniform to `±2` (`card_units_Ico`).

Partial windows (the frontier of the count) are partial cycles, and the
distribution of a partial doubling-cycle is exactly the incomplete-
exponential-sum wall.  The route around it (Bailey–Borwein 2013, via
Bailey–Misiurewicz 2006) is one-sided: a partial cycle's visits are a
*subset* of a full cycle's, so **upper** visit bounds survive with no
cancellation needed (`segment_visit_upper`), and the **strong hot spot
lemma** says one-sided bounds suffice: a non-normal number must have an
interval family visited with frequency exceeding any constant multiple of
its length, which the window counting rules out with an absolute constant.
The hot-spot lemma (`not_isNormal_exists_hotspot`, statement to be pinned
against Bailey–Misiurewicz, Proc. AMS 134 (2006) 2495–2501) is the one
piece of real analysis; everything else is exact counting in `(ℤ/3^M)ˣ`.
No character sums and no Erdős–Turán inequality anywhere.
-/

namespace NormalNumbers

/-- The Stoneham constant `α₂,₃ = Σ_{m≥1} 1/(3ᵐ·2^(3ᵐ))`. -/
noncomputable def stoneham23 : ℝ :=
  ∑' n : ℕ, 1 / ((3 : ℝ) ^ (n + 1) * 2 ^ (3 ^ (n + 1)))

/-- Head of the Stoneham series: terms `m = 1 … M`. -/
noncomputable def stonehamPartial (M : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 M, 1 / ((3 : ℝ) ^ m * 2 ^ (3 ^ m))

/-- The integer orbit state at time `n` in window `M`:
`c_M(n) = (Σ_{m=1}^{M} 3^(M-m)·2^(n-3^m)) mod 3^M`.  Meaningful for
`n ≥ 3^M` (natural subtraction truncates earlier terms harmlessly only
when every `3^m ≤ n`). -/
def stonehamState (M n : ℕ) : ℕ :=
  (∑ m ∈ Finset.Icc 1 M, 3 ^ (M - m) * 2 ^ (n - 3 ^ m)) % 3 ^ M

/-- The state doubles mod `3^M` at each step (once `n ≥ 3^M`). -/
theorem stonehamState_succ (M n : ℕ) (hM : 1 ≤ M) (hn : 3 ^ M ≤ n) :
    stonehamState M (n + 1) = 2 * stonehamState M n % 3 ^ M := by
  sorry

/-- The seed of window `M` is a unit mod `3^M`: only the `m = M` term is
prime to 3. -/
theorem stonehamState_unit (M : ℕ) (hM : 1 ≤ M) :
    ¬ 3 ∣ stonehamState M (3 ^ M) := by
  sorry

/-- Orbit points in window `M` are the rational state plus a positive
error under `2/3^(M+1)`: for `3^M ≤ n < 3^(M+1)`,
`c_M(n)/3^M < 2^n·α mod 1 < c_M(n)/3^M + 2/3^(M+1)`. -/
theorem stonehamState_approx (M n : ℕ) (hM : 1 ≤ M)
    (hn : 3 ^ M ≤ n) (hn' : n < 3 ^ (M + 1)) :
    (stonehamState M n : ℝ) / 3 ^ M < orbit 2 stoneham23 n ∧
      orbit 2 stoneham23 n
        < (stonehamState M n : ℝ) / 3 ^ M + 2 / 3 ^ (M + 1) := by
  sorry

/-- Units of `ℤ/3^M` in an integer interval are uniform to `±2`:
`(q-p)·2/3 - 2 ≤ #{u ∈ [p,q) : ¬3∣u} ≤ (q-p)·2/3 + 2` (stated with
`3·card` to stay in `ℕ`). -/
theorem card_units_Ico (p q : ℕ) (hpq : p ≤ q) :
    2 * (q - p) - 6 ≤ 3 * ((Finset.Ico p q).filter fun u => ¬ 3 ∣ u).card ∧
      3 * ((Finset.Ico p q).filter fun u => ¬ 3 ∣ u).card ≤ 2 * (q - p) + 6 := by
  sorry

/-- **One-sided segment bound**: a doubling-orbit segment of any length
`ℓ` visits an interval at most as often as `⌈ℓ/ord⌉` full unit cycles do —
a partial cycle is a subset of a full one, so no cancellation is needed.
With `ord = 2·3^(M-1)` and the unit-counting bound, the visits to
`[a, c)` are at most `(⌊ℓ/ord⌋ + 1)·((c-a)·2·3^(M-1) + 4)`. -/
theorem segment_visit_upper (M : ℕ) (hM : 1 ≤ M) (u : ℕ)
    (hu : ¬ 3 ∣ u) (a c : ℝ) (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1)
    (ℓ : ℕ) :
    (((Finset.range ℓ).filter fun j =>
        ((u * 2 ^ j % 3 ^ M : ℕ) : ℝ) / 3 ^ M ∈ Set.Ico a c).card : ℝ)
      ≤ (ℓ / (2 * 3 ^ (M - 1)) + 1) * ((c - a) * (2 * 3 ^ (M - 1)) + 4) := by
  sorry

/-- **Strong hot spot lemma** (Bailey–Misiurewicz 2006), contrapositive
form: if there is a constant `C` such that every b-adic interval's visit
frequency has `limsup ≤ C·(its length)`, then `x` is normal.  ⚠️ Statement
shape is provisional — pin it against Proc. AMS 134 (2006) 2495–2501
before proving (the paper works with shrinking neighborhoods of a point;
the b-adic-interval form here should be derived from, not substituted
for, the paper's). -/
theorem isNormal_of_visit_upper_bound (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (C : ℝ)
    (h : ∀ k m : ℕ, m < b ^ k → ∀ᶠ n in Filter.atTop,
      (visitCount (orbit b (Int.fract x)) ((m : ℝ) / (b : ℝ) ^ k)
          ((m + 1 : ℝ) / (b : ℝ) ^ k) n : ℝ) / n ≤ C / (b : ℝ) ^ k) :
    IsNormal b x := by
  sorry

/-- **Stoneham's theorem** (1973): `α₂,₃` is normal in base 2. -/
theorem isNormal_two_stoneham23 : IsNormal 2 stoneham23 := by
  sorry

end NormalNumbers
