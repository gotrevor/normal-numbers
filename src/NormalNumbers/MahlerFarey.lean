/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerPrimeHalf

/-!
# Farey separation: the shadow of quality `1/(2Q)` is unique 🧮

Infrastructure for the multi-scale attack on the prime-base upper bound
(`DIRECTION.md`'s named next move, and the remaining factor `2` localized in
`PENDING_WORK.md`).

The covering method as used in `MahlerMultiplier.lean` and
`MahlerPrimeHalf.lean` follows ONE rational shadow `ρ` forward under `×g`, and
its whole strength is spent at the single time where the shadow's defect last
sits below `1/Q`.  What it never uses is the times where the shadow has already
LEFT that window: there `x_n` is no longer close to `ρ`, but it is close to some
*other* rational — a Farey neighbour of larger denominator — which carries its
own covering constraint.  Turning "the orbit visits every scale" into a
conjunction of constraints is the attack; this file is its first brick.

* `defect_pair_ge` — for distinct rationals `p/q ≠ p'/q'`,
  `q'·|qx − p| + q·|q'x − p'| ≥ 1`.  (One line, from `|pq' − p'q| ≥ 1`: the
  integer is nonzero, and it telescopes as `q'(p − qx) + q(q'x − p')`.)
* `approx_unique` — hence at most one rational of denominator `≤ Q` has defect
  `< 1/(2Q)` at any given `x`: the "quality `1/(2Q)` shadow" is a *function* of
  `x`, not a choice.
* `orbit_approx_unique` — the same, stated on the orbit, which is where the
  escape argument needs it: the shadow chain of `orbit_escapes` is forced, so a
  constraint derived at one time cannot be dodged by switching shadows.
-/

namespace NormalNumbers.Mahler

open NormalNumbers

/-- **Farey separation, defect form.**  If `p/q` and `p'/q'` are distinct
rationals (`p q' ≠ p' q`) with `q, q' ≥ 1`, then for every real `x`

    `q'·|q x − p| + q·|q' x − p'| ≥ 1`.

Two rationals of denominators `q, q'` are at distance `≥ 1/(q q')`, and a real
cannot be nearer than half of that to both. -/
theorem defect_pair_ge (x : ℝ) (p p' : ℤ) (q q' : ℕ) (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hne : p * (q' : ℤ) ≠ p' * (q : ℤ)) :
    1 ≤ (q' : ℝ) * |(q : ℝ) * x - p| + (q : ℝ) * |(q' : ℝ) * x - p'| := by
  have hqR : (0 : ℝ) ≤ q := by positivity
  have hq'R : (0 : ℝ) ≤ q' := by positivity
  -- the integer `p q' − p' q` is nonzero, hence of absolute value at least one
  have hZ : (1 : ℤ) ≤ |p * (q' : ℤ) - p' * (q : ℤ)| := by
    rcases lt_trichotomy (p * (q' : ℤ) - p' * (q : ℤ)) 0 with h | h | h
    · rw [abs_of_neg h]; omega
    · exact absurd (by omega : p * (q' : ℤ) = p' * (q : ℤ)) hne
    · rw [abs_of_pos h]; omega
  have hR : (1 : ℝ) ≤ |(p : ℝ) * q' - p' * q| := by
    have := (Int.cast_le (R := ℝ)).2 hZ
    rwa [Int.cast_abs, Int.cast_one, Int.cast_sub, Int.cast_mul, Int.cast_mul,
      Int.cast_natCast, Int.cast_natCast] at this
  -- and it telescopes
  have htel : (p : ℝ) * q' - p' * q
      = (q' : ℝ) * ((p : ℝ) - q * x) + (q : ℝ) * ((q' : ℝ) * x - p') := by ring
  calc (1 : ℝ) ≤ |(p : ℝ) * q' - p' * q| := hR
    _ = |(q' : ℝ) * ((p : ℝ) - q * x) + (q : ℝ) * ((q' : ℝ) * x - p')| := by rw [htel]
    _ ≤ |(q' : ℝ) * ((p : ℝ) - q * x)| + |(q : ℝ) * ((q' : ℝ) * x - p')| :=
        abs_add_le _ _
    _ = (q' : ℝ) * |(q : ℝ) * x - p| + (q : ℝ) * |(q' : ℝ) * x - p'| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hqR, abs_of_nonneg hq'R,
          show ((p : ℝ) - q * x) = -((q : ℝ) * x - p) by ring, abs_neg]

/-- **Uniqueness of the quality-`1/(2Q)` shadow.**  At most one rational with
denominator `≤ Q` approximates `x` with defect below `1/(2Q)`. -/
theorem approx_unique (x : ℝ) (Q : ℕ) (hQ : 1 ≤ Q) (p p' : ℤ) (q q' : ℕ)
    (hq : 1 ≤ q) (hq' : 1 ≤ q') (hqQ : q ≤ Q) (hq'Q : q' ≤ Q)
    (h : |(q : ℝ) * x - p| < 1 / (2 * Q))
    (h' : |(q' : ℝ) * x - p'| < 1 / (2 * Q)) :
    p * (q' : ℤ) = p' * (q : ℤ) := by
  by_contra hne
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hqR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hq'R : (q' : ℝ) ≤ Q := by exact_mod_cast hq'Q
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hq'0 : (0 : ℝ) ≤ q' := by positivity
  have key := defect_pair_ge x p p' q q' hq hq' hne
  have h1 : (q' : ℝ) * |(q : ℝ) * x - p| ≤ (Q : ℝ) * (1 / (2 * Q)) := by
    apply mul_le_mul hq'R h.le (abs_nonneg _) (by linarith)
  have h2 : (q : ℝ) * |(q' : ℝ) * x - p'| ≤ (Q : ℝ) * (1 / (2 * Q)) := by
    apply mul_le_mul hqR h'.le (abs_nonneg _) (by linarith)
  have hhalf : (Q : ℝ) * (1 / (2 * Q)) = 1 / 2 := by field_simp
  rw [hhalf] at h1 h2
  -- strictness: at least one of the two products is strictly below `1/2`
  have hstrict : (q' : ℝ) * |(q : ℝ) * x - p| < 1 / 2 := by
    rcases eq_or_lt_of_le hq'0 with h0 | h0
    · rw [← h0]; simp only [zero_mul]; norm_num
    · calc (q' : ℝ) * |(q : ℝ) * x - p| < (q' : ℝ) * (1 / (2 * Q)) := by
            exact mul_lt_mul_of_pos_left h h0
        _ ≤ (Q : ℝ) * (1 / (2 * Q)) := by
            apply mul_le_mul_of_nonneg_right hq'R (by positivity)
        _ = 1 / 2 := hhalf
  linarith

/-- **The shadow is forced along the orbit.**  Stated where the escape argument
uses it: at each time `n` there is at most one rational of denominator `≤ Q`
whose defect at `orbit g α n` is below `1/(2Q)`.  So the covering constraints
collected at different times all refer to a canonical shadow — they cannot be
dodged by choosing a different approximation at each scale. -/
theorem orbit_approx_unique (g : ℕ) (α : ℝ) (n Q : ℕ) (hQ : 1 ≤ Q) (ρ σ : ℚ)
    (hρ : ρ.den ≤ Q) (hσ : σ.den ≤ Q)
    (hρd : |(ρ.den : ℝ) * orbit g α n - ρ.num| < 1 / (2 * Q))
    (hσd : |(σ.den : ℝ) * orbit g α n - σ.num| < 1 / (2 * Q)) :
    ρ = σ := by
  have h := approx_unique (orbit g α n) Q hQ ρ.num σ.num ρ.den σ.den ρ.pos σ.pos
    hρ hσ hρd hσd
  exact Rat.eq_iff_mul_eq_mul.2 (by exact_mod_cast h)

/-! ### The denominator-jump engine

The multi-scale argument sketched in `PENDING_WORK.md`.  Fix `Q = gᵏ` and a bad
`x` (no `m ≤ M` puts `m x` in the cell of `W`).  The covering lemma bounds the
defect of EVERY reduced rational of denominator `≤ Q` — in particular the
Dirichlet approximation `σ`, whose defect is therefore not merely `≤ 1/(Q+1)`
but `< 1/(M + 1 − 2Q)`, which is `O(1/M)` and hence tiny.  Farey separation then
says any OTHER rational `p/a` with `a ≤ Q` is seen by `σ` at resolution
`σ.den · |a x − p| ≥ 1 − a · (defect of σ) > 1/2`:

    **a rational that is not the Dirichlet one has its defect bounded BELOW by
    `1/(2 σ.den)`** — equivalently `σ.den ≥ 1 / (2 |a x − p|)`.

That is the engine.  Applied to the shadow chain of `orbit_escapes` at the
moment its defect first leaves the window `[0, 1/Q)`, it forces the Dirichlet
denominator at that time to exceed `(M + 1 − 2a) / (2 g (1 − a/Q))`, i.e. the
canonical denominator JUMPS.  Iterating, the denominators satisfy
`a_{j+1} ≳ (M/g) / (1 − a_j/Q)`, whose fixed points `a(1 − a/Q) = M/g` exist
only when `M ≤ g Q / 4`; above that the denominators increase by at least a
fixed fraction of `Q` per stage and must exceed `Q`, which is impossible.  The
target of that iteration is `M(g,k) ≤ (1/4 + O(1/g))·g^(k+1)` — the constant the
exact values `M(5,1) = 6`, `M(7,1) = 9`, `M(11,1) = 25`, `M(17,1) = 64` sit at.
The chain/exit-time bookkeeping is the remaining work; this file lands the
engine. -/

/-- **The Dirichlet approximation of a bad point has a tiny defect.**  For a bad
`x` the covering lemma applies to every reduced rational of denominator `≤ gᵏ`;
with `M ≥ 4gᵏ` the coefficient `M + 1 − 2q` is at least `2gᵏ + 1`, so the defect
is below `1/(2gᵏ+1)` — an `O(1/M)` bound where Dirichlet alone gives only
`1/(gᵏ+1)`. -/
theorem defect_small_of_bad (g k W M : ℕ) (hg : 2 ≤ g) (hW : W < g ^ k)
    (hM : 4 * g ^ k ≤ M) (x : ℝ) (hx : Irrational x)
    (hbad : ∀ m : ℕ, 1 ≤ m → m ≤ M →
      Int.fract ((m : ℝ) * x) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k))
    (σ : ℚ) (hσden : σ.den ≤ g ^ k)
    (hσ : |(σ.den : ℝ) * x - σ.num| < 1 / (g : ℝ) ^ k) :
    |(σ.den : ℝ) * x - σ.num| < 1 / (2 * (g : ℝ) ^ k + 1) := by
  have hcop : IsCoprime σ.num (σ.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact σ.reduced
  have h := defect_bound_of_bad g k W hg hW M x hx hbad σ.num σ.den σ.pos hσden hcop hσ
  have hQ0 : (0 : ℝ) < (g : ℝ) ^ k := by
    have : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
    positivity
  have hQR : ((g ^ k : ℕ) : ℝ) = (g : ℝ) ^ k := by push_cast; ring
  have hdR : (σ.den : ℝ) ≤ (g : ℝ) ^ k := by rw [← hQR]; exact_mod_cast hσden
  have hMR : 4 * (g : ℝ) ^ k ≤ M := by
    have := (Nat.cast_le (α := ℝ)).2 hM
    rwa [Nat.cast_mul, Nat.cast_ofNat, hQR] at this
  have hcoef : 2 * (g : ℝ) ^ k + 1 ≤ (M : ℝ) + 1 - 2 * σ.den := by linarith
  have hrhs : 1 - (σ.den : ℝ) / (g : ℝ) ^ k ≤ 1 := by
    have : (0 : ℝ) ≤ (σ.den : ℝ) / (g : ℝ) ^ k := by positivity
    linarith
  have hpos : (0 : ℝ) < 2 * (g : ℝ) ^ k + 1 := by linarith
  rw [lt_div_iff₀ hpos]
  nlinarith [abs_nonneg ((σ.den : ℝ) * x - σ.num)]

/-- **The denominator jump.**  For a bad `x` (with `M ≥ 4gᵏ`), any reduced
rational `p/a` with `a ≤ gᵏ` that is *not* the given small-defect rational `σ`
has

    `σ.den · |a x − p| > 1/2`,

i.e. `σ.den > 1 / (2|a x − p|)`.  Farey separation gives
`σ.den·|ax−p| + a·|σ.den x − σ.num| ≥ 1`, and the second term is at most
`gᵏ/(2gᵏ+1) < 1/2` by `defect_small_of_bad`. -/
theorem den_jump_of_bad (g k W M : ℕ) (hg : 2 ≤ g) (hW : W < g ^ k)
    (hM : 4 * g ^ k ≤ M) (x : ℝ) (hx : Irrational x)
    (hbad : ∀ m : ℕ, 1 ≤ m → m ≤ M →
      Int.fract ((m : ℝ) * x) ∉
        Set.Ico ((W : ℝ) / (g : ℝ) ^ k) (((W : ℝ) + 1) / (g : ℝ) ^ k))
    (σ : ℚ) (hσden : σ.den ≤ g ^ k)
    (hσ : |(σ.den : ℝ) * x - σ.num| < 1 / (g : ℝ) ^ k)
    (p : ℤ) (a : ℕ) (ha : 1 ≤ a) (haQ : a ≤ g ^ k)
    (hne : p * (σ.den : ℤ) ≠ σ.num * (a : ℤ)) :
    1 / 2 < (σ.den : ℝ) * |(a : ℝ) * x - p| := by
  have hQ0 : (0 : ℝ) < (g : ℝ) ^ k := by
    have : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
    positivity
  have hQR : ((g ^ k : ℕ) : ℝ) = (g : ℝ) ^ k := by push_cast; ring
  have haR : (a : ℝ) ≤ (g : ℝ) ^ k := by rw [← hQR]; exact_mod_cast haQ
  have hpair := defect_pair_ge x p σ.num a σ.den ha σ.pos hne
  have hsmall := defect_small_of_bad g k W M hg hW hM x hx hbad σ hσden hσ
  have hpos : (0 : ℝ) < 2 * (g : ℝ) ^ k + 1 := by linarith
  have hprod : (a : ℝ) * |(σ.den : ℝ) * x - σ.num| < 1 / 2 := by
    have h1 : (a : ℝ) * |(σ.den : ℝ) * x - σ.num|
        ≤ (g : ℝ) ^ k * |(σ.den : ℝ) * x - σ.num| :=
      mul_le_mul_of_nonneg_right haR (abs_nonneg _)
    have h2 : (g : ℝ) ^ k * |(σ.den : ℝ) * x - σ.num|
        < (g : ℝ) ^ k * (1 / (2 * (g : ℝ) ^ k + 1)) :=
      mul_lt_mul_of_pos_left hsmall hQ0
    have h3 : (g : ℝ) ^ k * (1 / (2 * (g : ℝ) ^ k + 1)) < 1 / 2 := by
      rw [mul_one_div, div_lt_div_iff₀ hpos (by norm_num)]
      linarith
    linarith
  linarith


end NormalNumbers.Mahler
