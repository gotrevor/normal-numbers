/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Dioph
import NormalNumbers.VandeheyS7Hecke

/-!
# S7-X: the arithmetic of `Φ` — a good scale for `φx` is a BAD scale for `x`

Lap 34 localized the crux's remaining content: of the `≍ log Q / log T` scales that *could* carry a
primitive `T`-good denominator for the image `y = φ x`, only a `1/T` fraction may.  Nothing about
the size, shape or normalization of the target sets is left open — what is missing is a link
between the expansion of `x` and *which* `q` are good.  Lap 30's directive called that the missing
handle and instructed: attack the arithmetic of `Φ`.

This module supplies such a link, unconditionally, from the one arithmetic fact about `φ` that the
repo already has in the kernel (`abs_sub_mul_goldenRatio_ge : |p − mφ| ≥ 1/(4m)`).

## The transfer

`φ` is a **unit** of `ℤ[φ]` with `φ⁻¹ = φ − 1`.  So a good approximation of `qφx` propagates:

  `q φ x = m + δ`  ⟹  `q x = (m + δ)(φ − 1) = (mφ − m) + δ(φ − 1)`,

and `mφ − m` is an integer translate of `mφ`, whose distance to `ℤ` is `≥ 1/(4m)` because `φ` is a
*badly approximable* quadratic unit.  With `m ≤ 2q` this gives

  `‖q x‖ ≥ 1/(8q) − (φ−1)·‖q φ x‖`   (`nearInt_mul_ge_of_good`),

so for `T ≥ 32` a `T`-good denominator of `φx` satisfies `‖q x‖ ≥ 1/(16 q)`: **it approximates `x`
badly.**  The immediate consequence at the convergents of `x`
(`digit_le_of_good_at_convergent`): if `q = qᵢ(x)` is `T`-good for `φx` then `aᵢ(x) ≤ 32`.

## What this is, and what it is not

It IS the first statement in this project that ties the good set `{q : ‖qφx‖ small}` to the
expansion of `x` — a *negative* correlation, and exactly the shape one wants: the image's large
digits can only occur at scales where `x`'s own digit is small.  It is NOT yet the counting bound:
the `q` that are `T`-good need not be convergent denominators of `x` at all (they are convergent
denominators of `φx`), and this constrains only those that are.  The next step is therefore to run
the same unit trick at the *state* level — `q` is `qₚ(φx)`, and `‖qx‖ ≥ 1/(16q)` says the point
`q(x, φx)` of the orbit avoids a fixed neighbourhood — rather than at `x`'s own convergents.

## Guard rule

Content locator: `nearInt_mul_ge_of_good` at `T = 32` is the stated `1/(16q)`, and the inequality it
comes from degrades continuously in `T` — at `T ≤ 16` it says nothing, which is correct since
`‖qx‖` really can be small when `‖qφx‖ ≈ 1/(8q)`.  Degenerate cases: `m = 0` is excluded by
hypothesis (then `qφx` itself is tiny and there is no constraint — it happens only for
`q < 1/(2φx)`, finitely many `q`); `nearInt_mul_fract` records that the whole statement is
insensitive to replacing `φx` by its fractional part, which is the form the frozen §7 targets use.
-/

namespace NormalNumbers.VandeheyS7

open NormalNumbers

/-! ## `nearInt` housekeeping -/

lemma nearInt_add_int (r : ℝ) (k : ℤ) : nearInt (r + k) = nearInt r := by
  rw [nearInt, nearInt, round_add_intCast]
  push_cast
  ring_nf

/-- The transfer is insensitive to taking fractional parts, so it applies to the frozen §7
targets, which are stated for `Int.fract (q x + r₀)`. -/
lemma nearInt_mul_fract (q : ℕ) (r : ℝ) :
    nearInt ((q : ℝ) * Int.fract r) = nearInt ((q : ℝ) * r) := by
  have hid : (q : ℝ) * Int.fract r = (q : ℝ) * r + (-(q * ⌊r⌋) : ℤ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [hid, nearInt_add_int]

/-- `nearInt` is `1`-Lipschitz, in the form needed: a nearby point cannot be much closer to `ℤ`. -/
lemma nearInt_ge_sub (a b : ℝ) : nearInt b - |a - b| ≤ nearInt a := by
  have h : nearInt b ≤ |b - (round a : ℝ)| := nearInt_le b (round a)
  have h2 : |b - (round a : ℝ)| ≤ |b - a| + |a - (round a : ℝ)| := abs_sub_le _ _ _
  rw [abs_sub_comm b a] at h2
  have h3 : |a - (round a : ℝ)| = nearInt a := rfl
  linarith

/-- **The arithmetic fact about `φ`**, in `nearInt` form: `‖mφ‖ ≥ 1/(4m)`. -/
theorem nearInt_goldenRatio_ge {m : ℤ} (hm : 0 < m) :
    1 / (4 * (m : ℝ)) ≤ nearInt ((m : ℝ) * Real.goldenRatio) := by
  have h := abs_sub_mul_goldenRatio_ge (p := round ((m : ℝ) * Real.goldenRatio)) hm
  rw [nearInt, abs_sub_comm]
  exact h

/-! ## The transfer -/

/-- **A `T`-good denominator for `φx` approximates `x` badly.**  For `T ≥ 32`,
`‖q φ x‖ ≤ 2/(Tq)` forces `‖q x‖ ≥ 1/(16 q)`.

The mechanism is that `φ` is a unit (`φ⁻¹ = φ − 1`) and badly approximable
(`nearInt_goldenRatio_ge`): the good approximation `m` of `qφx` transports to the *bad* target
`mφ − m` for `qx`. -/
theorem nearInt_mul_ge_of_good {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {T q : ℕ}
    (hT : 32 ≤ T) (hq : 1 ≤ q)
    (hm : 0 < round ((q : ℝ) * (Real.goldenRatio * x)))
    (hgood : nearInt ((q : ℝ) * (Real.goldenRatio * x)) ≤ 2 / ((T : ℝ) * q)) :
    1 / (16 * (q : ℝ)) ≤ nearInt ((q : ℝ) * x) := by
  have hφ2 : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hφ1 : 1 < Real.goldenRatio := Real.one_lt_goldenRatio
  have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have hTR : (32:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT
  set m := round ((q : ℝ) * (Real.goldenRatio * x)) with hmdef
  set δ := (q : ℝ) * (Real.goldenRatio * x) - (m : ℝ) with hδ
  have hδabs : |δ| ≤ 2 / ((T : ℝ) * q) := hgood
  -- `m ≤ 2q`, by integrality
  have hmhalf : |δ| ≤ 1/2 := abs_sub_round _
  have hmlt : (m : ℝ) < 2 * (q:ℝ) + 1 := by
    have h1 : (q : ℝ) * (Real.goldenRatio * x) < 2 * (q:ℝ) := by
      have : Real.goldenRatio * x < 2 := by nlinarith
      nlinarith
    have h2 : (m:ℝ) ≤ (q : ℝ) * (Real.goldenRatio * x) + 1/2 := by
      have := abs_le.1 hmhalf
      linarith [this.1, this.2]
    linarith
  have hmle : m ≤ 2 * (q:ℤ) := by
    have : (m : ℝ) < ((2 * (q:ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
    have hlt : m < 2 * (q:ℤ) + 1 := by exact_mod_cast this
    omega
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmR2 : (m:ℝ) ≤ 2 * (q:ℝ) := by exact_mod_cast hmle
  -- the unit identity: `q x = (mφ − m) + δ(φ − 1)`
  have hunit : (q:ℝ) * x
      = ((m : ℝ) * Real.goldenRatio + (-m : ℤ)) + δ * (Real.goldenRatio - 1) := by
    have hexp : ((m : ℝ) + δ) * (Real.goldenRatio - 1)
        = (q : ℝ) * (Real.goldenRatio * x) * (Real.goldenRatio - 1) := by
      rw [hδ]; ring
    have hcollapse : (q : ℝ) * (Real.goldenRatio * x) * (Real.goldenRatio - 1) = (q:ℝ) * x := by
      have : Real.goldenRatio * (Real.goldenRatio - 1) = 1 := by nlinarith [hsq]
      calc (q : ℝ) * (Real.goldenRatio * x) * (Real.goldenRatio - 1)
          = (q:ℝ) * x * (Real.goldenRatio * (Real.goldenRatio - 1)) := by ring
        _ = (q:ℝ) * x := by rw [this]; ring
    push_cast
    nlinarith [hexp, hcollapse]
  -- transport the lower bound
  have hgolden : 1 / (4 * (m : ℝ)) ≤ nearInt ((m : ℝ) * Real.goldenRatio) :=
    nearInt_goldenRatio_ge hm
  have hshift : nearInt ((m : ℝ) * Real.goldenRatio + (-m : ℤ))
      = nearInt ((m : ℝ) * Real.goldenRatio) := nearInt_add_int _ _
  have hclose : |(q:ℝ) * x - ((m : ℝ) * Real.goldenRatio + (-m : ℤ))|
      = |δ| * (Real.goldenRatio - 1) := by
    rw [hunit]
    have : ((m : ℝ) * Real.goldenRatio + (-m : ℤ)) + δ * (Real.goldenRatio - 1)
        - ((m : ℝ) * Real.goldenRatio + (-m : ℤ)) = δ * (Real.goldenRatio - 1) := by ring
    rw [this, abs_mul, abs_of_pos (by linarith : (0:ℝ) < Real.goldenRatio - 1)]
  have hlip := nearInt_ge_sub ((q:ℝ) * x) ((m : ℝ) * Real.goldenRatio + (-m : ℤ))
  rw [hshift, hclose] at hlip
  -- arithmetic: `1/(4m) ≥ 1/(8q)` and `|δ|(φ−1) ≤ 2/(32q) = 1/(16q)`
  have hA : 1 / (8 * (q:ℝ)) ≤ 1 / (4 * (m:ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hB : |δ| * (Real.goldenRatio - 1) ≤ 1 / (16 * (q:ℝ)) := by
    have h1 : |δ| ≤ 2 / ((32:ℝ) * q) := by
      refine le_trans hδabs ?_
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    have h2 : (Real.goldenRatio - 1) ≤ 1 := by linarith
    have h3 : (0:ℝ) ≤ |δ| := abs_nonneg _
    calc |δ| * (Real.goldenRatio - 1) ≤ |δ| * 1 := by nlinarith
      _ = |δ| := by ring
      _ ≤ 2 / ((32:ℝ) * q) := h1
      _ = 1 / (16 * (q:ℝ)) := by ring
  have hgoal : 1 / (8 * (q:ℝ)) - 1 / (16 * (q:ℝ)) = 1 / (16 * (q:ℝ)) := by
    field_simp
    ring
  linarith [hlip, hgolden, hA, hB, hgoal]

/-! ## The additive target `x + φ`

The second frozen §7 target is `x + φ`, where the same phenomenon appears with no unit trick at
all: `q(x+φ)` near `ℤ` and `qφ` far from `ℤ` force `qx` far from `ℤ`.  Both frozen targets
therefore obey the same negative correlation, from the same single fact about `φ`. -/

/-- `nearInt` is subadditive under subtraction. -/
lemma nearInt_sub_le (a b : ℝ) : nearInt (a - b) ≤ nearInt a + nearInt b := by
  have h := nearInt_le (a - b) (round a - round b)
  have hid : a - b - ((round a - round b : ℤ) : ℝ)
      = (a - (round a : ℝ)) - (b - (round b : ℝ)) := by push_cast; ring
  rw [hid] at h
  exact le_trans h (le_trans (abs_sub _ _) (le_of_eq rfl))

/-- **The additive transfer.**  For `T ≥ 16`, a `T`-good denominator for `x + φ` satisfies
`‖q x‖ ≥ 1/(8q)`: it approximates `x` badly.  Same conclusion as the multiplicative case
(`nearInt_mul_ge_of_good`), from the same arithmetic input `‖qφ‖ ≥ 1/(4q)`. -/
theorem nearInt_mul_ge_of_good_add {x : ℝ} {T q : ℕ} (hT : 16 ≤ T) (hq : 1 ≤ q)
    (hgood : nearInt ((q : ℝ) * (x + Real.goldenRatio)) ≤ 2 / ((T : ℝ) * q)) :
    1 / (8 * (q : ℝ)) ≤ nearInt ((q : ℝ) * x) := by
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have hTR : (16:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT
  have hqZ : (0:ℤ) < (q:ℤ) := by exact_mod_cast hq
  have hphi : 1 / (4 * (q:ℝ)) ≤ nearInt ((q : ℝ) * Real.goldenRatio) := by
    have h := nearInt_goldenRatio_ge hqZ
    simpa using h
  have hsplit : (q : ℝ) * Real.goldenRatio
      = (q : ℝ) * (x + Real.goldenRatio) - (q : ℝ) * x := by ring
  have hsub : nearInt ((q : ℝ) * Real.goldenRatio)
      ≤ nearInt ((q : ℝ) * (x + Real.goldenRatio)) + nearInt ((q : ℝ) * x) := by
    rw [hsplit]
    exact nearInt_sub_le _ _
  have hsmall : 2 / ((T : ℝ) * q) ≤ 1 / (8 * (q:ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have harith : 1 / (4 * (q:ℝ)) - 1 / (8 * (q:ℝ)) = 1 / (8 * (q:ℝ)) := by
    field_simp
    ring
  linarith [hphi, hsub, hgood, hsmall, harith]

/-- The additive analogue of `digit_le_of_good_at_convergent`: a convergent denominator of `x` that
is `T`-good for `x + φ` sits at a digit `≤ 16`. -/
theorem digit_le_of_good_at_convergent_add {x : ℝ} (hx : Irrational x)
    (hmem : x ∈ Set.Ioo (0:ℝ) 1) {T i : ℕ} (hT : 16 ≤ T) (hi : 1 ≤ i)
    (hgood : nearInt ((cfK (digitWord x i) : ℝ) * (x + Real.goldenRatio))
      ≤ 2 / ((T : ℝ) * (cfK (digitWord x i) : ℝ))) :
    cfDigit x i ≤ 16 := by
  have hq1 : 1 ≤ cfK (digitWord x i) := one_le_cfK _ (digitWord_pos hx hmem i)
  have hbad := nearInt_mul_ge_of_good_add hT hq1 hgood
  have hgoodx : nearInt ((cfK (digitWord x i) : ℝ) * x)
      ≤ 2 / (cfK (digitWord x (i + 1)) : ℝ) :=
    le_trans (nearInt_le _ (cfNum (digitWord x i) : ℤ)) (abs_convDen_mul_sub_le hx hmem hi)
  have hqR : (1:ℝ) ≤ (cfK (digitWord x i) : ℝ) := by exact_mod_cast hq1
  have hvR : (0:ℝ) < (cfK (digitWord x (i + 1)) : ℝ) :=
    cfK_pos (digitWord_pos hx hmem (i + 1))
  have hchain : 1 / (8 * (cfK (digitWord x i) : ℝ)) ≤ 2 / (cfK (digitWord x (i + 1)) : ℝ) := by
    linarith
  rw [div_le_div_iff₀ (by positivity) hvR] at hchain
  have hle : (cfK (digitWord x (i + 1)) : ℝ) ≤ 16 * (cfK (digitWord x i) : ℝ) := by linarith
  have hleN : cfK (digitWord x (i + 1)) ≤ 16 * cfK (digitWord x i) := by
    have : ((cfK (digitWord x (i + 1)) : ℕ) : ℝ) ≤ ((16 * cfK (digitWord x i) : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  have hrec : cfK (digitWord x (i + 1))
      = cfDigit x i * cfK (digitWord x i) + cfK (digitWord x i).dropLast := by
    rw [digitWord_succ, cfK_concat _ _ (digitWord_ne_nil hi)]
  have hdl : 1 ≤ cfK (digitWord x i).dropLast :=
    one_le_cfK _ fun a ha => digitWord_pos hx hmem i a (List.mem_of_mem_dropLast ha)
  have hmul : cfDigit x i * cfK (digitWord x i) ≤ 16 * cfK (digitWord x i) := by omega
  exact Nat.le_of_mul_le_mul_right (by omega) (Nat.lt_of_lt_of_le Nat.zero_lt_one hq1)

/-! ## The consequence at `x`'s own convergents -/

/-- **The negative correlation.**  If a convergent denominator `qᵢ(x)` of `x` itself is a `T`-good
denominator for `φ x` (`T ≥ 32`), then `x`'s digit there is small: `aᵢ(x) ≤ 32`.

So the image's large digits can only be produced at scales where `x`'s own expansion is *not*
making a large step — the first link in this project between the expansion of `x` and the good
set. -/
theorem digit_le_of_good_at_convergent {x : ℝ} (hx : Irrational x)
    (hmem : x ∈ Set.Ioo (0:ℝ) 1) {T i : ℕ} (hT : 32 ≤ T) (hi : 1 ≤ i)
    (hm : 0 < round ((cfK (digitWord x i) : ℝ) * (Real.goldenRatio * x)))
    (hgood : nearInt ((cfK (digitWord x i) : ℝ) * (Real.goldenRatio * x))
      ≤ 2 / ((T : ℝ) * (cfK (digitWord x i) : ℝ))) :
    cfDigit x i ≤ 32 := by
  have hq1 : 1 ≤ cfK (digitWord x i) := one_le_cfK _ (digitWord_pos hx hmem i)
  have hbad := nearInt_mul_ge_of_good hmem.1 hmem.2 hT hq1 hm hgood
  -- but a convergent denominator approximates `x` well
  have hgoodx : nearInt ((cfK (digitWord x i) : ℝ) * x)
      ≤ 2 / (cfK (digitWord x (i + 1)) : ℝ) :=
    le_trans (nearInt_le _ (cfNum (digitWord x i) : ℤ)) (abs_convDen_mul_sub_le hx hmem hi)
  have hqR : (1:ℝ) ≤ (cfK (digitWord x i) : ℝ) := by exact_mod_cast hq1
  have hvR : (0:ℝ) < (cfK (digitWord x (i + 1)) : ℝ) :=
    cfK_pos (digitWord_pos hx hmem (i + 1))
  -- `1/(16 q) ≤ 2/q_{i+1}` forces `q_{i+1} ≤ 32 q`
  have hchain : 1 / (16 * (cfK (digitWord x i) : ℝ)) ≤ 2 / (cfK (digitWord x (i + 1)) : ℝ) := by
    linarith
  rw [div_le_div_iff₀ (by positivity) hvR] at hchain
  have hle : (cfK (digitWord x (i + 1)) : ℝ) ≤ 32 * (cfK (digitWord x i) : ℝ) := by linarith
  have hleN : cfK (digitWord x (i + 1)) ≤ 32 * cfK (digitWord x i) := by
    have : ((cfK (digitWord x (i + 1)) : ℕ) : ℝ) ≤ ((32 * cfK (digitWord x i) : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  -- and `q_{i+1} ≥ aᵢ qᵢ`
  have hrec : cfK (digitWord x (i + 1))
      = cfDigit x i * cfK (digitWord x i) + cfK (digitWord x i).dropLast := by
    rw [digitWord_succ, cfK_concat _ _ (digitWord_ne_nil hi)]
  have hdl : 1 ≤ cfK (digitWord x i).dropLast :=
    one_le_cfK _ fun a ha => digitWord_pos hx hmem i a (List.mem_of_mem_dropLast ha)
  have hmul : cfDigit x i * cfK (digitWord x i) ≤ 32 * cfK (digitWord x i) := by omega
  exact Nat.le_of_mul_le_mul_right (by omega) (Nat.lt_of_lt_of_le Nat.zero_lt_one hq1)

/-! ## The numerator of a good approximation is an *anti*-good denominator

One more consequence of `φ` being a unit, and the sharpest structural constraint this module
produces.  If `q` is primitive `T`-good for `φx` with numerator `m`, then

  `m φ x = m²/q + mδ/q`   (again because `φ(φ−1) = 1`),

and `m²/q` is a rational with denominator `q` whose numerator is coprime to `q`, hence at distance
`≥ 1/q` from `ℤ`.  So `‖m φ x‖ ≥ 1/(2q)`: the numerator `m ≍ q` is a *badly* approximating
denominator for the very same number.  Good denominators therefore come in pairs `(q, m)` whose
second coordinate is excluded from the good set — a constraint on the good set that uses the
arithmetic of `φ` and not the orbit at all.
-/

/-- A rational with denominator `q` that is not an integer is `≥ 1/q` from `ℤ`. -/
lemma nearInt_div_nat_ge {k : ℤ} {q : ℕ} (hq : 1 ≤ q) (hdvd : ¬ ((q:ℤ) ∣ k)) :
    1 / (q : ℝ) ≤ nearInt ((k : ℝ) / (q : ℝ)) := by
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  set r := round ((k : ℝ) / (q : ℝ)) with hr
  have hne : k - (q:ℤ) * r ≠ 0 := by
    intro h
    exact hdvd ⟨r, by linarith [sub_eq_zero.1 h]⟩
  have habs : (1:ℝ) ≤ |((k - (q:ℤ) * r : ℤ) : ℝ)| := by
    have h1 : (1:ℤ) ≤ |k - (q:ℤ) * r| := Int.one_le_abs hne
    have : ((|k - (q:ℤ) * r| : ℤ) : ℝ) ≥ 1 := by exact_mod_cast h1
    rwa [Int.cast_abs] at this
  have hid : (k : ℝ) / (q : ℝ) - (r : ℝ) = ((k - (q:ℤ) * r : ℤ) : ℝ) / (q:ℝ) := by
    push_cast
    field_simp
  rw [nearInt, hid, abs_div, abs_of_pos hqR]
  gcongr

/-- **The numerator is an anti-good denominator.**  For `T ≥ 8` and a primitive `T`-good `q ≥ 2`
for `φ x`, the numerator `m = round(q φ x)` satisfies `‖m φ x‖ ≥ 1/(2q)`. -/
theorem nearInt_numerator_ge_of_good {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {T q : ℕ}
    (hT : 8 ≤ T) (hq : 2 ≤ q)
    (hm : 0 < round ((q : ℝ) * (Real.goldenRatio * x)))
    (hcop : Nat.Coprime (round ((q : ℝ) * (Real.goldenRatio * x))).natAbs q)
    (hgood : nearInt ((q : ℝ) * (Real.goldenRatio * x)) ≤ 2 / ((T : ℝ) * q)) :
    1 / (2 * (q : ℝ)) ≤
      nearInt ((round ((q : ℝ) * (Real.goldenRatio * x)) : ℝ) * (Real.goldenRatio * x)) := by
  have hφ2 : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hφ1 : 1 < Real.goldenRatio := Real.one_lt_goldenRatio
  have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have hqR : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have hTR : (8:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT
  set m := round ((q : ℝ) * (Real.goldenRatio * x)) with hmdef
  set δ := (q : ℝ) * (Real.goldenRatio * x) - (m : ℝ) with hδ
  have hδabs : |δ| ≤ 2 / ((T : ℝ) * q) := hgood
  -- `m ≤ 2q`, as in `nearInt_mul_ge_of_good`
  have hmhalf : |δ| ≤ 1/2 := abs_sub_round _
  have hmlt : (m : ℝ) < 2 * (q:ℝ) + 1 := by
    have h1 : (q : ℝ) * (Real.goldenRatio * x) < 2 * (q:ℝ) := by
      have : Real.goldenRatio * x < 2 := by nlinarith
      nlinarith
    have h2 : (m:ℝ) ≤ (q : ℝ) * (Real.goldenRatio * x) + 1/2 := by
      have := abs_le.1 hmhalf
      linarith [this.1, this.2]
    linarith
  have hmle : m ≤ 2 * (q:ℤ) := by
    have h : (m : ℝ) < ((2 * (q:ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
    have hlt : m < 2 * (q:ℤ) + 1 := by exact_mod_cast h
    omega
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmR2 : (m:ℝ) ≤ 2 * (q:ℝ) := by exact_mod_cast hmle
  -- the unit identity `m φ x = m²/q + m δ/q`
  have hcol : Real.goldenRatio * (Real.goldenRatio - 1) = 1 := by nlinarith [hsq]
  have hsum : (m : ℝ) + δ = (q : ℝ) * (Real.goldenRatio * x) := by rw [hδ]; ring
  have hqx : ((m : ℝ) + δ) * (Real.goldenRatio - 1) = (q : ℝ) * x := by
    rw [hsum]
    calc (q : ℝ) * (Real.goldenRatio * x) * (Real.goldenRatio - 1)
        = (q : ℝ) * x * (Real.goldenRatio * (Real.goldenRatio - 1)) := by ring
      _ = (q : ℝ) * x := by rw [hcol]; ring
  have hmul : (q : ℝ) * ((m : ℝ) * (Real.goldenRatio * x)) = (m:ℝ) * (m:ℝ) + (m:ℝ) * δ := by
    have hre : (q : ℝ) * ((m : ℝ) * (Real.goldenRatio * x))
        = (m : ℝ) * Real.goldenRatio * ((q : ℝ) * x) := by ring
    rw [hre, ← hqx]
    linear_combination ((m:ℝ) * ((m:ℝ) + δ)) * hcol
  have hkey : (m : ℝ) * (Real.goldenRatio * x)
      = ((m * m : ℤ) : ℝ) / (q:ℝ) + (m : ℝ) * δ / (q:ℝ) := by
    have hcomb : ((m * m : ℤ) : ℝ) / (q:ℝ) + (m : ℝ) * δ / (q:ℝ)
        = (((m:ℝ) * (m:ℝ) + (m:ℝ) * δ)) / (q:ℝ) := by push_cast; ring
    rw [hcomb, eq_div_iff (ne_of_gt hqpos)]
    linear_combination hmul
  -- `q ∤ m²` by primitivity
  have hdvd : ¬ ((q:ℤ) ∣ m * m) := by
    intro hd
    have hnat : q ∣ (m * m).natAbs := by
      have h := Int.natAbs_dvd_natAbs.2 hd
      simpa using h
    have hcop2 : Nat.Coprime (m.natAbs * m.natAbs) q := Nat.Coprime.mul_left hcop hcop
    have hdd : q ∣ m.natAbs * m.natAbs := by rwa [Int.natAbs_mul] at hnat
    have hq1 : q = 1 := Nat.Coprime.eq_one_of_dvd hcop2.symm hdd
    omega
  have hrat : 1 / (q:ℝ) ≤ nearInt (((m * m : ℤ) : ℝ) / (q:ℝ)) :=
    nearInt_div_nat_ge (by omega) hdvd
  -- transport
  have hclose : |(m : ℝ) * (Real.goldenRatio * x) - ((m * m : ℤ) : ℝ) / (q:ℝ)|
      = |(m : ℝ) * δ| / (q:ℝ) := by
    rw [hkey]
    have : ((m * m : ℤ) : ℝ) / (q:ℝ) + (m : ℝ) * δ / (q:ℝ) - ((m * m : ℤ) : ℝ) / (q:ℝ)
        = (m : ℝ) * δ / (q:ℝ) := by ring
    rw [this, abs_div, abs_of_pos hqpos]
  have hlip := nearInt_ge_sub ((m : ℝ) * (Real.goldenRatio * x)) (((m * m : ℤ) : ℝ) / (q:ℝ))
  rw [hclose] at hlip
  -- `|m δ|/q ≤ 2q·(2/(Tq))/q = 4/(Tq) ≤ 1/(2q)`
  have hmδ : |(m : ℝ) * δ| / (q:ℝ) ≤ 1 / (2 * (q:ℝ)) := by
    have h1 : |(m : ℝ) * δ| = (m:ℝ) * |δ| := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ (m:ℝ))]
    rw [h1]
    have h2 : (m:ℝ) * |δ| ≤ 2 * (q:ℝ) * (2 / ((T : ℝ) * q)) := by
      have h3 : (0:ℝ) ≤ |δ| := abs_nonneg _
      have h4 : (0:ℝ) ≤ 2 / ((T : ℝ) * q) := by positivity
      nlinarith [hδabs, hmR2]
    have h5 : 2 * (q:ℝ) * (2 / ((T : ℝ) * q)) = 4 / (T:ℝ) := by
      field_simp
      ring
    rw [h5] at h2
    have h6 : 4 / (T:ℝ) / (q:ℝ) ≤ 1 / (2 * (q:ℝ)) := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc (m:ℝ) * |δ| / (q:ℝ) ≤ (4 / (T:ℝ)) / (q:ℝ) := by gcongr
      _ ≤ 1 / (2 * (q:ℝ)) := h6
  have harith : 1 / (q:ℝ) - 1 / (2 * (q:ℝ)) = 1 / (2 * (q:ℝ)) := by
    field_simp
    ring
  linarith [hlip, hrat, hmδ, harith]

section Audit

#print axioms nearInt_add_int
#print axioms nearInt_mul_fract
#print axioms nearInt_ge_sub
#print axioms nearInt_goldenRatio_ge
#print axioms nearInt_mul_ge_of_good
#print axioms digit_le_of_good_at_convergent
#print axioms nearInt_sub_le
#print axioms nearInt_mul_ge_of_good_add
#print axioms digit_le_of_good_at_convergent_add
#print axioms nearInt_div_nat_ge
#print axioms nearInt_numerator_ge_of_good

end Audit

end NormalNumbers.VandeheyS7
