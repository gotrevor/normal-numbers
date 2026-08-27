/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.Pillai
import NormalNumbers.Headline
import NormalNumbers.NormalMeager

/-!
# Uniform high-base equidistribution

A **single-limit** sufficient criterion for absolute normality, as an
alternative interface to `pillai`.

`pillai` asks for simple normality at *every* power `b ^ r`: a family of
limits indexed by `r`, each taken as the depth `N → ∞`.  This file asks
instead for one uniform statement as the *base* runs to infinity, measured
in total variation.

## Why total variation

The naive reading "each digit value has frequency `1 / b`" degenerates as
`b → ∞`, because the target `1 / b` vanishes: a sup-norm bound
`max_c |freq c - 1/b| → 0` says only that no digit value takes a positive
share of the window, which plenty of non-normal reals satisfy.  Summing the
deviations over all `b` cells cancels the vanishing target, so `digitTV` is
the notion with content here.  See `digitTV_diag_eq` for the sharp form of
the degeneracy at the diagonal depth `N = b`.

## Route

The engine is `Pillai.lean`, reused rather than rebuilt.  A base-`b ^ r`
digit is an aligned length-`r` block of base-`b` digits
(`digitOf_pow_eq_blockNatVal`), block occurrences at a fixed phase are
counted by `card_matchingValues`, and boundary-straddling occurrences are
already bounded by `card_straddling_phases`.  The only new ingredient is
`abs_expectation_sub_le_two_mul_digitTV`: total variation controls the
expectation of any `[0,1]`-valued statistic of a digit, which converts a
histogram bound into a block-frequency bound in one step, with no induction
on `r`.

Contrast with `phaseWindowFreq_tendsto`, which obtains the same conclusion
from a limit at fixed `r`.  Here `r` is large and the bound is uniform in
it, and that is the whole trade.

## Guardrails

Two statements in this file are refutations rather than tools, recorded so
that a proof search does not spend laps on them:

* `digitTV_diag_eq` shows the depth-`N = b` reading is a rigidity (the digit
  multiset must be a near-permutation), not a weakened randomness.  A random
  real fails it.
* `exists_schedule_digitTV_tendsto_not_isNormal` shows that asking for *some*
  depth schedule, rather than every one, is dodgeable: one depth per base is
  exactly what an oscillating real can satisfy.
-/

namespace NormalNumbers

open Filter

/-- Occurrences of the digit value `c` among the first `N` base-`b` digits
of `x`. -/
noncomputable def digitOccCount (b : ℕ) (x : ℝ) (N c : ℕ) : ℕ :=
  ((Finset.range N).filter fun i => digitOf b x i = c).card

/-- Total-variation distance from the base-`b` digit histogram of the first
`N` digits of `x` to the uniform distribution on `{0, …, b - 1}`. -/
noncomputable def digitTV (b : ℕ) (x : ℝ) (N : ℕ) : ℝ :=
  (∑ c ∈ Finset.range b, |(digitOccCount b x N c : ℝ) / N - (b : ℝ)⁻¹|) / 2

/-- **Guardrail.**  At the diagonal depth `N = b` the criterion is a
rigidity, not a randomness: `digitTV b x b` is small exactly when the first
`b` base-`b` digits are a permutation of `{0, …, b - 1}` up to `o b`
defects.  A uniformly random real has about `b / e` unused values at this
depth, pinning `digitTV b x b ≥ 1 / (2 * e)`, so this is *stronger* than
normality and orthogonal to it. -/
theorem digitTV_diag_eq (b : ℕ) (hb : 2 ≤ b) (x : ℝ) :
    digitTV b x b
      = (∑ c ∈ Finset.range b, |(digitOccCount b x b c : ℝ) - 1|) / (2 * b) := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have : (0 : ℕ) < b := lt_of_lt_of_le (by norm_num) hb
    exact_mod_cast this
  have hterm : ∀ c : ℕ, |(digitOccCount b x b c : ℝ) / b - (b : ℝ)⁻¹|
      = |(digitOccCount b x b c : ℝ) - 1| / b := by
    intro c
    rw [inv_eq_one_div, div_sub_div_same, abs_div, abs_of_pos hb0]
  simp only [digitTV, hterm, ← Finset.sum_div]
  ring

/-- Total variation controls every `[0,1]`-valued statistic of a digit.
This is the one genuinely new lemma; everything else is `Pillai.lean`. -/
theorem abs_expectation_sub_le_two_mul_digitTV (b : ℕ) (x : ℝ) (N : ℕ)
    (f : ℕ → ℝ) (hf0 : ∀ c, 0 ≤ f c) (hf1 : ∀ c, f c ≤ 1) :
    |(∑ c ∈ Finset.range b, (digitOccCount b x N c : ℝ) / N * f c)
        - ∑ c ∈ Finset.range b, (b : ℝ)⁻¹ * f c|
      ≤ 2 * digitTV b x N := by
  have h2 : 2 * digitTV b x N
      = ∑ c ∈ Finset.range b, |(digitOccCount b x N c : ℝ) / N - (b : ℝ)⁻¹| := by
    unfold digitTV; ring
  rw [h2, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro c _
  have hrw : (digitOccCount b x N c : ℝ) / N * f c - (b : ℝ)⁻¹ * f c
      = ((digitOccCount b x N c : ℝ) / N - (b : ℝ)⁻¹) * f c := by ring
  rw [hrw, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (abs_le.mpr ⟨by linarith [hf0 c], hf1 c⟩)

/-- The bridge home: at a fixed base, the total-variation form and the
digit-frequency form of simple normality agree.  Stated so that a search
landing on either shape can reach the other. -/
theorem simplyNormal_iff_digitTV_tendsto (b : ℕ) (x : ℝ) :
    (∀ c < b, Tendsto (fun N => (digitOccCount b x N c : ℝ) / N) atTop (nhds (b : ℝ)⁻¹))
      ↔ Tendsto (digitTV b x) atTop (nhds 0) := by
  constructor
  · intro h
    have hsum : Tendsto (fun N => ∑ c ∈ Finset.range b,
        |(digitOccCount b x N c : ℝ) / N - (b : ℝ)⁻¹|) atTop (nhds 0) := by
      have hz : (0 : ℝ) = ∑ _c ∈ Finset.range b, (0 : ℝ) := by simp
      rw [hz]
      refine tendsto_finset_sum _ (fun c hc => ?_)
      have h0 : Tendsto (fun N => (digitOccCount b x N c : ℝ) / N - (b : ℝ)⁻¹)
          atTop (nhds 0) := by
        simpa using (h c (Finset.mem_range.mp hc)).sub_const ((b : ℝ)⁻¹)
      simpa using h0.abs
    unfold digitTV
    simpa using hsum.div_const 2
  · intro h c hc
    have hterm : ∀ N : ℕ, |(digitOccCount b x N c : ℝ) / N - (b : ℝ)⁻¹|
        ≤ 2 * digitTV b x N := by
      intro N
      have h2 : 2 * digitTV b x N
          = ∑ c' ∈ Finset.range b, |(digitOccCount b x N c' : ℝ) / N - (b : ℝ)⁻¹| := by
        unfold digitTV; ring
      rw [h2]
      exact Finset.single_le_sum
        (f := fun c' => |(digitOccCount b x N c' : ℝ) / N - (b : ℝ)⁻¹|)
        (fun i _ => abs_nonneg _) (Finset.mem_range.mpr hc)
    have hsq : Tendsto (fun N => |(digitOccCount b x N c : ℝ) / N - (b : ℝ)⁻¹|)
        atTop (nhds 0) :=
      squeeze_zero (fun _ => abs_nonneg _) hterm (by simpa using h.const_mul 2)
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq] using hsq

/-- **Uniform high-base equidistribution.**  For every `ε` there is a
sampling ratio `L` and a base threshold `B` such that every base `b ≥ B`,
read to any depth `N ≥ L * b`, has its digit histogram within `ε` of
uniform.

The `L * b` floor is forced: at `N` samples in `b` cells the typical
total variation is of order `√(b / N)`, so depth must outgrow the base for
the condition to be satisfiable at all. -/
def UniformDigitTV (x : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ L B : ℕ, ∀ b ≥ B, ∀ N ≥ L * b, digitTV b x N < ε

/-- **Per-phase uniform bound.**  Total variation at base `b^r` controls the
frequency of block `w` at phase `s`, without needing a limit — the uniform
analogue of `phaseWindowFreq_tendsto`, driven by
`abs_expectation_sub_le_two_mul_digitTV` against the indicator of the
matching-value set. -/
theorem phaseWindowFreq_uniform_bound (b r m s : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r)
    (hL : s + m ≤ r) (y : ℝ) (hy : y ∈ Set.Ico (0 : ℝ) 1) (w : List ℕ)
    (hwlen : w.length = m) (hwlt : ∀ d ∈ w, d < b) (Q : ℕ) :
    |(((Finset.range Q).filter
        (fun q => List.ofFn (fun i : Fin m => digitOf b y (r * q + s + i)) = w)).card : ℝ) / Q
        - ((b : ℝ) ^ m)⁻¹|
      ≤ 2 * digitTV (b ^ r) y Q := by
  have hVlt : blockNatVal b w < b ^ m := by
    have := blockNatVal_lt b w hwlt; rwa [hwlen] at this
  set V : ℕ := blockNatVal b w with hVdef
  set mV : Finset ℕ := (Finset.range (b ^ r)).filter
    (fun c => c / b ^ (r - s - m) % b ^ m = V) with hmVdef
  have hmVcard : mV.card = b ^ (r - m) := card_matchingValues b r m s V hb hL hVlt
  have hbr2 : 2 ≤ b ^ r := le_trans hb (Nat.le_self_pow (by omega) b)
  set f : ℕ → ℝ := fun c => if c ∈ mV then 1 else 0 with hfdef
  have hf0 : ∀ c, 0 ≤ f c := fun c => by simp only [hfdef]; split_ifs <;> norm_num
  have hf1 : ∀ c, f c ≤ 1 := fun c => by simp only [hfdef]; split_ifs <;> norm_num
  have hkey := abs_expectation_sub_le_two_mul_digitTV (b ^ r) y Q f hf0 hf1
  have hfilter_eq : (Finset.range (b ^ r)).filter (fun c => c ∈ mV) = mV := by
    ext c
    simp only [hmVdef, Finset.mem_filter, Finset.mem_range]
    tauto
  have hcount_eq : ((Finset.range Q).filter
      (fun q => List.ofFn (fun i : Fin m => digitOf b y (r * q + s + i)) = w)).card
      = ∑ c ∈ mV, digitOccCount (b ^ r) y Q c := by
    rw [count_windowMatch_eq_count_matchingValues b r m s hb hr hL y hy w hwlen hwlt Q]
    rw [show ((Finset.range Q).filter
        (fun q => digitOf (b ^ r) y q / b ^ (r - s - m) % b ^ m = V)).card
        = ((Finset.range Q).filter (fun q => digitOf (b ^ r) y q ∈ mV)).card from by
      congr 1; apply Finset.filter_congr; intro q _
      simp only [hmVdef, Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => ⟨digitOf_lt (b ^ r) hbr2 y q, h⟩, fun h => h.2⟩]
    rw [Finset.card_eq_sum_card_fiberwise
      (s := (Finset.range Q).filter (fun q => digitOf (b ^ r) y q ∈ mV))
      (t := mV) (f := fun q => digitOf (b ^ r) y q)
      (fun q hq => (Finset.mem_filter.mp hq).2)]
    apply Finset.sum_congr rfl
    intro c hc
    unfold digitOccCount
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨ha, _⟩, hfa⟩; exact ⟨ha, hfa⟩
    · rintro ⟨ha, hfa⟩; exact ⟨⟨ha, hfa ▸ hc⟩, hfa⟩
  have hsum1' : (((Finset.range Q).filter
        (fun q => List.ofFn (fun i : Fin m => digitOf b y (r * q + s + i)) = w)).card : ℝ) / Q
      = ∑ c ∈ mV, (digitOccCount (b ^ r) y Q c : ℝ) / Q := by
    rw [hcount_eq]; push_cast; rw [Finset.sum_div]
  have step1 : ∀ c, (digitOccCount (b ^ r) y Q c : ℝ) / Q * f c
      = if c ∈ mV then (digitOccCount (b ^ r) y Q c : ℝ) / Q else 0 := by
    intro c; simp only [hfdef]; split_ifs <;> ring
  have hsum1 : ∑ c ∈ Finset.range (b ^ r), (digitOccCount (b ^ r) y Q c : ℝ) / Q * f c
      = (((Finset.range Q).filter
        (fun q => List.ofFn (fun i : Fin m => digitOf b y (r * q + s + i)) = w)).card : ℝ) / Q := by
    simp_rw [step1]
    rw [← Finset.sum_filter, hfilter_eq, ← hsum1']
  have step2 : ∀ c, ((b ^ r : ℕ) : ℝ)⁻¹ * f c = if c ∈ mV then ((b ^ r : ℕ) : ℝ)⁻¹ else 0 := by
    intro c; simp only [hfdef]; split_ifs <;> ring
  have hsum2 : ∑ c ∈ Finset.range (b ^ r), ((b ^ r : ℕ) : ℝ)⁻¹ * f c = ((b : ℝ) ^ m)⁻¹ := by
    simp_rw [step2]
    rw [← Finset.sum_filter, hfilter_eq, Finset.sum_const, hmVcard, nsmul_eq_mul]
    push_cast
    have hsplit : (b : ℝ) ^ r = (b : ℝ) ^ m * (b : ℝ) ^ (r - m) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    have hmpos : (0 : ℝ) < (b : ℝ) ^ m := by positivity
    have hrmpos : (0 : ℝ) < (b : ℝ) ^ (r - m) := by positivity
    field_simp
  rw [hsum1, hsum2] at hkey
  exact hkey

/-- The base-`b` digit map is invariant under discarding the integer part,
for nonnegative reals: adding an integer multiple of `b^(i+1)` before
flooring never changes the residue mod `b`. -/
theorem digitOf_eq_digitOf_fract (b : ℕ) (hb : 1 ≤ b) (x : ℝ) (hx : 0 ≤ x) (i : ℕ) :
    digitOf b x i = digitOf b (Int.fract x) i := by
  unfold digitOf
  have hbZpos : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hb
  set M : ℤ := ⌊x⌋ * (b : ℤ) ^ (i + 1) with hMdef
  have hxeq : x * (b : ℝ) ^ (i + 1) = Int.fract x * (b : ℝ) ^ (i + 1) + (M : ℝ) := by
    rw [hMdef]; push_cast; rw [Int.fract]; ring
  rw [hxeq, Int.floor_add_intCast]
  have hA : 0 ≤ ⌊Int.fract x * (b : ℝ) ^ (i + 1)⌋ := by
    apply Int.floor_nonneg.mpr
    positivity
  have hMge : 0 ≤ (⌊x⌋ : ℤ) := Int.floor_nonneg.mpr hx
  have hbpos : (0 : ℤ) < (b : ℤ) ^ (i + 1) := by positivity
  set A : ℤ := ⌊Int.fract x * (b : ℝ) ^ (i + 1)⌋ with hAdef
  have hMnn : 0 ≤ M := mul_nonneg hMge hbpos.le
  have htoNat : (A + M).toNat = A.toNat + M.toNat := Int.toNat_add hA hMnn
  rw [htoNat]
  have hMdvd : b ∣ M.toNat := by
    have hdvd : (b : ℤ) ∣ M := Dvd.dvd.mul_left (dvd_pow_self (b : ℤ) (Nat.succ_ne_zero i)) _
    obtain ⟨k, hk⟩ := hdvd
    have hknn : 0 ≤ k := by
      by_contra hcon
      push_neg at hcon
      have hneg : (b : ℤ) * k < 0 := mul_neg_of_pos_of_neg hbZpos hcon
      rw [← hk] at hneg
      linarith
    refine ⟨k.toNat, ?_⟩
    have hMk : M = (b : ℤ) * k := hk
    have hcast : M.toNat = ((b : ℤ) * k).toNat := by rw [hMk]
    rw [hcast, Int.toNat_mul (by positivity) hknn]
    simp
  obtain ⟨k, hk⟩ := hMdvd
  rw [hk, Nat.add_mul_mod_self_left]

/-- If `UniformDigitTV`-style equidistribution holds at some base beyond `2`
for `x`, then `x ≥ 0`: a negative `x` has every digit equal to `0`, pinning
`digitTV b' x N ≥ 1/2` for every `b' ≥ 2`, which contradicts the hypothesis
at `ε = 1/2`. -/
theorem nonneg_of_digitTV_small (x : ℝ)
    (h : ∃ b' N : ℕ, 2 ≤ b' ∧ digitTV b' x N < 1 / 2) : 0 ≤ x := by
  by_contra hx
  push_neg at hx
  obtain ⟨b', N, hb', hlt⟩ := h
  have hb'pos : (0 : ℕ) < b' := by omega
  have hdig0 : ∀ i, digitOf b' x i = 0 := by
    intro i
    unfold digitOf
    have hneg : x * (b' : ℝ) ^ (i + 1) < 0 :=
      mul_neg_of_neg_of_pos hx (by positivity)
    have hflneg : ⌊x * (b' : ℝ) ^ (i + 1)⌋ < 0 := Int.floor_lt.mpr (by simpa using hneg)
    simp [Int.toNat_of_nonpos hflneg.le]
  have hocc : ∀ c, digitOccCount b' x N c = if c = 0 then N else 0 := by
    intro c
    unfold digitOccCount
    split_ifs with hc
    · subst hc
      rw [show (Finset.range N).filter (fun i => digitOf b' x i = 0)
          = Finset.range N from by
        ext i; simp [hdig0 i]]
      exact Finset.card_range N
    · rw [show (Finset.range N).filter (fun i => digitOf b' x i = c)
          = ∅ from by
        ext i; simp [hdig0 i, Ne.symm hc]]
      simp
  have hb'R : (2 : ℝ) ≤ (b' : ℝ) := by exact_mod_cast hb'
  have hb'pos' : (0 : ℝ) < (b' : ℝ) := by linarith
  have hval : digitTV b' x N = 1 / 2 ∨ digitTV b' x N ≥ 1 / 2 := by
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · left
      subst hN0
      unfold digitTV
      have : ∀ c ∈ Finset.range b', |(digitOccCount b' x 0 c : ℝ) / (0:ℕ) - (b' : ℝ)⁻¹|
          = (b' : ℝ)⁻¹ := by
        intro c _
        rw [hocc c]
        split_ifs <;> simp [abs_of_pos (inv_pos.mpr hb'pos')]
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    · right
      unfold digitTV
      have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
      have hsplit : Finset.range b' = insert 0 ((Finset.range b').erase 0) := by
        rw [Finset.insert_erase (Finset.mem_range.mpr hb'pos)]
      have h0term : |(digitOccCount b' x N 0 : ℝ) / N - (b' : ℝ)⁻¹| = 1 - (b' : ℝ)⁻¹ := by
        rw [hocc 0]; simp
        rw [div_self hNR.ne']
        rw [abs_of_nonneg (by
          have : (b':ℝ)⁻¹ ≤ 1/2 := by rw [inv_le_iff_one_le_mul₀ hb'pos']; linarith
          linarith)]
      have hrest : ∀ c ∈ (Finset.range b').erase 0,
          |(digitOccCount b' x N c : ℝ) / N - (b' : ℝ)⁻¹| = (b' : ℝ)⁻¹ := by
        intro c hc
        have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
        rw [hocc c]
        simp [hc0, abs_of_pos (inv_pos.mpr hb'pos')]
      have hcardrest : ((Finset.range b').erase 0).card = b' - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hb'pos), Finset.card_range]
      rw [hsplit, Finset.sum_insert (Finset.notMem_erase 0 _), h0term,
        Finset.sum_congr rfl hrest, Finset.sum_const, hcardrest, nsmul_eq_mul]
      have hb'1 : ((b' - 1 : ℕ) : ℝ) = (b' : ℝ) - 1 := by
        rw [Nat.cast_sub hb'pos]; norm_num
      rw [hb'1]
      rw [ge_iff_le, le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      have : (b' : ℝ)⁻¹ * (b' : ℝ) = 1 := by field_simp
      nlinarith [inv_pos.mpr hb'pos' , this]
  rcases hval with h1 | h1 <;> linarith

/-- The engine.  Only the powers of `b` are consumed, so the hypothesis may
be weakened to that subfamily. -/
theorem isNormal_of_uniform_digitTV_pow (b : ℕ) (hb : 2 ≤ b) (x : ℝ)
    (h : ∀ ε > (0 : ℝ), ∃ L K : ℕ, ∀ r ≥ K, ∀ N ≥ L * b ^ r, digitTV (b ^ r) x N < ε) :
    IsNormal b x := by
  have hx0 : 0 ≤ x := by
    apply nonneg_of_digitTV_small
    obtain ⟨L, K, hLK⟩ := h (1 / 2) (by norm_num)
    refine ⟨b ^ (max K 1), L * b ^ (max K 1), ?_, hLK (max K 1) (le_max_left _ _) _ le_rfl⟩
    calc 2 ≤ b := hb
      _ ≤ b ^ (max K 1) := Nat.le_self_pow (by omega) b
  set y : ℝ := Int.fract x with hydef
  have hy : y ∈ Set.Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
  have hdeq : ∀ r i, digitOf (b ^ r) x i = digitOf (b ^ r) y i := by
    intro r i
    exact digitOf_eq_digitOf_fract (b ^ r) (Nat.one_le_pow r b (by omega)) x hx0 i
  have htveq : ∀ r N, digitTV (b ^ r) x N = digitTV (b ^ r) y N := by
    intro r N
    have hocceq : ∀ c, digitOccCount (b ^ r) x N c = digitOccCount (b ^ r) y N c := by
      intro c
      unfold digitOccCount
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro i _
      rw [hdeq r i]
    unfold digitTV
    simp_rw [hocceq]
  have h' : ∀ ε > (0 : ℝ), ∃ L K : ℕ, ∀ r ≥ K, ∀ N ≥ L * b ^ r, digitTV (b ^ r) y N < ε := by
    intro ε hε
    obtain ⟨L, K, hLK⟩ := h ε hε
    exact ⟨L, K, fun r hr N hN => (htveq r N) ▸ hLK r hr N hN⟩
  show IsNormalSequence b (digitOf b y)
  intro w hwne hwlt
  set m := w.length with hmdef
  have hm1 : 1 ≤ m := List.length_pos_of_ne_nil hwne
  set a : ℝ := ((b : ℝ) ^ m)⁻¹ with hadef
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    rw [hadef]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ b)))
  have hwf : Filter.Tendsto (fun N : ℕ => (((Finset.range (N + 1)).filter
        (fun i => i + m ≤ N ∧ List.ofFn (fun j : Fin m => digitOf b y (i + j)) = w)).card : ℝ) / N)
      Filter.atTop (nhds a) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- fix ε₂ (capped at `1/16` so its square stays a controlled multiple of itself)
    -- and pull `Lh, Kh` from the uniform hypothesis
    set ε₂ : ℝ := min (ε / 16) (1 / 16) with hε₂def
    have hε₂pos : 0 < ε₂ := lt_min (by linarith) (by norm_num)
    have hε₂le16 : ε₂ ≤ ε / 16 := min_le_left _ _
    have hε₂le : ε₂ ≤ 1 / 16 := min_le_right _ _
    obtain ⟨Lh, Kh, hLK⟩ := h' ε₂ hε₂pos
    -- fix `r` large enough for the straddling density and beyond `Kh`, `m`
    obtain ⟨r₀, hr₀⟩ := exists_nat_gt (4 * ((m : ℝ) - 1) / ε)
    set r := max (max r₀ m) Kh with hrdef
    have hrm : m ≤ r := le_trans (le_max_right r₀ m) (le_max_left _ _)
    have hr1 : 1 ≤ r := le_trans hm1 hrm
    have hrKh : Kh ≤ r := le_max_right _ _
    have hr0R : (0 : ℝ) < r := by exact_mod_cast hr1
    have hr₀r : (r₀ : ℝ) ≤ r := by exact_mod_cast le_trans (le_max_left r₀ m) (le_max_left _ _)
    have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hgap : ((m : ℝ) - 1) * (r : ℝ)⁻¹ < ε / 4 := by
      rw [← div_eq_mul_inv, div_lt_iff₀ hr0R]
      have h4 : 4 * ((m : ℝ) - 1) < r * ε := by
        have hlt : 4 * ((m : ℝ) - 1) / ε < r := lt_of_lt_of_le hr₀ hr₀r
        calc 4 * ((m : ℝ) - 1) = (4 * ((m : ℝ) - 1) / ε) * ε := by field_simp
          _ < r * ε := mul_lt_mul_of_pos_right hlt hε
      nlinarith [h4]
    -- ε₃: tolerance for how close `phaseOccCount / N` is to `1/r`, chosen after `r`
    -- and after `ε₂`, so that `r * ε₃ ≤ ε₂`
    set ε₃ : ℝ := ε₂ / ((r : ℝ) + 1) with hε₃def
    have hrε₃le : (r : ℝ) * ε₃ ≤ ε₂ := by
      rw [hε₃def, div_eq_mul_inv, ← mul_assoc]
      have hrr1 : (r : ℝ) * ((r : ℝ) + 1)⁻¹ ≤ 1 := by
        rw [mul_inv_le_iff₀ (by positivity)]; nlinarith [hr0R]
      nlinarith [hrr1, hε₂pos]
    have hε₃pos : 0 < ε₃ := by rw [hε₃def]; positivity
    -- eventual thresholds, per non-straddling phase `s`, for the two ingredients
    have hNa : ∀ s < r, s + m ≤ r → ∃ Na, ∀ N ≥ Na, Lh * b ^ r ≤ phaseOccCount r m s N := by
      intro s _ _
      have := phaseOccCount_tendsto_atTop r m s hr1
      rw [Filter.tendsto_atTop_atTop] at this
      obtain ⟨Na, hNa⟩ := this (Lh * b ^ r)
      exact ⟨Na, hNa⟩
    have hNb : ∀ s < r, ∃ Nb, ∀ N ≥ Nb, |(phaseOccCount r m s N : ℝ) / N - (r : ℝ)⁻¹| < ε₃ := by
      intro s _
      have := phaseOccCount_div_tendsto r m s hr1
      rw [Metric.tendsto_atTop] at this
      obtain ⟨Nb, hNb⟩ := this ε₃ hε₃pos
      refine ⟨Nb, fun N hN => ?_⟩
      have := hNb N hN
      rwa [Real.dist_eq] at this
    classical
    -- concrete choice functions for the two eventual thresholds, combined by `Finset.sup`
    set NaC : ℕ → ℕ := fun s =>
      if hs : s < r then (if hsm : s + m ≤ r then (hNa s hs hsm).choose else 0) else 0
      with hNaCdef
    set NbC : ℕ → ℕ := fun s => if hs : s < r then (hNb s hs).choose else 0 with hNbCdef
    set N0 : ℕ := (Finset.range r).sup (fun s => max (NaC s) (NbC s)) with hN0def
    refine ⟨max N0 1, fun N hN => ?_⟩
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hNN0 : N0 ≤ N := le_trans (le_max_left _ _) hN
    have hphaseQ : ∀ s, s < r → s + m ≤ r → Lh * b ^ r ≤ phaseOccCount r m s N := by
      intro s hs hsm
      have hsmem : s ∈ Finset.range r := Finset.mem_range.mpr hs
      have hle : max (NaC s) (NbC s) ≤ N0 := Finset.le_sup (f := fun s => max (NaC s) (NbC s)) hsmem
      have hNa' : NaC s ≤ N := le_trans (le_trans (le_max_left _ _) hle) hNN0
      have hspec := (hNa s hs hsm).choose_spec
      have heq : NaC s = (hNa s hs hsm).choose := by simp [hNaCdef, hs, hsm]
      rw [← heq] at hspec
      exact hspec N hNa'
    have hphaseB : ∀ s, s < r → |(phaseOccCount r m s N : ℝ) / N - (r : ℝ)⁻¹| < ε₃ := by
      intro s hs
      have hsmem : s ∈ Finset.range r := Finset.mem_range.mpr hs
      have hle : max (NaC s) (NbC s) ≤ N0 := Finset.le_sup (f := fun s => max (NaC s) (NbC s)) hsmem
      have hNb' : NbC s ≤ N := le_trans (le_trans (le_max_right _ _) hle) hNN0
      have hspec := (hNb s hs).choose_spec
      have heq : NbC s = (hNb s hs).choose := by simp [hNbCdef, hs]
      rw [← heq] at hspec
      exact hspec N hNb'
    -- per-phase bound: `T_s(N) := phaseWindowMatchCount_s(Q_s(N)) / N` is within `D`
    -- of `a / r`, where `D` collects the two error sources
    set D : ℝ := 2 * ε₂ * ((r : ℝ)⁻¹ + ε₃) + ε₃ with hDdef
    have hDnn : 0 ≤ D := by
      rw [hDdef]; have : (0:ℝ) ≤ (r:ℝ)⁻¹ := by positivity
      nlinarith [hε₂pos.le, hε₃pos.le]
    have hphaseT : ∀ s, s < r → s + m ≤ r →
        |(((Finset.range (phaseOccCount r m s N)).filter
            (fun q => List.ofFn (fun i : Fin m => digitOf b y (r * q + s + i)) = w)).card : ℝ) / N
          - a * (r : ℝ)⁻¹| ≤ D := by
      intro s hs hsm
      set Q := phaseOccCount r m s N with hQdef
      have hQge : Lh * b ^ r ≤ Q := hphaseQ s hs hsm
      have hBbound := hphaseB s hs
      have hdig : digitTV (b ^ r) y Q < ε₂ := hLK r hrKh Q hQge
      have hAbound := phaseWindowFreq_uniform_bound b r m s hb hr1 hsm y hy w hmdef.symm hwlt Q
      set A : ℝ := (((Finset.range Q).filter
          (fun q => List.ofFn (fun i : Fin m => digitOf b y (r * q + s + i)) = w)).card : ℝ) / Q
        with hAdef
      set B : ℝ := (Q : ℝ) / N with hBdef
      have hABeq : (((Finset.range Q).filter
          (fun q => List.ofFn (fun i : Fin m => digitOf b y (r * q + s + i)) = w)).card : ℝ) / N
          = A * B := by
        rw [hAdef, hBdef]
        rcases eq_or_ne (Q : ℝ) 0 with hQ0 | hQ0
        · have hQ0' : Q = 0 := by exact_mod_cast hQ0
          simp [hQ0, hQ0']
        · field_simp
      rw [hABeq]
      have hA2 : |A - a| ≤ 2 * ε₂ := by
        have := hAbound
        have hlt : 2 * digitTV (b ^ r) y Q < 2 * ε₂ := by linarith
        calc |A - a| ≤ 2 * digitTV (b ^ r) y Q := hAbound
          _ ≤ 2 * ε₂ := by linarith
      have hBnn : 0 ≤ B := by rw [hBdef]; positivity
      have hBrange : (r : ℝ)⁻¹ - ε₃ < B ∧ B < (r : ℝ)⁻¹ + ε₃ := by
        have := abs_lt.mp hBbound
        constructor <;> linarith [this.1, this.2]
      have key : A * B - a * (r : ℝ)⁻¹ = (A - a) * B + a * (B - (r : ℝ)⁻¹) := by ring
      rw [key]
      have hBabs : |B| ≤ (r : ℝ)⁻¹ + ε₃ := by
        rw [abs_of_nonneg hBnn]; linarith [hBrange.2]
      have haabs : |a| ≤ 1 := by rw [abs_of_nonneg ha0]; exact ha1
      have hBdiffabs : |B - (r : ℝ)⁻¹| ≤ ε₃ := hBbound.le
      calc |(A - a) * B + a * (B - (r : ℝ)⁻¹)|
          ≤ |(A - a) * B| + |a * (B - (r : ℝ)⁻¹)| := abs_add_le _ _
        _ = |A - a| * |B| + |a| * |B - (r : ℝ)⁻¹| := by rw [abs_mul, abs_mul]
        _ ≤ (2 * ε₂) * ((r : ℝ)⁻¹ + ε₃) + 1 * ε₃ :=
            add_le_add
              (mul_le_mul hA2 hBabs (abs_nonneg _) (by positivity))
              (mul_le_mul haabs hBdiffabs (abs_nonneg _) (by norm_num))
        _ = D := by rw [hDdef]; ring
    -- non-straddling / straddling phase sets and their cardinalities
    set NS : Finset ℕ := (Finset.range r).filter (fun s => s + m ≤ r) with hNSdef
    set ST : Finset ℕ := (Finset.range r).filter (fun s => r < s + m) with hSTdef
    have hNScard : NS.card = r - m + 1 := by
      rw [hNSdef, show (Finset.range r).filter (fun s => s + m ≤ r)
          = Finset.range (r - m + 1) from by
        ext s; simp only [Finset.mem_filter, Finset.mem_range]; omega, Finset.card_range]
    have hSTcard : ST.card = m - 1 := card_straddling_phases r m hm1 hrm
    have hNScardR : (NS.card : ℝ) = (r : ℝ) - (m : ℝ) + 1 := by
      rw [hNScard, Nat.cast_add, Nat.cast_sub hrm, Nat.cast_one]
    have hSTcardR : (ST.card : ℝ) = (m : ℝ) - 1 := by
      rw [hSTcard, Nat.cast_sub hm1, Nat.cast_one]
    -- the sandwich from `Pillai.lean`
    obtain ⟨hlow, hhigh⟩ := windowCount_div_sandwich b r m hr1 hm1 y w hmdef.symm N
    -- non-straddling sum is close to its target `NS.card • (a * r⁻¹)`
    have hLo_bound : |(∑ s ∈ NS, (((Finset.range (phaseOccCount r m s N)).filter
          (fun q => List.ofFn (fun i : Fin m => digitOf b y (r * q + s + i)) = w)).card : ℝ) / N)
        - (NS.card : ℝ) * (a * (r : ℝ)⁻¹)| ≤ (NS.card : ℝ) * D := by
      have heq : (NS.card : ℝ) * (a * (r : ℝ)⁻¹) = ∑ _s ∈ NS, a * (r : ℝ)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [heq, ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ s ∈ NS, |(((Finset.range (phaseOccCount r m s N)).filter
              (fun q => List.ofFn (fun i : Fin m => digitOf b y (r * q + s + i)) = w)).card : ℝ)
              / N - a * (r : ℝ)⁻¹|
          ≤ ∑ _s ∈ NS, D := Finset.sum_le_sum (fun s hs =>
              hphaseT s (Finset.mem_range.mp (Finset.mem_filter.mp hs).1)
                (Finset.mem_filter.mp hs).2)
        _ = (NS.card : ℝ) * D := by rw [Finset.sum_const, nsmul_eq_mul]
    -- straddling sum is close to its target `ST.card • r⁻¹`
    have hStrad_bound : |(∑ s ∈ ST, (phaseOccCount r m s N : ℝ) / N) - (ST.card : ℝ) * (r : ℝ)⁻¹|
        ≤ (ST.card : ℝ) * ε₃ := by
      have heq : (ST.card : ℝ) * (r : ℝ)⁻¹ = ∑ _s ∈ ST, (r : ℝ)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [heq, ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ s ∈ ST, |(phaseOccCount r m s N : ℝ) / N - (r : ℝ)⁻¹|
          ≤ ∑ _s ∈ ST, ε₃ := Finset.sum_le_sum (fun s hs =>
              (hphaseB s (Finset.mem_range.mp (Finset.mem_filter.mp hs).1)).le)
        _ = (ST.card : ℝ) * ε₃ := by rw [Finset.sum_const, nsmul_eq_mul]
    -- crude but sufficient cardinality bounds
    have hNScardle : (NS.card : ℝ) ≤ (r : ℝ) := by
      rw [hNScardR]; linarith [hm1R]
    have hSTcardle : (ST.card : ℝ) ≤ (r : ℝ) := by
      rw [hSTcardR]; linarith [hrm, (by exact_mod_cast hrm : (m:ℝ) ≤ (r:ℝ))]
    -- `r * D` is a controlled fraction of `ε`
    have hrD : (r : ℝ) * D ≤ 25 * ε / 128 := by
      have hrr : (r : ℝ) * (r : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hr0R.ne'
      have hexpand : (r : ℝ) * D
          = 2 * ε₂ * ((r : ℝ) * (r : ℝ)⁻¹) + 2 * ε₂ * ((r : ℝ) * ε₃) + (r : ℝ) * ε₃ := by
        rw [hDdef]; ring
      rw [hexpand, hrr]
      nlinarith [hrε₃le, hε₂le16, mul_le_mul_of_nonneg_left hε₂le hε₂pos.le]
    -- `(NS.card) * (a * r⁻¹)` sits within `(m-1)/r * a ≤ (m-1)/r` of `a`
    have hexpandNS : (NS.card : ℝ) * (a * (r : ℝ)⁻¹)
        = a - ((m : ℝ) - 1) * (r : ℝ)⁻¹ * a := by
      rw [hNScardR]; field_simp; ring
    have hmid_nn : 0 ≤ ((m : ℝ) - 1) * (r : ℝ)⁻¹ :=
      mul_nonneg (by linarith [hm1R]) (by positivity)
    have hNStarget_lo : a - ε / 4 ≤ (NS.card : ℝ) * (a * (r : ℝ)⁻¹) := by
      rw [hexpandNS]
      have hstep : ((m : ℝ) - 1) * (r : ℝ)⁻¹ * a ≤ ((m : ℝ) - 1) * (r : ℝ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left ha1 hmid_nn
      linarith [hstep, hgap]
    have hNStarget_hi : (NS.card : ℝ) * (a * (r : ℝ)⁻¹) ≤ a := by
      rw [hexpandNS]
      have : 0 ≤ ((m : ℝ) - 1) * (r : ℝ)⁻¹ * a := mul_nonneg hmid_nn ha0
      linarith [this]
    have hST_target : (ST.card : ℝ) * (r : ℝ)⁻¹ < ε / 4 := by rw [hSTcardR]; exact hgap
    have hNSD : (NS.card : ℝ) * D ≤ (r : ℝ) * D := mul_le_mul_of_nonneg_right hNScardle hDnn
    have hSTD : (ST.card : ℝ) * ε₃ ≤ (r : ℝ) * ε₃ := mul_le_mul_of_nonneg_right hSTcardle hε₃pos.le
    -- assemble the final bound
    rw [Real.dist_eq, abs_lt]
    obtain ⟨hLo1, hLo2⟩ := abs_le.mp hLo_bound
    obtain ⟨hSt1, hSt2⟩ := abs_le.mp hStrad_bound
    constructor
    · linarith [hlow, hLo1, hNStarget_lo, hNSD, hrD]
    · linarith [hhigh, hLo2, hSt2, hNStarget_hi, hSTD, hST_target, hrε₃le, hε₂le16, hrD]
  have hpred : ∀ i, (List.ofFn (fun j : Fin w.length => digitOf b y (i + (j : ℕ))) = w)
      ↔ MatchesAt (digitOf b y) w i := by
    intro i
    constructor
    · intro heq j hj
      have hf : (fun j : Fin w.length => digitOf b y (i + (j : ℕ))) = w.get :=
        List.ofFn_injective (heq.trans (List.ofFn_get w).symm)
      have hval := congrFun hf ⟨j, hj⟩
      rw [List.getD_eq_getElem w 0 hj, List.get_eq_getElem] at *
      exact hval
    · intro heq
      have hf : (fun j : Fin w.length => digitOf b y (i + (j : ℕ))) = w.get := by
        funext j
        have hj := heq j.1 j.2
        rw [List.getD_eq_getElem w 0 j.2] at hj
        rw [List.get_eq_getElem]
        exact hj
      rw [hf, List.ofFn_get]
  refine Filter.Tendsto.congr (fun n => ?_) hwf
  rw [countOccurrences_range_map]
  have hfilt : (Finset.range (n + 1)).filter (fun i => i + m ≤ n ∧
        List.ofFn (fun j : Fin m => digitOf b y (i + j)) = w)
      = (Finset.range (n + 1)).filter (fun i => i + m ≤ n ∧ MatchesAt (digitOf b y) w i) := by
    apply Finset.filter_congr
    intro i _
    rw [hmdef, hpred i]
  rw [congrArg Finset.card hfilt]

/-- **Headline.**  Uniform high-base equidistribution implies absolute
normality.  Strictly stronger than the conclusion: a normal real may have
arbitrarily bad rates as the base grows, so this is a sufficient criterion,
not a characterisation. -/
theorem isAbsolutelyNormal_of_uniformDigitTV (x : ℝ) (h : UniformDigitTV x) :
    IsAbsolutelyNormal x := by
  intro b hb
  apply isNormal_of_uniform_digitTV_pow b hb x
  intro ε hε
  obtain ⟨L, B, hLB⟩ := h ε hε
  refine ⟨L, B, fun r hr N hN => ?_⟩
  have hlt : B < b ^ B := Nat.lt_pow_self (by omega)
  have hmono : b ^ B ≤ b ^ r := Nat.pow_le_pow_right (by omega) hr
  exact hLB (b ^ r) (by omega) N hN

/-- The periodic base-`b` block `0, 1, …, b-1, 0, 1, …` of length `b * t`:
each residue `< b` occurs exactly `t` times, so a real whose digits spell it
out is exactly balanced on that stretch. -/
private def periodicPattern (b t : ℕ) : List ℕ := (List.range (b * t)).map (· % b)

private theorem periodicPattern_length (b t : ℕ) :
    (periodicPattern b t).length = b * t := by
  simp [periodicPattern]

private theorem periodicPattern_lt (b t : ℕ) (hb : 0 < b) :
    ∀ d ∈ periodicPattern b t, d < b := by
  intro d hd
  simp only [periodicPattern, List.mem_map, List.mem_range] at hd
  obtain ⟨j, _, rfl⟩ := hd
  exact Nat.mod_lt j hb

private theorem periodicPattern_getElem (b t j : ℕ) (hj : j < b * t) :
    (periodicPattern b t)[j]'(by rwa [periodicPattern_length]) = j % b := by
  simp [periodicPattern, List.getElem_map]

/-- Among the first `b * t` naturals, each residue class `< b` occurs
exactly `t` times. -/
private theorem card_residue_range (b t c : ℕ) (hb : 0 < b) (hc : c < b) :
    ((Finset.range (b * t)).filter (fun j => j % b = c)).card = t := by
  have heq : (Finset.range (b * t)).filter (fun j => j % b = c)
      = (Finset.range t).image (fun q => c + b * q) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hj, hmod⟩
      refine ⟨j / b, ?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hb, mul_comm]; exact hj
      · have hdm := Nat.div_add_mod j b
        rw [hmod] at hdm
        omega
    · rintro ⟨q, hq, rfl⟩
      refine ⟨?_, ?_⟩
      · calc c + b * q < b + b * q := by omega
          _ ≤ b * t := by nlinarith [hq]
      · rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hc
  rw [heq, Finset.card_image_of_injective _ (fun q q' hqq' => by
    have hcancel : b * q = b * q' := by omega
    exact Nat.eq_of_mul_eq_mul_left hb hcancel)]
  exact Finset.card_range t

/-- If the digits of `x` at positions `[p, p + b * t)` spell out the
periodic pattern, then at depth `N = p + b * t` the digit histogram is
exactly the (arbitrary) first-`p`-digit histogram plus `t` at every
residue — total variation at most `p / N` away from uniform. -/
private theorem digitTV_le_of_tail_periodic (b p t : ℕ) (hb : 2 ≤ b) (hp : 0 < p) (x : ℝ)
    (htail : ∀ j < b * t, digitOf b x (p + j) = j % b) :
    digitTV b x (p + b * t) ≤ (p : ℝ) / (p + b * t) + (b : ℝ) *
      |(t : ℝ) / (p + b * t) - (b : ℝ)⁻¹| := by
  set N := p + b * t with hNdef
  have hNpos : 0 < N := by rw [hNdef]; omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hocc : ∀ c < b, digitOccCount b x N c
      = ((Finset.range p).filter (fun i => digitOf b x i = c)).card + t := by
    intro c hc
    unfold digitOccCount
    rw [hNdef, Finset.range_add_eq_union]
    rw [Finset.filter_union, Finset.card_union_of_disjoint]
    · congr 1
      rw [Finset.filter_map, Finset.card_map]
      simp only [Function.comp, addLeftEmbedding_apply]
      have hcongr : (Finset.range (b * t)).filter
          (fun j => digitOf b x (p + j) = c)
          = (Finset.range (b * t)).filter (fun j => j % b = c) := by
        apply Finset.filter_congr
        intro j hj
        rw [htail j (Finset.mem_range.mp hj)]
      rw [hcongr]
      exact card_residue_range b t c (by omega) hc
    · apply Finset.disjoint_filter_filter
      rw [Finset.disjoint_left]
      intro a ha hamap
      simp only [Finset.mem_map, addLeftEmbedding_apply] at hamap
      obtain ⟨j, _, rfl⟩ := hamap
      simp only [Finset.mem_range] at ha
      omega
  have hpsum : ∑ c ∈ Finset.range b,
      ((Finset.range p).filter (fun i => digitOf b x i = c)).card = p := by
    rw [← Finset.card_eq_sum_card_fiberwise
      (s := Finset.range p) (t := Finset.range b) (f := fun i => digitOf b x i)
      (fun i _ => Finset.mem_range.mpr (digitOf_lt b hb x i))]
    exact Finset.card_range p
  have hterm : ∀ c < b, |(digitOccCount b x N c : ℝ) / N - (b : ℝ)⁻¹|
      ≤ (((Finset.range p).filter (fun i => digitOf b x i = c)).card : ℝ) / N
        + |(t : ℝ) / N - (b : ℝ)⁻¹| := by
    intro c hc
    rw [hocc c hc]
    push_cast
    have heq : (((Finset.range p).filter (fun i => digitOf b x i = c)).card + t : ℝ) / N
          - (b : ℝ)⁻¹
        = (((Finset.range p).filter (fun i => digitOf b x i = c)).card : ℝ) / N
          + ((t : ℝ) / N - (b : ℝ)⁻¹) := by ring
    rw [heq]
    have hAnn : (0:ℝ) ≤ (((Finset.range p).filter (fun i => digitOf b x i = c)).card : ℝ) / N :=
      by positivity
    calc |(((Finset.range p).filter (fun i => digitOf b x i = c)).card : ℝ) / N
          + ((t : ℝ) / N - (b : ℝ)⁻¹)|
        ≤ |(((Finset.range p).filter (fun i => digitOf b x i = c)).card : ℝ) / N|
          + |(t : ℝ) / N - (b : ℝ)⁻¹| := abs_add_le _ _
      _ = (((Finset.range p).filter (fun i => digitOf b x i = c)).card : ℝ) / N
          + |(t : ℝ) / N - (b : ℝ)⁻¹| := by rw [abs_of_nonneg hAnn]
  have hsum : ∑ c ∈ Finset.range b, |(digitOccCount b x N c : ℝ) / N - (b : ℝ)⁻¹|
      ≤ (p : ℝ) / N + (b : ℝ) * |(t : ℝ) / N - (b : ℝ)⁻¹| := by
    calc ∑ c ∈ Finset.range b, |(digitOccCount b x N c : ℝ) / N - (b : ℝ)⁻¹|
        ≤ ∑ c ∈ Finset.range b,
            ((((Finset.range p).filter (fun i => digitOf b x i = c)).card : ℝ) / N
              + |(t : ℝ) / N - (b : ℝ)⁻¹|) :=
          Finset.sum_le_sum (fun c hc => hterm c (Finset.mem_range.mp hc))
      _ = (p : ℝ) / N + (b : ℝ) * |(t : ℝ) / N - (b : ℝ)⁻¹| := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← Finset.sum_div, ← Nat.cast_sum, hpsum]
  unfold digitTV
  rw [hNdef] at hsum ⊢
  push_cast at hsum ⊢
  have h2 : (0:ℝ) < 2 := by norm_num
  rw [div_le_iff₀ h2]
  have hnn : (0:ℝ) ≤ (p:ℝ)/((p:ℝ)+(b:ℝ)*(t:ℝ)) + (b:ℝ)*|(t:ℝ)/((p:ℝ)+(b:ℝ)*(t:ℝ)) - (b:ℝ)⁻¹| := by
    positivity
  linarith [hsum, hnn]

end NormalNumbers
