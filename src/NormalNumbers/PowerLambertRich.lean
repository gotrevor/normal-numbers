/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerLambertNonNormal
import NormalNumbers.PowerLambertRichOrbit
import NormalNumbers.CastingOut

/-!
# Perfect-power Lambert constants are rich (every word has positive lower frequency)

`S_{b,r} = Σ_{n≥1} 1/(b^{n^r} − 1)`, `r ≥ 2`, is disjunctive (`isDisjunctive_powerLambert`) and not
normal (`not_isNormal_powerLambert`) in base `b`.  This file freezes the rung in between:
**richness** (`NormalNumbers.CastingOut.IsRich`): every base-`b` word occurs at a set of positions
of positive lower density.

## Mechanism (paper, 2026-11-03, Ren)

Write `S_{b,r} = q + Y` with `q` rational and `Y = coefficientValue c b`,
`c m = #{d > 8 : d^r ∣ m}` (`exists_rat_powerLambert_tail`).  The orbit is
`{b^n S} = {b^n q + Σ_{j≥1} c(n+j) b^{−j}}`, and `b^n q mod 1` is periodic in `n` with period
`T = lcm(1..8)^r` (each `1/(b^m − 1)` has period `m`).

1. **Witness with guard digits.**  For a word `w` of length `L`, disjunctivity gives a position
   `n₁` at which the longer word `w ++ [1] ++ replicate m 0` occurs, so `{b^{n₁} S}` lies in the
   `w`-cylinder with two-sided margin `δ := b^{−(L+1)} − b^{−(L+1+m)} > 0`.
2. **Freeze the small structure.**  Choose `J₀` with `Σ_{j>J₀} c(n₁+j) b^{−j} (1 + C_r) < δ/8`
   (the sum converges since `c m ≤ m`), then `D ≥ 8` larger than every `d` with `d^r ∣ n₁ + j`,
   `j ≤ J₀`.  Put `Q := (lcm(1..D))^{2r}` (a multiple of `T`).
3. **The shifted class.**  For `n = n₁ + kQ`, `k ≥ 0`: `{b^n q} = {b^{n₁} q}`, and the coefficients
   split as `c = c_Q + c_⊥`, where `c_Q m := #{d > 8 : d^r ∣ Q ∧ d^r ∣ m}` is `Q`-periodic, so
   `c_Q(n+j) = c_Q(n₁+j)` for all `j`.  Hence
   `|{b^n S} − {b^{n₁} S}| ≤ Σ_j c_⊥(n+j) b^{−j} + Σ_j c_⊥(n₁+j) b^{−j}` (mod-1 distance), and the
   second sum is `< δ/8` by the choice of `D` (for `j ≤ J₀`, `c_⊥(n₁+j) = 0`).
4. **Averaging over `k`.**  For `j ≤ J₀`: `d^r ∣ n₁ + kQ + j` with `d^r ∤ Q` forces a prime power
   `p^a ∥ d` with `p^a > D`; if `p ≤ D` the congruence is incompatible with the valuation of
   `n₁ + j` (which is `< 2⌊log_p D⌋ r`), and if `p > D` it has density `≤ 1/p^r` in `k`.  So
   `avg_{k<K} c_⊥(n₁+kQ+j) ≤ a_r(n₁+j) · Σ_{p>D} p^{−r} + o(1)`.  For `j > J₀` use the crude
   `avg_{k<K} c(n₁+kQ+j) ≤ (1 + C_r) a_r(n₁+j) + o(1)` with `C_r = Σ_p p^{−r}/(1 − p^{−r})`.
   The `o(1)` terms are the `+1` errors of counting `k < K` with `d^r ∣ n₁+kQ+j`, summed over
   `d ≤ (KQ + J)^{1/r}`: `O((KQ)^{1/r}) = o(K)` because `r ≥ 2`.  (For `r = 1` this fails, which
   is where `E_b` differs.)
5. **Markov.**  Hence for `K` large, at least `K/2` of the `k < K` have
   `Σ_j c_⊥(n₁+kQ+j) b^{−j} < δ/2`, and each such `n = n₁ + kQ` is an occurrence of `w`.  So the
   occurrence count below `N` is `≥ (N − n₁)/(2Q) − O(1)`: lower density `≥ 1/(4Q) > 0`.

The constant `1/(4Q)` depends on `w` through `n₁`, `J₀`, `D` — exactly what `IsRich` allows.

## Status

Proved (2026-11-04), axioms `propext`, `Classical.choice`, `Quot.sound`.  The formal proof
simplifies steps 2–4 above:

* the whole constant is used, `S = coefficientValue (powerDivisorCount r) b`, with no rational
  head; `orbit_powerLambert_eq` splits the orbit tail into `periodicTail` (roots `d` with
  `d^r ∣ Q`, exactly `Q`-periodic: `periodicTail_add_mul`) and `aperiodicTail ≥ 0`;
* `Q := (D!)^r` (every `d ≤ D` has `d^r ∣ Q`), with `D > 8 C / δ`, `C = Σ_j (n₁+1+j)/b^{j+1}`;
* no `p`-adic incompatibility step is needed: `card_filter_dvd_add_mul_le` gives
  `#{k < K : d^r ∣ m₀ + kQ} ≤ K m₀ / d^r + 1`, because `gcd(d^r, Q) ∣ m₀` caps the gcd by `m₀`;
  summing over `D < d ≤ √(m₀ + KQ)` (`sum_aperiodicPowerCount_le`) and over `j`
  (`sum_aperiodicTail_le`) gives `Σ_{k<K} R(n₁+kQ) ≤ C (2K/(D+1) + √(KQ+1))`; the `√` term is
  `o(K)`, which is where `r ≥ 2` enters (`d^r ≥ d^2`);
* the witness margin comes from disjunctivity on the middle third of the `w`-cylinder
  (no guard digits); `exists_progression_occursAt_powerLambert` is the Markov step and
  `eventually_le_card_filter_of_progression` converts it into lower density `≥ 1/(4Q)`.
-/

namespace NormalNumbers.ArithmeticDisjunctivity

open NormalNumbers.CastingOut Finset Filter

/-- A fractional part with margin `δ` inside `[A, B) ⊆ [0, 1)` stays in `[A, B)` when the
small summand changes by less than `δ`. -/
theorem fract_add_mem_Ico_of_close {P R R₁ A B δ : ℝ} (hA : 0 ≤ A) (hB : B ≤ 1)
    (hu : Int.fract (P + R₁) ∈ Set.Ico (A + δ) (B - δ))
    (hR : 0 ≤ R) (hRδ : R < δ) (hR₁ : 0 ≤ R₁) (hR₁δ : R₁ < δ) :
    Int.fract (P + R) ∈ Set.Ico A B := by
  set u := Int.fract (P + R₁)
  have hsplit : P + R = (⌊P + R₁⌋ : ℝ) + (u + (R - R₁)) := by
    have := Int.floor_add_fract (P + R₁)
    linarith
  have hv : Int.fract (P + R) = u + (R - R₁) := by
    rw [hsplit, Int.fract_intCast_add, Int.fract_eq_self]
    constructor <;> linarith [hu.1, hu.2]
  rw [hv]
  constructor <;> linarith [hu.1, hu.2]

/-- **Markov.**  If a nonnegative function has total at most `δ |s| / 2` on `s`, at least half
of `s` has value `< δ`. -/
theorem card_le_two_mul_card_filter_lt {s : Finset ℕ} {f : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : ∀ k ∈ s, 0 ≤ f k) (hsum : (∑ k ∈ s, f k) ≤ δ * s.card / 2) :
    (s.card : ℝ) ≤ 2 * (s.filter fun k => f k < δ).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := s) (fun k => f k < δ)
  have hbad : δ * ((s.filter fun k => ¬ f k < δ).card : ℝ) ≤ ∑ k ∈ s, f k := by
    calc δ * ((s.filter fun k => ¬ f k < δ).card : ℝ)
        = ∑ k ∈ s.filter (fun k => ¬ f k < δ), δ := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ k ∈ s.filter (fun k => ¬ f k < δ), f k :=
          Finset.sum_le_sum fun k hk => not_lt.mp (Finset.mem_filter.mp hk).2
      _ ≤ ∑ k ∈ s, f k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun k hk _ => hf k hk
  have hcast : ((s.filter fun k => f k < δ).card : ℝ) +
      ((s.filter fun k => ¬ f k < δ).card : ℝ) = s.card := by exact_mod_cast hsplit
  have : ((s.filter fun k => ¬ f k < δ).card : ℝ) ≤ s.card / 2 := by
    have h := hbad.trans hsum
    rw [mul_div_assoc] at h
    exact le_of_mul_le_mul_left h hδ
  linarith

/-- **Progression to lower density.**  If, for all large `K`, at least half of the shifts
`n₁ + kQ`, `k < K`, satisfy `P`, then `P` holds on a set of lower density `≥ 1/(4Q)`. -/
theorem eventually_le_card_filter_of_progression (P : ℕ → Prop) [DecidablePred P]
    {n₁ Q K₀ : ℕ} (hQ : 0 < Q)
    (hmarkov : ∀ K, K₀ ≤ K → 0 < K →
      (K : ℝ) ≤ 2 * (((range K).filter fun k => P (n₁ + k * Q)).card : ℝ)) :
    ∀ᶠ N in atTop, 1 / (4 * (Q : ℝ)) * N ≤ (((range N).filter P).card : ℝ) := by
  filter_upwards [eventually_ge_atTop (Q * (K₀ + 2 * n₁ + 4))] with N hN
  set M := N / Q with hMdef
  have hM : K₀ + 2 * n₁ + 4 ≤ M := (Nat.le_div_iff_mul_le hQ).mpr (by rw [mul_comm]; exact hN)
  set K := M - n₁ - 1 with hKdef
  have hmk := hmarkov K (by omega) (by omega)
  set G := (range K).filter fun k => P (n₁ + k * Q)
  have hinj : Set.InjOn (fun k => n₁ + k * Q) (G : Set ℕ) := by
    intro k _ k' _ h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_right hQ (by omega)
  have hsub : G.image (fun k => n₁ + k * Q) ⊆
      (range N).filter P := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hkK, hkgood⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨?_, hkgood⟩
    rw [Finset.mem_range]
    have hkK' : k + n₁ + 1 ≤ M := by have := Finset.mem_range.mp hkK; omega
    have h1 : (k + n₁ + 1) * Q ≤ M * Q := Nat.mul_le_mul_right Q hkK'
    have h2 : M * Q ≤ N := Nat.div_mul_le_self N Q
    have h3 : n₁ ≤ n₁ * Q := Nat.le_mul_of_pos_right n₁ hQ
    nlinarith
  have hcard : (G.card : ℝ) ≤
      (((range N).filter P).card : ℝ) := by
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj] at this
    exact_mod_cast this
  have hNlt : (N : ℝ) < Q * ((M : ℝ) + 1) := by
    have h := Nat.lt_div_mul_add (a := N) hQ
    have : N < Q * (M + 1) := by rw [hMdef]; nlinarith
    exact_mod_cast this
  have hKR : (K : ℝ) = (M : ℝ) - n₁ - 1 := by
    rw [hKdef, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hMR : (2 * n₁ + 4 : ℝ) ≤ M := by exact_mod_cast (by omega : 2 * n₁ + 4 ≤ M)
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  calc 1 / (4 * (Q : ℝ)) * N ≤ G.card := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        rw [hKR] at hmk
        nlinarith
    _ ≤ _ := hcard


open Classical in
/-- **Markov along a progression.**  For each word `w`, a positive proportion (at least half,
eventually) of the shifts `n₁ + kQ` are occurrences of `w`. -/
theorem exists_progression_occursAt_powerLambert (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r)
    (w : List ℕ) (hw : ∀ d ∈ w, d < b) :
    ∃ n₁ Q K₀ : ℕ, 0 < Q ∧ ∀ K, K₀ ≤ K → 0 < K → (K : ℝ) ≤
      2 * (((range K).filter fun k => OccursAt b (powerLambert b r) w (n₁ + k * Q)).card : ℝ) := by
  classical
  set L := w.length
  set W := blockNatVal b w
  have hWlt : W < b ^ L := blockNatVal_lt b w hw
  have hpow : (0 : ℝ) < (b : ℝ) ^ L := by positivity
  set A : ℝ := (W : ℝ) / (b : ℝ) ^ L with hAdef
  set B : ℝ := ((W : ℝ) + 1) / (b : ℝ) ^ L with hBdef
  set δ : ℝ := 1 / (3 * (b : ℝ) ^ L) with hδdef
  have hδ : 0 < δ := by positivity
  have hA : 0 ≤ A := by positivity
  have hB : B ≤ 1 := by
    rw [hBdef, div_le_one hpow]
    exact_mod_cast Nat.succ_le_of_lt hWlt
  have hBA : B - A = 3 * δ := by
    rw [hAdef, hBdef, hδdef]
    field_simp
    ring
  -- Step 1: a witness deep inside the cylinder of `w`.
  obtain ⟨n₁, hn₁⟩ := isDisjunctive_powerLambert b r hb (by omega) (A + δ) (B - δ)
    (by linarith) (by linarith) (by linarith)
  -- Step 2: freeze the roots up to `D` in the modulus `Q = (D!)^r`.
  obtain ⟨C, hCdef⟩ : ∃ C, C = affineTailWeight b n₁ := ⟨_, rfl⟩
  have hC : 0 ≤ C := hCdef ▸ affineTailWeight_nonneg b n₁
  obtain ⟨D, hD⟩ := exists_nat_gt (8 * C / δ)
  set Q := (D.factorial) ^ r with hQdef
  have hQ : 0 < Q := Nat.pow_pos (Nat.factorial_pos D)
  have hQD : ∀ d, 1 ≤ d → d ≤ D → d ^ r ∣ Q := fun d hd1 hdD =>
    pow_dvd_pow_of_dvd (Nat.dvd_factorial hd1 hdD) r
  have hDsmall : 2 / ((D : ℝ) + 1) * C ≤ δ / 4 := by
    have hD1 : (0 : ℝ) < (D : ℝ) + 1 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hD1]
    have := (div_lt_iff₀ hδ).mp hD
    nlinarith
  have hR₁ : aperiodicTail b r Q n₁ < δ := by
    have := aperiodicTail_le hb hr hQD n₁
    rw [← hCdef] at this
    linarith
  have hdecomp := orbit_powerLambert_eq b r Q hb (by omega) hQ
  -- Step 3: every shift `n₁ + kQ` with a small non-periodic tail is an occurrence.
  have hgood : ∀ k, aperiodicTail b r Q (n₁ + k * Q) < δ →
      OccursAt b (powerLambert b r) w (n₁ + k * Q) := by
    intro k hk
    rw [occursAt_iff_orbit_mem b hb (powerLambert b r) w hw, hdecomp, periodicTail_add_mul]
    rw [hdecomp] at hn₁
    exact fract_add_mem_Ico_of_close hA hB hn₁ (aperiodicTail_nonneg _ _ _ _) hk
      (aperiodicTail_nonneg _ _ _ _) hR₁
  -- Step 4: Markov along the progression.
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (16 * C ^ 2 * ((Q : ℝ) + 1) / δ ^ 2)
  have hmarkov : ∀ K, K₀ ≤ K → 0 < K → (K : ℝ) ≤
      2 * ((range K).filter fun k => aperiodicTail b r Q (n₁ + k * Q) < δ).card := by
    intro K hK hKpos
    have h := card_le_two_mul_card_filter_lt (s := range K)
      (f := fun k => aperiodicTail b r Q (n₁ + k * Q)) hδ
      (fun k _ => aperiodicTail_nonneg _ _ _ _) ?_
    · simpa using h
    rw [Finset.card_range]
    have hsum := sum_aperiodicTail_le hb hr hQD n₁ K
    rw [← hCdef] at hsum
    have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
    have hK0R : (K₀ : ℝ) ≤ K := by exact_mod_cast hK
    set y := Real.sqrt (((K * Q : ℕ) : ℝ) + 1) with hydef
    have hy0 : 0 ≤ y := Real.sqrt_nonneg _
    have hy2 : y ^ 2 = ((K * Q : ℕ) : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hCy : C * y ≤ K * δ / 4 := by
      by_contra hcon
      push Not at hcon
      have hT : 0 ≤ (K : ℝ) * δ / 4 := by positivity
      have h1 : ((K : ℝ) * δ / 4) ^ 2 < (C * y) ^ 2 := by nlinarith
      have h2 : (C * y) ^ 2 = C ^ 2 * ((K : ℝ) * Q + 1) := by
        rw [mul_pow, hy2]
        push_cast
        ring
      have h3 : 16 * C ^ 2 * ((Q : ℝ) + 1) < K₀ * δ ^ 2 :=
        (div_lt_iff₀ (by positivity : (0 : ℝ) < δ ^ 2)).mp hK₀
      have h4 : C ^ 2 * ((K : ℝ) * Q + 1) ≤ C ^ 2 * (K * ((Q : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      have h5 : (K₀ : ℝ) * δ ^ 2 ≤ K * δ ^ 2 := by
        apply mul_le_mul_of_nonneg_right hK0R (by positivity)
      nlinarith
    calc (∑ k ∈ range K, aperiodicTail b r Q (n₁ + k * Q))
        ≤ C * ((K : ℝ) * (2 / ((D : ℝ) + 1)) + y) := hsum
      _ = K * (2 / ((D : ℝ) + 1) * C) + C * y := by ring
      _ ≤ K * (δ / 4) + K * δ / 4 :=
          add_le_add (mul_le_mul_of_nonneg_left hDsmall (by positivity)) hCy
      _ = δ * K / 2 := by ring
  refine ⟨n₁, Q, K₀, hQ, fun K hK hKpos => (hmarkov K hK hKpos).trans ?_⟩
  have hsub : ((range K).filter fun k => aperiodicTail b r Q (n₁ + k * Q) < δ) ⊆
      (range K).filter fun k => OccursAt b (powerLambert b r) w (n₁ + k * Q) :=
    Finset.monotone_filter_right _ fun k _ hk => hgood k hk
  have := Finset.card_le_card hsub
  have hcast : ((((range K).filter fun k => aperiodicTail b r Q (n₁ + k * Q) < δ).card : ℕ) : ℝ)
      ≤ (((range K).filter fun k => OccursAt b (powerLambert b r) w (n₁ + k * Q)).card : ℝ) := by
    exact_mod_cast this
  linarith

/-- **Headline (frozen, 2026-11-03).**  Every finite base-`b` word occurs in the expansion of
`Σ_{n≥1} 1/(b^{n^r} − 1)`, `r ≥ 2`, at a set of positions of positive lower density.
Confidence 92%; mechanism in the module docstring (shifted residue class `n₁ + kQ` with
`Q = lcm(1..D)^{2r}` reproduces the witness's small-divisor structure; the non-periodic divisor
mass averages to `o(1)` because `r ≥ 2`). -/
@[blueprint (title := "Perfect-power Lambert constants are rich")]
theorem isRich_powerLambert (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
    IsRich b (powerLambert b r) := by
  classical
  intro w hw
  obtain ⟨n₁, Q, K₀, hQ, hmarkov⟩ := exists_progression_occursAt_powerLambert b r hb hr w hw
  exact ⟨1 / (4 * (Q : ℝ)), by positivity, eventually_le_card_filter_of_progression _ hQ hmarkov⟩

/-- The rung between disjunctive and normal, inhabited by an explicit arithmetic family:
rich (every word has positive lower frequency) and nonnormal (frequencies are not uniform). -/
@[blueprint (title := "Perfect-power Lambert constants are rich and nonnormal")]
theorem powerLambert_rich_not_normal (b r : ℕ) (hb : 2 ≤ b) (hr : 2 ≤ r) :
    IsRich b (powerLambert b r) ∧ ¬ IsNormal b (powerLambert b r) :=
  ⟨isRich_powerLambert b r hb hr, not_isNormal_powerLambert b r hb hr⟩

end NormalNumbers.ArithmeticDisjunctivity
