/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorLiouville
import NormalNumbers.LevinSparse

/-!
# The exact normality profile of the Cantor–Liouville points: `IsNormal b x ↔ ¬ 3 ∣ b`

Strengthens Bugeaud 10.37 (`CantorLiouville.exists_computable_liouville_mem_cantorSet_isNormal_two`)
to: there is a computable `e` with `x = cantorLiouvilleReal e ∈ cantorSet`, `x` Liouville, and
for every base `b ≥ 2`, `IsNormal b x ↔ ¬ 3 ∣ b`
(`exists_computable_liouville_mem_cantorSet_normalProfile`).

## The true statement, and the contrast with Cassels

Cassels (1959; Schmidt 1960 independently) proved that for the Cantor measure `μ_K`, almost
every point of `K` is normal to **every base that is not a power of 3**, including `6, 12, 15, …`
(`Literature.Cassels1959`, stated with `μ_K` = the law of `pt (fun _ => true)`).  For *our*
points the profile is different: the forced zero-runs `[a_k, (k+2)a_k)` needed for the Liouville
property make `bʲx` lie within `b⁻¹` of an integer for a fraction `→ 1` of `j ≤ N_k` whenever
`3 ∣ b`, for **every** coin sequence (`not_isNormal_of_three_dvd`).  So the profile is
`¬ 3 ∣ b`, not "`b` is not a power of 3"; base `6` separates them (`not_isNormal_six`).

## Mechanism (bases coprime to 3)

`CantorLiouville.secondMoment_le` with `2ᵏ → bᵏ`.  The base-2 arithmetic input was that `2`
generates `(ℤ/3ᴹ)ˣ`.  For general `b` coprime to 3, with `t = v₃(b² − 1)` (`tb`), `⟨b²⟩` is the
congruence subgroup `1 + 3ᵗℤ` mod `3ᴹ` (3-adic `1 + 3ℤ₃` is procyclic), so the orbit `c·bᵐ`
covers a union of full residue classes mod `3ᵗ`, each lifted uniformly.  The digit-by-digit
`three_point` induction of `residue_sum_le` then runs from position `t` instead of `1`: a constant
loss `(3/2)ᵗ` (`sum_Hf_le_b`).  Pairs with large `v₃(bᵈ − 1)` stay rare by LTE,
`v₃(bᵈ − 1) ≤ t + v₃(d)` (`padicValNat_pow_sub_one_le`): another constant `3ᵗ`.  Both are
absorbed by `3ᵗ < b²`, giving the constant `16 b⁶ |h|` in `secondMoment_le_b`.

## Difficulty check (known-false siblings)

* `3 ∣ b` (incl. `b = 3, 6, 9, 12`): must fail, and the mechanism refuses it — `sum_Hf_le_b`
  needs `b` a unit mod 3 (for `3 ∣ b`, `c·bᵐ` has `v₃ ≥ m`, so `Hf` sees only the shifted
  zeros, cf. `tdig_mul_three_pow`).  The failure is proved separately and for every `ω`
  (`not_isNormal_of_three_dvd`, via `fract_lt_of_mem_run`).
* `b = 4, 16`: covered both directly and via base 2.  `b = 10, 28` (`b ≡ 1 mod 9`, small orbit
  mod `3ᴹ`): `t = 2, 3`; only the constant changes.

## Leaves (sorry, with confidence)

`padicValNat_pow_sub_one_le` (95%), `sum_Hf_le_b` (85%), `secondMoment_le_b` (80%),
`fract_lt_of_mem_run` (90%), `not_isNormal_of_three_dvd` (85%),
`exists_computable_normal_sched_family` (70%).  Everything else is proved wiring.
-/

open MeasureTheory Filter Topology

namespace NormalNumbers.CantorLiouvilleAll

open CantorLiouville DecayAeNormal ExplicitSquare CantorSelfSimilar

/-! ## Cited contrast -/

namespace Literature

/-- **Cassels 1959** (J. W. S. Cassels, *On a problem of Steinhaus about normal numbers*, Colloq.
Math. 7 (1959) 95–101; independently W. M. Schmidt, *On normal numbers*, Pacific J. Math. 10
(1960) 661–672): almost every point of the middle-third Cantor set for the Cantor measure is
normal to every base that is not a power of `3`.  The Cantor measure is the law of
`pt (fun _ => true)` under fair coins (all ternary digits `0`/`2`, independent, uniform).
Recorded only as the contrast to `not_isNormal_six`; nothing here uses it. -/
def Cassels1959 : Prop :=
  ∀ᵐ ω ∂coinMeasure, ∀ b : ℕ, 2 ≤ b → (∀ k : ℕ, b ≠ 3 ^ k) → IsNormal b (pt (fun _ => true) ω)

end Literature

/-! ## Arithmetic: bases coprime to 3 -/

/-- The 3-adic defect `t = v₃(b² − 1)` of a base coprime to 3 (`t = 1` for `b = 2`). -/
def tb (b : ℕ) : ℕ := padicValNat 3 (b ^ 2 - 1)

/-- **LTE bound.**  Confidence 95%.

English proof.  `b² ≡ 1 mod 3`.  If `b ≡ 1 mod 3`: Mathlib's `padicValNat.pow_sub_pow`
(odd prime, `3 ∣ b − 1`, `3 ∤ b`) gives `v₃(bᵈ − 1) = v₃(b − 1) + v₃(d) ≤ v₃(b² − 1) + v₃(d)`
(as `b − 1 ∣ b² − 1`).  If `b ≡ 2 mod 3`: for odd `d`, `bᵈ ≡ 2 mod 3`, so `v₃ = 0`; for
`d = 2d'`, apply LTE to `(b²)^{d'} − 1`: `v₃ = v₃(b² − 1) + v₃(d') ≤ t + v₃(d)`. -/
theorem padicValNat_pow_sub_one_le {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) {d : ℕ} (hd : d ≠ 0) :
    padicValNat 3 (b ^ d - 1) ≤ tb b + padicValNat 3 d := by
  sorry

/-- `3ᵗ < b²`, so every constant `3^{O(t)}` is `b^{O(1)}`. -/
theorem three_pow_tb_lt {b : ℕ} (hb : 2 ≤ b) : 3 ^ tb b < b ^ 2 := by
  have hne : b ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ b ^ 2 := by nlinarith
    omega
  have h1 : 3 ^ tb b ≤ b ^ 2 - 1 := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have : 1 ≤ b ^ 2 := by nlinarith
  omega

/-- **Coset version of `sum_Hf_le`.**  Confidence 85%.

English proof.  Write `L = orderOf (b : ZMod 3^{j+1}) ≤ φ(3^{j+1}) = 2·3ʲ`; the summand has
period `L` in `m` (`Hf_periodic`, as in `sum_Hf_le`), so it suffices to show one period sums to
`≤ L (3/2)ᵗ (2/3)^{|posSet|}`.  If `j + 1 < t` this is trivial: `|posSet| ≤ j < t` and `Hf ≤ 1`.
Otherwise `⟨b²⟩ = 1 + 3ᵗℤ` in `(ℤ/3^{j+1})ˣ` (`b² = 1 + 3ᵗu`, `3 ∤ u`; the subgroup
`1 + 3ᵗℤ` is cyclic of order `3^{j+1−t}` and `b²` has exactly that order), so `⟨b⟩` is a union of
`L / 3^{j+1−t}` residue classes mod `3ᵗ`, and one period of `c·bᵐ mod 3^{j+1}` enumerates the
coset `c⟨b⟩` once.  For a fixed class `r mod 3ᵗ`, the `residue_sum_le` induction from `k = t`
(not `k = 1`) gives `Σ_{u ≡ r} Hf free v (j+1) u ≤ 3^{j+1−t} (2/3)^{#free in [v+t, v+j]}` (each
step fixes the lower digits and uses `three_point` on the new top digit).  The positions of
`posSet` below `v + t` number `≤ t − 1`. -/
theorem sum_Hf_le_b (free : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (v j c : ℕ)
    (hc : ¬ 3 ∣ c) (N : ℕ) :
    ∑ m ∈ Finset.range N, Hf free v (j + 1) ((c * b ^ m : ℕ) : ℝ) ≤
      (N + 2 * 3 ^ j) * (3 / 2 : ℝ) ^ tb b * (2 / 3 : ℝ) ^ (posSet free v (j + 1)).card := by
  sorry

/-- **Cassels second moment, base `b` coprime to 3.**  Confidence 80%.

English proof.  `secondMoment_le_explicit` verbatim with `2 → b`: `secondMoment_expand` (base-free
up to `2ᵏ → bᵏ`) gives `Σ_{n,m} Bf free M (h(bⁿ − bᵐ))`; the pair `m < n` has frequency
`h(bᵈ − 1)·bᵐ`, `d = n − m`.  Good `d` (`e + v₃(bᵈ−1) + 1 ≤ F/2`, `e = v₃ h`): `good_shift` with
`sum_Hf_le_b` in place of `sum_Hf_le`, an extra `(3/2)ᵗ`.  Bad `d`: by
`padicValNat_pow_sub_one_le` they have `v₃(d) ≥ W − e − t`, so there are
`≤ N / 3^{W−e−t−1}` of them (`bad_count` with `3^{t}` more).  The explicit constant becomes
`(1 + 3(3^{e+t+1} + 2))(3/2)ᵗ ≤ 16·|h|·(9/2)ᵗ ≤ 16·|h|·b⁶` (`3ᵉ ≤ |h|`, `three_pow_tb_lt`). -/
theorem secondMoment_le_b (free : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ)
    (hh : h ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * pt free ω)‖ ^ 2 ∂coinMeasure ≤
      16 * (b : ℝ) ^ 6 * |(h : ℝ)| * (N : ℝ) ^ 2 *
        (Real.exp (-(Real.log (3 / 2) / 2) * freeCount free (Nat.log 3 N / 2)) +
          (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  sorry

/-! ## Davenport–Erdős–LeVeque, base `b` (copy of `ae_isNormal_two_of_secondMoment`) -/

/-- **DEL along a schedule with ratio → 1, base `b`.**  Proved: the base-2 proof with
`2 → b` and `LevinSparse.fourierMean_orbit`. -/
theorem ae_isNormal_of_secondMoment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {b : ℕ} (hb : 2 ≤ b) (G : Ω → ℝ) (hG : Measurable G) (n : ℕ → ℕ)
    (hn : StrictMono n) (hratio : Tendsto (fun j => (n (j + 1) : ℝ) / n j) atTop (𝓝 1))
    (hsum : ∀ h : ℤ, h ≠ 0 → Summable fun j =>
      (∫ ω, ‖∑ k ∈ Finset.range (n j), ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂μ) / ((n j : ℝ) ^ 2)) :
    ∀ᵐ ω ∂μ, IsNormal b (G ω) := by
  have hone : ∀ h : ℤ, h ≠ 0 → ∀ᵐ ω ∂μ, Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω)) / (N : ℂ)) atTop (𝓝 0) := by
    intro h hh
    set S : ℕ → Ω → ℂ := fun N ω => ∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω) with hSdef
    have hSm : ∀ N, Measurable (S N) := fun N =>
      Finset.measurable_sum _ fun k _ => measurable_ee.comp (hG.const_mul _)
    have hSb : ∀ N ω, ‖S N ω‖ ≤ N := fun N ω =>
      (norm_sum_le _ _).trans (by simp [norm_ee])
    set f : ℕ → Ω → ℝ := fun j ω => ‖S (n j) ω‖ ^ 2 / ((n j : ℝ)) ^ 2 with hfdef
    have hf0 : ∀ j ω, 0 ≤ f j ω := fun j ω => by positivity
    have hfm : ∀ j, Measurable (f j) := fun j => (((hSm _).norm.pow_const 2).div_const _)
    have hfi : ∀ j, Integrable (f j) μ := fun j =>
      Integrable.of_bound (hfm j).aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (hf0 j ω)]
        rcases Nat.eq_zero_or_pos (n j) with h0 | hpos
        · simp [f, h0]
        · have hpos' : (0 : ℝ) < n j := by exact_mod_cast hpos
          rw [div_le_one (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hSb _ ω) 2)
    have hfI : ∀ j, ∫ ω, f j ω ∂μ =
        (∫ ω, ‖∑ k ∈ Finset.range (n j), ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂μ) / ((n j : ℝ) ^ 2) := by
      intro j; simp only [f, S]; rw [integral_div]
    have hlin : ∫⁻ ω, ∑' j, ENNReal.ofReal (f j ω) ∂μ ≠ ⊤ := by
      rw [lintegral_tsum fun j => (hfm j).ennreal_ofReal.aemeasurable]
      refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
        (r := ∑' j : ℕ, ∫ ω, f j ω ∂μ)) ?_
      have hs : Summable fun j => ∫ ω, f j ω ∂μ := by simp_rw [hfI]; exact hsum h hh
      rw [ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (hf0 j)) hs]
      refine ENNReal.tsum_le_tsum fun j => ?_
      rw [← ofReal_integral_eq_lintegral_ofReal (hfi j) (Eventually.of_forall (hf0 j))]
    have hae := ae_lt_top' (AEMeasurable.tsum fun j =>
      (hfm j).ennreal_ofReal.aemeasurable) hlin
    filter_upwards [hae] with ω hω
    have h1 : Tendsto (fun j => ENNReal.ofReal (f j ω)) atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
    have h2 : Tendsto (fun j => f j ω) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
      simpa [Function.comp_def, ENNReal.toReal_ofReal (hf0 _ ω)] using this
    have h3 : Tendsto (fun j : ℕ => ‖S (n j) ω‖ / (n j : ℝ)) atTop (𝓝 0) := by
      have := h2.sqrt
      rw [Real.sqrt_zero] at this
      refine this.congr fun j => ?_
      simp only [hfdef]
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)]
    exact tendsto_of_tendsto_sched (fun k => ee (h * (b : ℝ) ^ k * G ω)) (fun k => (norm_ee _).le) n hn
      hratio h3
  have hall : ∀ᵐ ω ∂μ, ∀ h : ℤ, h ≠ 0 → Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω)) / (N : ℂ)) atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro h
    by_cases hh : h = 0
    · exact Eventually.of_forall fun ω hne => absurd hh hne
    · filter_upwards [hone h hh] with ω hω _ using hω
  filter_upwards [hall] with ω hω
  rw [isNormal_iff_equidistributed_orbit b hb]
  refine equidistributed_of_weyl _ (fun k => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩) ?_
  intro h hh
  have := hω h hh
  refine this.congr fun N => ?_
  rw [LevinSparse.fourierMean_orbit]


/-! ## Almost every coin sequence -/

/-- **Base `b` coprime to 3, a.e.**  Wiring (proved from `secondMoment_le_b`). -/
theorem ae_isNormal_of_coprime_three {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) :
    ∀ᵐ ω ∂coinMeasure, IsNormal b (cantorLiouvilleReal ω) := by
  refine ae_isNormal_of_secondMoment coinMeasure hb _ (measurable_pt isFree) sched
    sched_strictMono sched_ratio ?_
  intro h hh
  have hC : (0 : ℝ) < 16 * (b : ℝ) ^ 6 * |(h : ℝ)| := by
    have : (h : ℝ) ≠ 0 := by exact_mod_cast hh
    positivity
  have hl : 0 < Real.log (3 / 2) / 2 := by have := Real.log_pos (by norm_num : (1:ℝ) < 3 / 2); linarith
  refine (summable_sched_bound _ _ hC hl).of_nonneg_of_le
    (fun j => div_nonneg (integral_nonneg fun ω => by positivity) (by positivity))
    (fun j => ?_)
  have hN : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ _ := secondMoment_le_b isFree hb h3 h hh (sched j) (one_le_sched j)
    _ = _ := by ring

/-! ## Bases divisible by 3 fail for every coin sequence -/

/-- **Near-integers on a run.**  Confidence 90%.

English proof.  Split `x = cantorLiouvilleReal ω = P + θ` at place `a = runStart k`:
`P = Σ_{i<a} dᵢ 3^{−(i+1)} ∈ 3^{−a}ℤ` and, the digits on `[a, (k+2)a)` being forced `0`,
`θ = Σ_{i ≥ (k+2)a} dᵢ 3^{−(i+1)}`, with `0 ≤ θ < 3^{−(k+2)a}` strictly (digits `≤ 2`, and the
next run forces a `0`, so the geometric bound is not attained).  Since `3 ∣ b` and `j ≥ a`,
`3^a ∣ bʲ`, so `bʲP ∈ ℤ`; and `bʲθ < bʲ 3^{−(k+2)a} ≤ b⁻¹` by `hj2`.  Hence
`fract(bʲx) = bʲθ < 1/b`. -/
theorem fract_lt_of_mem_run (ω : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b) {k j : ℕ}
    (hj1 : runStart k ≤ j) (hj2 : b ^ (j + 1) ≤ 3 ^ ((k + 2) * runStart k)) :
    Int.fract (cantorLiouvilleReal ω * (b : ℝ) ^ j) < 1 / b := by
  sorry

/-- **Every base divisible by 3 fails, for every `ω`.**  Confidence 85%.

English proof.  Suppose `IsNormal b x`; by Wall (`isNormal_iff_equidistributed_orbit`) the
visit frequency of `orbit b x` to `[0, 1/b)` tends to `1/b ≤ 1/3`.  Let `a = runStart k`,
`E = (k+2)a` and `N_k = ⌊E / log₃ b⌋` (so `b^{N_k} ≤ 3^E`).  By `fract_lt_of_mem_run`, every
`j ∈ [a, N_k − 1)` visits `[0, 1/b)`, so `visitCount ≥ N_k − 1 − a`.  Since
`b ≤ 3^{log₃ b}` and `log₃ b ≤ b`, `N_k ≥ E / b − 1 = (k+2)a/b − 1`, and
`(N_k − 1 − a)/N_k ≥ 1 − (2 + a)/N_k → 1 − b/(k+2) → 1` (`a → ∞`, `runStart` grows).  So the
frequency along `N_k` tends to `1 ≠ 1/b`. -/
theorem not_isNormal_of_three_dvd (ω : ℕ → Bool) {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b) :
    ¬ IsNormal b (cantorLiouvilleReal ω) := by
  sorry

/-- **The separating base.**  Cassels (`Literature.Cassels1959`) makes `μ_K`-a.e. point normal
to base 6; no Cantor–Liouville point is. -/
theorem not_isNormal_six (ω : ℕ → Bool) : ¬ IsNormal 6 (cantorLiouvilleReal ω) :=
  not_isNormal_of_three_dvd ω (by norm_num) (by norm_num)

/-- **Normality profile, a.e. form.**  Wiring (proved). -/
theorem ae_normalProfile :
    ∀ᵐ ω ∂coinMeasure, ∀ b : ℕ, 2 ≤ b → (IsNormal b (cantorLiouvilleReal ω) ↔ ¬ 3 ∣ b) := by
  have hall : ∀ᵐ ω ∂coinMeasure, ∀ b : ℕ, 2 ≤ b → ¬ 3 ∣ b → IsNormal b (cantorLiouvilleReal ω) := by
    rw [ae_all_iff]
    intro b
    by_cases hb : 2 ≤ b
    · by_cases h3 : 3 ∣ b
      · exact Eventually.of_forall fun ω _ h => absurd h3 h
      · filter_upwards [ae_isNormal_of_coprime_three hb h3] with ω hω _ _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hb
  filter_upwards [hall] with ω hω b hb
  exact ⟨fun hn h3 => not_isNormal_of_three_dvd ω hb h3 hn, hω b hb⟩

/-- **Normality profile, existence.**  Wiring (proved). -/
theorem exists_liouville_mem_cantorSet_normalProfile :
    ∃ x : ℝ, x ∈ cantorSet ∧ Liouville x ∧ ∀ b : ℕ, 2 ≤ b → (IsNormal b x ↔ ¬ 3 ∣ b) := by
  obtain ⟨ω, hn, hf⟩ := (ae_normalProfile.and ae_frequently_free).exists
  exact ⟨_, pt_mem_cantorSet _ _, liouville_cantorLiouvilleReal ω hf, hn⟩

/-! ## Computable form -/

section Computable

open Derandomize SchedDerandomize

/-- **Family version of `SchedDerandomize.exists_computable_normal_sched`.**  Confidence 70%.

English proof.  The tests of `exists_computable_normal_sched` are already base-generic
(`fails Ψ b …`, `sprimrec_fails`, `level_bound_w` take `b`); only the assembly fixes `b = 2`.
Run the base-`b` level tests (for each `b` with `S b`) from stage `j ≥ g b` on, with
`g b = j₀ + ⌈4 B_b⌉ + 2 + b`, `B_b = 74016 √(κ b) Zc + 1` replaced by the primrec upper bound
`74016 (κ b + 1) (Zc + 1)` (`Zc` is a fixed real; any fixed rational bound for it works).  The
base-`b` test at stage `j` has mass `≤ B_b/(j+1)²` (`level_bound_w` and `hev`, as in the
base-2 assembly), so the total mass over `b` and `j ≥ g b` is `≤ Σ_b B_b/g b ≤ Σ_b 2^{-b}·…`
after choosing `g b ≥ 4^{b+2} B_b`; together with `bad'` it is `< 1`, so `exists_primrec_avoid`
gives a computable avoider.  Avoiding base `b` from stage `g b` on gives `IsNormal b` exactly as
in the base-2 proof (`good_of_pass`, schedule ratio `→ 1`). -/
theorem exists_computable_normal_sched_family (Ψ : ℕ → ℕ → List Bool → ℕ)
    (hΨp : Primrec fun x : ℕ × ℕ × List Bool => Ψ x.1 x.2.1 x.2.2) (A : List Bool → ℝ)
    (hΨ : ∀ b m p, Ψ b m p = ⌊A p * (b : ℝ) ^ m⌋₊) (hA0 : ∀ p, 0 ≤ A p)
    (G : (ℕ → Bool) → ℝ) (hGm : Measurable G)
    (hAG : ∀ ω D, A (pre ω D) ≤ G ω ∧ G ω ≤ A (pre ω D) + (1 / 2 : ℝ) ^ D)
    (S : ℕ → Prop) [DecidablePred S] (hS : PrimrecPred S) (κ : ℕ → ℕ) (hκ : Primrec κ)
    (W : ℕ → ℝ) (hW0 : ∀ N, 0 ≤ W N) (hWa : Antitone W)
    (hsm : ∀ b, 2 ≤ b → S b → ∀ h : ℤ, h ≠ 0 → ∀ N : ℕ, 1 ≤ N →
      ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * G ω)‖ ^ 2 ∂coins ≤
        κ b * |(h : ℝ)| * N ^ 2 * W N)
    (Ns nr : ℕ → ℕ) (hNs : Primrec Ns) (hnr : Primrec nr) (hNtop : Tendsto Ns atTop atTop)
    (hrat : ∀ a : ℝ, 1 < a → ∀ᶠ j in atTop, (Ns (j + 1) : ℝ) ≤ a * Ns j)
    (hnrtop : Tendsto nr atTop atTop)
    (hev : ∀ᶠ j in atTop, 8 ≤ nr j ∧ nr j ≤ Ns j ∧
      (nr j : ℝ) ^ 6 * W (Ns j) ≤ 1 / ((j : ℝ) + 1) ^ 4)
    (bad' : ℕ → List Bool → Bool) (hbad' : Primrec₂ bad') (d' : ℕ → ℕ) (hd' : Primrec d')
    (hmass : ∀ j, coins.real {ω | bad' j (pre ω (d' j)) = true} ≤ 1 / ((j : ℝ) + 1) ^ 2) :
    ∃ e : ℕ → Bool, Computable e ∧ (∀ b, 2 ≤ b → S b → IsNormal b (G e)) ∧
      ∃ j₁, ∀ j, j₁ ≤ j → bad' j (pre e (d' j)) = false := by
  sorry

/-- The base-`b` second moment in `clW` form (wiring from `secondMoment_le_b`). -/
theorem cl_secondMoment_b {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ) (hh : h ≠ 0) (N : ℕ)
    (hN : 1 ≤ N) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * cantorLiouvilleReal ω)‖ ^ 2 ∂coins ≤
      ((16 * b ^ 6 : ℕ) : ℝ) * |(h : ℝ)| * N ^ 2 * clW N := by
  have hW : clW N = Real.exp (-(Real.log (3 / 2) / 2) * freeCount isFree (Nat.log 3 N / 2)) +
      (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [clW, max_eq_left hN]
  rw [hW]
  refine (secondMoment_le_b isFree hb h3 h hh N hN).trans (le_of_eq ?_)
  push_cast; ring

theorem primrec_notThreeDvd : PrimrecPred fun b : ℕ => ¬ 3 ∣ b := by
  refine PrimrecPred.not ?_
  have : PrimrecPred fun b : ℕ => b % 3 = 0 :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 3)) (Primrec.const 0)
  exact this.of_eq fun b => (Nat.dvd_iff_mod_eq_zero).symm

theorem primrec_kappa : Primrec fun b : ℕ => 16 * b ^ 6 :=
  Primrec.nat_mul.comp (Primrec.const 16)
    (ComputableNormal.primrec_pow.comp Primrec.id (Primrec.const 6))

end Computable

/-- **The normality profile, computable.**  Wiring (proved from the leaves): a computable
`e` such that `x = cantorLiouvilleReal e` lies in the middle-third Cantor set, is Liouville, and
is normal to exactly the bases not divisible by 3. -/
theorem exists_computable_liouville_mem_cantorSet_normalProfile :
    ∃ e : ℕ → Bool, Computable e ∧ cantorLiouvilleReal e ∈ cantorSet ∧
      Liouville (cantorLiouvilleReal e) ∧
      ∀ b : ℕ, 2 ≤ b → (IsNormal b (cantorLiouvilleReal e) ↔ ¬ 3 ∣ b) := by
  obtain ⟨e, hce, hn, j₁, hj⟩ := exists_computable_normal_sched_family clΨ primrec_clΨ clA
    clΨ_eq clA_nonneg cantorLiouvilleReal measurable_cantorLiouvilleReal clA_bounds
    (fun b => ¬ 3 ∣ b) primrec_notThreeDvd (fun b => 16 * b ^ 6) primrec_kappa
    clW clW_nonneg clW_antitone (fun b hb h3 h hh N hN => cl_secondMoment_b hb h3 h hh N hN)
    clNs clNr primrec_clNs primrec_clNr tendsto_clNs clNs_ratio tendsto_clNr cl_ev clBad
    primrec_clBad clD primrec_clD clBad_mass
  refine ⟨e, hce, pt_mem_cantorSet _ _,
    liouville_cantorLiouvilleReal e (frequently_free_of_clBad e j₁ hj), fun b hb => ?_⟩
  exact ⟨fun hn' h3 => not_isNormal_of_three_dvd e hb h3 hn', hn b hb⟩

end NormalNumbers.CantorLiouvilleAll
