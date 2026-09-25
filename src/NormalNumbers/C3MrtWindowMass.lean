/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtTTPretentious
import PrimeNumberTheoremAnd.BrunTitchmarsh

/-!
# The sharp window mass, from Brun–Titchmarsh

`UniformResonantMass` (`C3MrtTTPretentious`) needs the reciprocal mass of the primes in a short
multiplicative window `(P, P(1+w)]` to be `≲ w / log P` — proportional to the window width,
with NO additive constant.  An additive constant per window is fatal: the resonance covering
produces `≈ |t| log Y` windows, and TT allow `|t|` up to `(log X)^{1/125}`.  This is exactly
why the dependency's interval Mertens (`reciprocalPrimeInterval_le_log_ratio`, additive error
`2·mertensBound`) cannot be summed, and it is recorded as refuted in `PENDING_WORK.md`.

Brun–Titchmarsh supplies precisely the missing shape, and it is already available, proved and
axiom-clean, in `PrimeNumberTheoremAnd.BrunTitchmarsh`:

    `primesBetween x (x+y) ≤ 2y/log z + 6z(1+log z)³`   for `0 < x`, `0 < y`, `1 < z`.

Taking `z = √P` turns it into `#{p ∈ (P, P(1+w)]} ≤ 4Pw/log P + 6√P(1 + ½log P)³`, and dividing
by `P` (every prime in the window exceeds `P`) gives this file's brick,
`short_interval_mass_le`.  The second term decays like `P^{-1/2}(log P)³` — it is summable over
the windows at every height, which the flat `2·mertensBound` is not.
-/

open Finset Real

namespace NormalNumbers

namespace CastingOut

/-- Every prime in the real window `(P, P(1+w)]` lies in Brun–Titchmarsh's index set. -/
theorem window_subset_primesBetween {P w : ℝ} (hP : 0 < P) (hw : 0 ≤ w) {G : Finset ℕ}
    (hG : ∀ p ∈ G, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ P * (1 + w)) :
    G ⊆ (Finset.Icc ⌈P⌉₊ ⌊P + P * w⌋₊).filter Nat.Prime := by
  intro p hp
  obtain ⟨hpp, hlo, hhi⟩ := hG p hp
  refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨Nat.ceil_le.2 hlo.le, Nat.le_floor ?_⟩, hpp⟩
  calc (p : ℝ) ≤ P * (1 + w) := hhi
    _ = P + P * w := by ring

/-- **The sharp short-interval prime mass.**  In a multiplicative window `(P, P(1+w)]` with
`P ≥ 2`, the primes carry reciprocal mass at most `4w/log P + 6(1 + log P)³/√P`.

The first term is the one that matters: it is proportional to the window width `w`, so it can
be summed over the `≈ |t| log Y` resonance windows.  The second decays faster than any power
of `log P`, so it too survives summation over a geometric stack of heights. -/
theorem short_interval_mass_le {P w : ℝ} (hP : 2 ≤ P) (hw : 0 < w) {G : Finset ℕ}
    (hG : ∀ p ∈ G, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ P * (1 + w)) :
    ∑ p ∈ G, (p : ℝ)⁻¹ ≤ 4 * w / Real.log P + 6 * (1 + Real.log P) ^ 3 / Real.sqrt P := by
  have hP0 : (0 : ℝ) < P := by linarith
  have hlogP : (0 : ℝ) < Real.log P := Real.log_pos (by linarith)
  have hsq : (1 : ℝ) < Real.sqrt P := by
    have : Real.sqrt 1 < Real.sqrt P := Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    simpa using this
  have hsq0 : (0 : ℝ) < Real.sqrt P := by linarith
  have hlogsq : Real.log (Real.sqrt P) = Real.log P / 2 := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow hP0]; ring
  -- Brun–Titchmarsh at level `z = √P`
  have hBT := BrunTitchmarsh.primesBetween_le P (P * w) (Real.sqrt P) hP0 (by positivity) hsq
  rw [hlogsq] at hBT
  -- the cardinality of `G`
  have hcard : (G.card : ℝ) ≤ (BrunTitchmarsh.primesBetween P (P + P * w) : ℝ) := by
    have := Finset.card_le_card (window_subset_primesBetween hP0 hw.le hG)
    exact_mod_cast this
  -- every prime in the window exceeds `P`
  have hmass : ∑ p ∈ G, (p : ℝ)⁻¹ ≤ (G.card : ℝ) * P⁻¹ := by
    calc ∑ p ∈ G, (p : ℝ)⁻¹ ≤ ∑ _p ∈ G, P⁻¹ := by
          refine Finset.sum_le_sum fun p hp => ?_
          have := (hG p hp).2.1
          exact inv_anti₀ hP0 this.le
      _ = (G.card : ℝ) * P⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hchain : (G.card : ℝ)
      ≤ 2 * (P * w) / (Real.log P / 2) + 6 * Real.sqrt P * (1 + Real.log P / 2) ^ 3 :=
    le_trans hcard hBT
  have hstep : (G.card : ℝ) * P⁻¹
      ≤ (2 * (P * w) / (Real.log P / 2) + 6 * Real.sqrt P * (1 + Real.log P / 2) ^ 3) * P⁻¹ :=
    mul_le_mul_of_nonneg_right hchain (by positivity)
  refine le_trans hmass (le_trans hstep ?_)
  · have hPsq : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt hP0.le
    have h1 : 2 * (P * w) / (Real.log P / 2) * P⁻¹ = 4 * w / Real.log P := by
      field_simp; ring
    have h2 : 6 * Real.sqrt P * (1 + Real.log P / 2) ^ 3 * P⁻¹
        ≤ 6 * (1 + Real.log P) ^ 3 / Real.sqrt P := by
      have hinv : Real.sqrt P * P⁻¹ = (Real.sqrt P)⁻¹ := by
        rw [← div_eq_mul_inv]
        first
          | exact Real.sqrt_div_self
          | exact Real.sqrt_div_self'
          | (rw [div_eq_iff (ne_of_gt hP0)]; field_simp; linarith [hPsq])
      have hrw : 6 * Real.sqrt P * (1 + Real.log P / 2) ^ 3 * P⁻¹
          = 6 * (1 + Real.log P / 2) ^ 3 * (Real.sqrt P * P⁻¹) := by ring
      rw [hrw, hinv, ← div_eq_mul_inv]
      have hmono : (1 + Real.log P / 2) ^ 3 ≤ (1 + Real.log P) ^ 3 := by
        gcongr
        linarith
      have : 6 * (1 + Real.log P / 2) ^ 3 ≤ 6 * (1 + Real.log P) ^ 3 := by linarith
      exact div_le_div_of_nonneg_right this hsq0.le
    rw [add_mul, h1]
    linarith

/-! ## Two elementary bricks for the resonance sum -/

/-- `log u ≤ c·u − 1 − log c` for every `c, u > 0`: the tangent-line bound on the logarithm,
with the slope a free parameter.  Used to absorb the small-prime mass `log log P₁` into the
`log(2+|t|)` budget: `log log s ≤ c log s + O_c(1)` for every `c > 0`. -/
theorem log_le_mul_sub {c : ℝ} (hc : 0 < c) {u : ℝ} (hu : 0 < u) :
    Real.log u ≤ c * u - 1 - Real.log c := by
  have h := Real.log_le_sub_one_of_pos (x := c * u) (by positivity)
  rw [Real.log_mul (ne_of_gt hc) (ne_of_gt hu)] at h
  linarith

/-- The small-prime absorption in the form the resonance argument uses. -/
theorem log_log_le_mul_log {c : ℝ} (hc : 0 < c) {s : ℝ} (hs : 1 < s) :
    Real.log (Real.log s) ≤ c * Real.log s - 1 - Real.log c :=
  log_le_mul_sub hc (Real.log_pos hs)

/-- **The resonance harmonic sum.**  With `γ_m = |arg z − 2πm| ≥ 2π|m| − π`, the reciprocals of
the window gaps `γ_m − δ` over `1 ≤ m ≤ K` sum to at most `(2/π)(1 + log K)`.

The gap bound is `2πm − π − δ ≥ (π/2)m` for `m ≥ 1` and `δ ≤ π/2`, which is what makes the
sum harmonic; mathlib's `harmonic_le_one_add_log` finishes it. -/
theorem sum_inv_gap_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ π / 2) (K : ℕ) :
    ∑ m ∈ Finset.Icc 1 K, (2 * π * (m : ℝ) - π - δ)⁻¹ ≤ (2 / π) * (1 + Real.log K) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hstep : ∀ m ∈ Finset.Icc 1 K, (2 * π * (m : ℝ) - π - δ)⁻¹ ≤ (2 / π) * ((m : ℝ)⁻¹) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
      have := (Finset.mem_Icc.1 hm).1
      exact_mod_cast this
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
    have hgap : (π / 2) * (m : ℝ) ≤ 2 * π * (m : ℝ) - π - δ := by nlinarith
    have hgap0 : (0 : ℝ) < (π / 2) * (m : ℝ) := by positivity
    calc (2 * π * (m : ℝ) - π - δ)⁻¹ ≤ ((π / 2) * (m : ℝ))⁻¹ := by
          exact inv_anti₀ hgap0 hgap
      _ = (2 / π) * ((m : ℝ)⁻¹) := by field_simp
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have hharm : ∑ m ∈ Finset.Icc 1 K, ((m : ℝ))⁻¹ ≤ 1 + Real.log K := by
    have h := harmonic_le_one_add_log K
    have heq : ((harmonic K : ℚ) : ℝ) = ∑ m ∈ Finset.Icc 1 K, ((m : ℝ))⁻¹ := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    rwa [heq] at h
  exact mul_le_mul_of_nonneg_left hharm (by positivity)

/-- `exp x − 1 ≤ 2x` on `[0,1]`, from mathlib's `Real.exp_bound` at `n = 1`.  This converts a
resonance window, which is an interval in `log p`, into a multiplicative window `(P, P(1+w)]`
with `w` proportional to the window length. -/
theorem exp_sub_one_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 ≤ 2 * x := by
  have habs : |x| ≤ 1 := abs_le.2 ⟨by linarith, hx1⟩
  have h := Real.exp_bound habs (n := 1) (by norm_num)
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one] at h
  have hax : |x| = x := abs_of_nonneg hx0
  rw [hax] at h
  have h2 := (abs_le.1 h).2
  norm_num at h2
  linarith

/-- **The resonance window mass.**  A set of primes confined to a window of length `2δ/|t|` in
`log p`, starting at height `a ≥ log 2`, carries reciprocal mass at most
`16δ/(|t|·a) + 6(1+a)³·exp(−a/2)`.

The first term is the one that sums: with `a = (γ_m − δ)/|t|` it is `16δ/(γ_m − δ)`, and
`sum_inv_gap_le` sums that over the windows.  The second is the Brun–Titchmarsh error, which
decays in the *height* `a` and is handled by grouping windows into dyadic blocks in `log p`. -/
theorem resonant_window_mass_le {t δ a : ℝ} (hδ0 : 0 < δ) (ht : 2 * δ ≤ |t|)
    (ha : Real.log 2 ≤ a) {G : Finset ℕ} (hGp : ∀ p ∈ G, p.Prime)
    (hGw : ∀ p ∈ G, a < Real.log p ∧ Real.log p < a + 2 * δ / |t|) :
    ∑ p ∈ G, (p : ℝ)⁻¹ ≤ 16 * δ / (|t| * a) + 6 * (1 + a) ^ 3 / Real.sqrt (Real.exp a) := by
  have htpos : (0 : ℝ) < |t| := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hapos : (0 : ℝ) < a := by linarith
  set x : ℝ := 2 * δ / |t| with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one htpos]; linarith
  set w : ℝ := Real.exp x - 1 with hw
  have hw0 : 0 < w := by
    rw [hw, sub_pos]
    linarith [Real.add_one_le_exp x]
  have hw2 : w ≤ 2 * x := exp_sub_one_le_two_mul hx0.le hx1
  set P : ℝ := Real.exp a with hP
  have hP2 : (2 : ℝ) ≤ P := by
    rw [hP, show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log]; norm_num]
    exact Real.exp_le_exp.2 ha
  have hlogP : Real.log P = a := by rw [hP, Real.log_exp]
  have hG : ∀ p ∈ G, p.Prime ∧ P < (p : ℝ) ∧ (p : ℝ) ≤ P * (1 + w) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hGw p hp
    have hppos : (0 : ℝ) < (p : ℝ) := by
      have := (hGp p hp).pos
      exact_mod_cast this
    refine ⟨hGp p hp, ?_, ?_⟩
    · rw [hP, ← Real.exp_log hppos]
      exact Real.exp_lt_exp.2 h1
    · have : (p : ℝ) < Real.exp (a + x) := by
        rw [← Real.exp_log hppos]
        exact Real.exp_lt_exp.2 h2
      have heq : Real.exp (a + x) = P * (1 + w) := by
        rw [hP, hw, Real.exp_add]; ring
      linarith [heq ▸ this]
  have hmain := short_interval_mass_le hP2 hw0 hG
  rw [hlogP] at hmain
  refine le_trans hmain ?_
  have hwt : 4 * w * |t| ≤ 16 * δ := by
    have hb : w * |t| ≤ 2 * x * |t| := by nlinarith [hw2, htpos]
    have hc : 2 * x * |t| = 4 * δ := by rw [hx]; field_simp; ring
    nlinarith [hb, hc]
  have h1 : 4 * w / a ≤ 16 * δ / (|t| * a) := by
    rw [div_le_div_iff₀ hapos (by positivity)]
    nlinarith [hwt, hapos, htpos]
  linarith
