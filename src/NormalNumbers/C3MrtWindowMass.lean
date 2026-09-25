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

/-! ## The `δ`-covering: a resonant prime lands in one window, and the index is bounded

`C3MrtArchimedean` builds this at the fixed half-width `resEps z`.  The Brun–Titchmarsh route
needs a free half-width `δ ≤ resEps z` (lap 73), so the covering is redone here; the gap
`2·resEps z ≤ |arg z − 2πm|` still comes from `two_resEps_le_abs_shift`, and only the
resonance threshold changes. -/

/-- **The window, at half-width `δ`.**  A prime resonating to within `δ` lands in one of the
windows `|t|·log p ∈ (γ_m − δ, γ_m + δ)`, `γ_m = |arg z − 2πm|`. -/
theorem exists_window_of_resonant_width {z : ℂ} (hz : ‖z‖ = 1) {p : ℕ} (hp : 2 ≤ p) {t δ : ℝ}
    (hδ : δ ≤ resEps z) (hres : |(primePhase z t p).arg| < δ) :
    ∃ m : ℤ, |z.arg - 2 * π * m| - δ < |t| * Real.log p ∧
             |t| * Real.log p < |z.arg - 2 * π * m| + δ := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  obtain ⟨m, hm⟩ := exists_int_arg_primePhase hz hp0 t
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hδ0 : 0 < δ := lt_of_le_of_lt (abs_nonneg _) hres
  have hgap : 2 * δ ≤ |z.arg - 2 * π * m| :=
    le_trans (by linarith) (two_resEps_le_abs_shift z m)
  have hkey : |(z.arg - 2 * π * m) - t * Real.log p| < δ := by
    have hc : (z.arg - 2 * π * m) - t * Real.log p = (primePhase z t p).arg := by
      rw [← hm]; ring
    rw [hc]; exact hres
  have habs : |(|z.arg - 2 * π * m|) - |t| * Real.log p| < δ := by
    rcases le_or_gt 0 t with hts | hts
    · have hcpos : 0 < z.arg - 2 * π * m := by
        by_contra hcon
        push_neg at hcon
        have h1 : |z.arg - 2 * π * m| = -(z.arg - 2 * π * m) := abs_of_nonpos hcon
        have h2 := (abs_lt.1 hkey).1
        have h3 : 0 ≤ t * Real.log p := mul_nonneg hts hL.le
        rw [h1] at hgap
        linarith
      rw [abs_of_pos hcpos, abs_of_nonneg hts]
      exact hkey
    · have hcneg : z.arg - 2 * π * m < 0 := by
        by_contra hcon
        push_neg at hcon
        have h1 : |z.arg - 2 * π * m| = z.arg - 2 * π * m := abs_of_nonneg hcon
        have h2 := (abs_lt.1 hkey).2
        have h3 : t * Real.log p < 0 := mul_neg_of_neg_of_pos hts hL
        rw [h1] at hgap
        linarith
      rw [abs_of_neg hcneg, abs_of_neg hts]
      have hrw : -(z.arg - 2 * π * m) - -t * Real.log p
          = -((z.arg - 2 * π * m) - t * Real.log p) := by ring
      rw [hrw, abs_neg]
      exact hkey
  have hsplit := abs_lt.1 habs
  exact ⟨m, by linarith [hsplit.2], by linarith [hsplit.1]⟩

open scoped Classical in
/-- The index of the `δ`-window a prime falls into (junk value `0` if it is not resonant). -/
noncomputable def windowIndexW (z : ℂ) (t δ : ℝ) (p : ℕ) : ℤ :=
  if h : ∃ m : ℤ, |z.arg - 2 * π * m| - δ < |t| * Real.log p ∧
                   |t| * Real.log p < |z.arg - 2 * π * m| + δ
  then h.choose else 0

theorem windowIndexW_spec {z : ℂ} (hz : ‖z‖ = 1) {p : ℕ} (hp : 2 ≤ p) {t δ : ℝ}
    (hδ : δ ≤ resEps z) (hres : |(primePhase z t p).arg| < δ) :
    |z.arg - 2 * π * windowIndexW z t δ p| - δ < |t| * Real.log p ∧
      |t| * Real.log p < |z.arg - 2 * π * windowIndexW z t δ p| + δ := by
  have hex := exists_window_of_resonant_width hz hp hδ hres
  rw [windowIndexW, dif_pos hex]
  exact hex.choose_spec

/-- Only the indices `|m| ≤ (T + δ + π)/(2π)` occur among primes with `|t| log p ≤ T`. -/
theorem abs_windowIndexW_le {z : ℂ} (hz : ‖z‖ = 1) {p : ℕ} (hp : 2 ≤ p) {t δ T : ℝ}
    (hδ : δ ≤ resEps z) (hres : |(primePhase z t p).arg| < δ) (hT : |t| * Real.log p ≤ T) :
    |windowIndexW z t δ p| ≤ (⌈(T + δ + π) / (2 * π)⌉₊ : ℤ) := by
  set m := windowIndexW z t δ p with hm
  obtain ⟨h1, _⟩ := windowIndexW_spec hz hp hδ hres
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hlow : 2 * π * |(m : ℝ)| - π ≤ |z.arg - 2 * π * m| := by
    have h2 : |z.arg| ≤ π := Complex.abs_arg_le_pi z
    have h3 := abs_sub_abs_le_abs_sub (2 * π * (m : ℝ)) z.arg
    rw [abs_sub_comm] at h3
    have h4 : |2 * π * (m : ℝ)| = 2 * π * |(m : ℝ)| := by
      rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * π)]
    linarith [h3, h4 ▸ h3]
  have hfin : |(m : ℝ)| ≤ (T + δ + π) / (2 * π) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * π)]
    nlinarith
  have hceil : (T + δ + π) / (2 * π) ≤ ((⌈(T + δ + π) / (2 * π)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have : |(m : ℝ)| ≤ ((⌈(T + δ + π) / (2 * π)⌉₊ : ℕ) : ℝ) := le_trans hfin hceil
  rw [← Int.cast_abs] at this
  exact_mod_cast this

/-! ## Two bricks for summing over the window indices `m ∈ [−K, K]` -/

/-- **Polynomial beats exponential, explicitly.**  The Brun–Titchmarsh error of
`resonant_window_mass_le` decays exponentially in the window height:
`6(1+a)³/√(exp a) ≤ 10⁵·exp(−a/8)`.  Proved from `exp x ≥ (1 + x/4)⁴`, i.e. four applications
of `Real.add_one_le_exp`, with no factorials. -/
theorem window_err_le {a : ℝ} (ha : 0 ≤ a) :
    6 * (1 + a) ^ 3 / Real.sqrt (Real.exp a) ≤ 100000 * Real.exp (-(a / 8)) := by
  have hsq : Real.sqrt (Real.exp a) = Real.exp (a / 2) := by
    have h2 : (Real.exp (a / 2)) ^ 2 = Real.exp a := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [← h2, Real.sqrt_sq (Real.exp_pos _).le]
  have hexp : (1 + 3 * a / 32) ^ 4 ≤ Real.exp (3 * a / 8) := by
    have h1 : 3 * a / 32 + 1 ≤ Real.exp (3 * a / 32) := Real.add_one_le_exp _
    have h2 : (1 + 3 * a / 32) ^ 4 ≤ (Real.exp (3 * a / 32)) ^ 4 := by
      refine pow_le_pow_left₀ (by positivity) (by linarith) 4
    calc (1 + 3 * a / 32) ^ 4 ≤ (Real.exp (3 * a / 32)) ^ 4 := h2
      _ = Real.exp (3 * a / 8) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hpoly : 6 * (1 + a) ^ 3 ≤ 100000 * (1 + 3 * a / 32) ^ 4 := by
    have hb : (3 / 32 : ℝ) * (1 + a) ≤ 1 + 3 * a / 32 := by linarith
    have hb0 : (0 : ℝ) ≤ (3 / 32 : ℝ) * (1 + a) := by positivity
    have h4 : ((3 / 32 : ℝ) * (1 + a)) ^ 4 ≤ (1 + 3 * a / 32) ^ 4 :=
      pow_le_pow_left₀ hb0 hb 4
    have hcube : (1 + a) ^ 3 ≤ (1 + a) ^ 4 := by
      refine pow_le_pow_right₀ (by linarith) (by norm_num)
    have hval : ((3 / 32 : ℝ) * (1 + a)) ^ 4 = (81 / 1048576 : ℝ) * (1 + a) ^ 4 := by ring
    rw [hval] at h4
    nlinarith [h4, hcube, pow_nonneg (by linarith : (0:ℝ) ≤ 1 + a) 4]
  rw [hsq, div_le_iff₀ (Real.exp_pos _)]
  have hrw : 100000 * Real.exp (-(a / 8)) * Real.exp (a / 2) = 100000 * Real.exp (3 * a / 8) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hrw]
  nlinarith [hexp, hpoly]

/-- **Symmetric index sums.**  A sum over `m ∈ [−K, K] ⊆ ℤ` of a nonnegative function of `|m|`
is at most twice the sum over `0 ≤ j ≤ K`: each fibre of `Int.natAbs` has at most two points. -/
theorem sum_Icc_symm_le {K : ℕ} (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), f |(m : ℝ)|
      ≤ 2 * ∑ j ∈ Finset.range (K + 1), f (j : ℝ) := by
  classical
  have hmaps : ∀ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), m.natAbs ∈ Finset.range (K + 1) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun m : ℤ => f |(m : ℝ)|)]
  refine le_trans (Finset.sum_le_sum (g := fun j : ℕ => 2 * f (j : ℝ)) (fun j _ => ?_))
    (le_of_eq (by rw [Finset.mul_sum]))
  · show ∑ m ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter (fun m => m.natAbs = j), f |(m : ℝ)|
        ≤ 2 * f (j : ℝ)
    have hsub : (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter (fun m => m.natAbs = j)
        ⊆ ({(j : ℤ), -(j : ℤ)} : Finset ℤ) := by
      intro m hm
      have hj : m.natAbs = j := (Finset.mem_filter.1 hm).2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have hconst : ∀ m ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter (fun m => m.natAbs = j),
        f |(m : ℝ)| = f (j : ℝ) := by
      intro m hm
      have hj : m.natAbs = j := (Finset.mem_filter.1 hm).2
      have habs : |m| = (j : ℤ) := by
        have h1 : |m| = (m.natAbs : ℤ) := by
          first
            | exact Int.abs_eq_natAbs m
            | exact (Int.natCast_natAbs m).symm
            | exact (Int.cast_natAbs m).symm
        rw [h1, hj]
      congr 1
      rw [← Int.cast_abs, habs]
      norm_cast
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.Icc (-(K : ℤ)) (K : ℤ)).filter (fun m => m.natAbs = j)).card ≤ 2 := by
      refine le_trans (Finset.card_le_card hsub) ?_
      exact le_trans (Finset.card_insert_le _ _) (by simp)
    have : (((Finset.Icc (-(K : ℤ)) (K : ℤ)).filter (fun m => m.natAbs = j)).card : ℝ) ≤ 2 := by
      exact_mod_cast hcard
    exact mul_le_mul_of_nonneg_right this (hf _)

/-- **The geometric sum.**  `∑_{j<n} exp(−cj) ≤ 1 + 1/c` for `c > 0`, from
`exp(−c) ≤ 1/(1+c)`.  With `c = π/(32|t|)` — the spacing of the resonance windows in the
height variable `a` — this is the `1 + 32|t|/π` that the Brun–Titchmarsh error tail costs. -/
theorem sum_exp_neg_le {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ∑ j ∈ Finset.range n, Real.exp (-(c * j)) ≤ 1 + 1 / c := by
  have hr : ∀ j : ℕ, Real.exp (-(c * j)) = (Real.exp (-c)) ^ j := by
    intro j
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [hr]
  set r : ℝ := Real.exp (-c) with hrdef
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hrdef, Real.exp_lt_one_iff]
    linarith
  have hrc : r ≤ 1 / (1 + c) := by
    have h := Real.add_one_le_exp c
    have h1 : (0 : ℝ) < 1 + c := by linarith
    rw [hrdef, Real.exp_neg, one_div]
    exact inv_anti₀ h1 (by linarith)
  have hgeom : ∑ j ∈ Finset.range n, r ^ j ≤ 1 / (1 - r) := by
    have hpos : (0 : ℝ) < 1 - r := by linarith
    have heq : ∑ j ∈ Finset.range n, r ^ j = (1 - r ^ n) / (1 - r) := by
      rw [geom_sum_eq (by linarith : r ≠ 1),
        show r ^ n - 1 = -(1 - r ^ n) by ring, show r - 1 = -(1 - r) by ring, neg_div_neg_eq]
    rw [heq]
    exact div_le_div_of_nonneg_right (by nlinarith [pow_nonneg hr0.le n]) hpos.le
  have hden : c / (1 + c) ≤ 1 - r := by
    have h1 : (0 : ℝ) < 1 + c := by linarith
    rw [div_le_iff₀ h1]
    have hr2 : r * (1 + c) ≤ 1 := by
      rw [← le_div_iff₀ h1]
      simpa using hrc
    nlinarith [hr2]
  have hfin : 1 / (1 - r) ≤ 1 + 1 / c := by
    have hpos : (0 : ℝ) < 1 - r := by linarith
    have hcpos : (0 : ℝ) < c / (1 + c) := by positivity
    calc 1 / (1 - r) ≤ 1 / (c / (1 + c)) := by
          exact one_div_le_one_div_of_le hcpos hden
      _ = (1 + c) / c := by rw [one_div_div]
      _ = 1 + 1 / c := by field_simp; ring
  linarith

/-- **The small-prime bound.**  Any set of primes `≤ B` carries reciprocal mass at most
`log log B + mertensBound`.  In the assembly this absorbs every window below the cutoff
height `A₁`, with `B = exp(A₁ + 1)`, so the cost is `log(A₁+1) + O(1) ≈ log log|t|`. -/
theorem small_prime_mass_le {B : ℕ} (hB : 2 ≤ B) {G : Finset ℕ}
    (hG : ∀ p ∈ G, p.Prime ∧ p ≤ B) :
    ∑ p ∈ G, (p : ℝ)⁻¹
      ≤ Real.log (Real.log B) + Erdos67b.PrimeEstimates.mertensBound := by
  have hsub : G ⊆ Erdos67b.primesUpTo B := fun p hp => Erdos67b.mem_primesUpTo.2 (hG p hp)
  have h1 : ∑ p ∈ G, (p : ℝ)⁻¹ ≤ ∑ p ∈ Erdos67b.primesUpTo B, (p : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have h2 : ∑ p ∈ Erdos67b.primesUpTo B, (p : ℝ)⁻¹
      = Erdos67b.PrimeEstimates.primeReciprocals B := by
    rw [primesUpTo_eq_primesLE]
    rfl
  have h3 := abs_le.1 (Erdos67b.PrimeEstimates.abs_primeReciprocals_sub_log_log_le hB)
  rw [h2] at h1
  linarith [h3.2]

/-! ## The block form: an arbitrary interval of `log p` of length `≤ 1`

`resonant_window_mass_le` takes the window length to be `2δ/|t|`, which is `≤ 1` only when
`2δ ≤ |t|`.  For `|t| < 2δ` the resonance windows are multiplicatively WIDE, Brun–Titchmarsh
applied to the whole window is exponentially lossy (`4(e^ℓ − 1)/a` versus the truth
`log(1 + ℓ/a)`), and the dependency's Mertens carries a flat error per window which the
`≈ δ·log Y` windows of that range cannot afford.

The fix is to cut every window into unit pieces in `log p` and apply Brun–Titchmarsh to each:
the pieces are then always narrow, and their Brun–Titchmarsh errors are spaced `≥ 1` apart in
height, so they sum geometrically with NO factor of `|t|`. -/

/-- **The unit-block mass.**  Primes in an interval `log p ∈ (a, a+ℓ)` with `a ≥ log 2` and
`0 < ℓ ≤ 1` carry reciprocal mass at most `8ℓ/a + 10⁵·exp(−a/8)`. -/
theorem interval_mass_le {a l : ℝ} (ha : Real.log 2 ≤ a) (hl0 : 0 < l) (hl1 : l ≤ 1)
    {G : Finset ℕ} (hGp : ∀ p ∈ G, p.Prime)
    (hGw : ∀ p ∈ G, a < Real.log p ∧ Real.log p < a + l) :
    ∑ p ∈ G, (p : ℝ)⁻¹ ≤ 8 * l / a + 100000 * Real.exp (-(a / 8)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hapos : (0 : ℝ) < a := by linarith
  set w : ℝ := Real.exp l - 1 with hw
  have hw0 : 0 < w := by
    rw [hw, sub_pos]
    linarith [Real.add_one_le_exp l]
  have hw2 : w ≤ 2 * l := exp_sub_one_le_two_mul hl0.le hl1
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
    · have hlt : (p : ℝ) < Real.exp (a + l) := by
        rw [← Real.exp_log hppos]
        exact Real.exp_lt_exp.2 h2
      have heq : Real.exp (a + l) = P * (1 + w) := by
        rw [hP, hw, Real.exp_add]; ring
      linarith [heq ▸ hlt]
  have hmain := short_interval_mass_le hP2 hw0 hG
  rw [hlogP] at hmain
  refine le_trans hmain ?_
  have herr : 6 * (1 + a) ^ 3 / Real.sqrt P ≤ 100000 * Real.exp (-(a / 8)) := by
    rw [hP]
    exact window_err_le hapos.le
  have h1 : 4 * w / a ≤ 8 * l / a := by
    refine div_le_div_of_nonneg_right ?_ hapos.le
    linarith
  linarith
