import NormalNumbers.PairDecoupleDigits

/-!
# The crux, named: a multi-point Elliott correlation

`PairDecoupleVdC.lean` reduced the ratified target to `ShiftCorrSmall` — the shifted
decorrelation of the large-prime phase along every progression to a small-prime modulus.
`PairDecoupleDigits.lean` identified the `b`-adic digit form: the truncated pair phase is a
product of `2K` root-of-unity powers of `ω`.

This file closes the reduction.  It shows that the truncation error is *uniformly* negligible
along a progression as soon as the depth `K = K(R)` grows (`AdmissibleTrunc`), hence

`ShiftCorrSmall b p q t  ↔  MultiElliott b p q t`,

where `MultiElliott` is exactly the statement that the `2K`-point correlation
`∏_{k<K} ζ_k^{ω(p·N_i+1+k)} · conj(ζ_k^{ω(q·N_i+1+k)})` — taken at the two shifted arguments
`N_i = c + (i+j)Q` and `c + (i+j')Q` of a progression, so `4K` linear forms in total — has mean
`o(R)`.  That is **Elliott's conjecture for a growing number of points**: the case `K = 1`
(two points, i.e. `f(p n+1) conj f(q n+1)`) is a theorem of Tao (Forum of Mathematics Pi, 2016)
in logarithmic average; no case with `K → ∞` is known, even logarithmically.

The truncation depth needed is small: with the sharp mean `Σ_{m ≤ X} ω(m) = X log log X + O(X)`
one may take `K(R) ≍ log_b log log R`; with the crude pointwise `ω(m) ≤ log₂ m` used here (via
`omegaTail_le_log`) `K(R) = R` already works, and `AdmissibleTrunc` is stated so that *any*
faster-than-logarithmic depth qualifies.  The equivalence is therefore not an artefact of the
depth: the crux IS the multi-point correlation.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-! ### The phase is globally Lipschitz -/

/-- `‖e(u) − 1‖ ≤ 4π|u|`, with no smallness hypothesis. -/
lemma norm_phase_sub_one_le' (u : ℝ) : ‖phase u - 1‖ ≤ 4 * Real.pi * |u| := by
  by_cases h : 2 * Real.pi * |u| ≤ 1
  · exact norm_phase_sub_one_le h
  · push_neg at h
    have h2 : ‖phase u - 1‖ ≤ 2 := by
      have hs := norm_sub_le (phase u) 1
      rw [norm_phase] at hs
      simp only [norm_one] at hs
      linarith
    linarith

lemma norm_phase_sub_phase_le (x y : ℝ) : ‖phase x - phase y‖ ≤ 4 * Real.pi * |x - y| := by
  rw [norm_phase_sub_phase]
  exact norm_phase_sub_one_le' _

/-! ### The discarded digits are a rescaled `omegaTail` -/

private lemma digit_shift_eq (b N K k : ℕ) :
    (omegaNat (N + 1 + (k + K)) : ℝ) / (b : ℝ) ^ ((k + K) + 1)
      = ((omegaNat ((N + K) + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)) / (b : ℝ) ^ K := by
  have h1 : N + 1 + (k + K) = (N + K) + 1 + k := by omega
  have h2 : (k + K) + 1 = (k + 1) + K := by omega
  rw [h1, h2, pow_add, ← div_div]

private lemma summable_digit_shift (b : ℕ) (hb : 2 ≤ b) (N K : ℕ) :
    Summable (fun k : ℕ => (omegaNat (N + 1 + (k + K)) : ℝ) / (b : ℝ) ^ ((k + K) + 1)) :=
  ((summable_omegaTail b hb (N + K)).div_const ((b : ℝ) ^ K)).congr
    fun k => (digit_shift_eq b N K k).symm

/-- **The discarded digits are exactly `b^{−K}·omegaTail` at the shifted point.** -/
theorem tsum_digit_shift (b : ℕ) (hb : 2 ≤ b) (N K : ℕ) :
    ∑' k : ℕ, (omegaNat (N + 1 + (k + K)) : ℝ) / (b : ℝ) ^ ((k + K) + 1)
      = omegaTail b (N + K) / (b : ℝ) ^ K := by
  rw [tsum_congr (digit_shift_eq b N K), tsum_div_const, omegaTail]

/-- **The digit truncation error, in closed form.** -/
theorem abs_pairTail_sub_digitTrunc_le_omegaTail (b : ℕ) (hb : 2 ≤ b) (p q K n : ℕ) :
    |pairTail b p q n - digitTrunc b p q K n|
      ≤ (omegaTail b (p * n + K) + omegaTail b (q * n + K)) / (b : ℝ) ^ K := by
  have hA := summable_digit_shift b hb (p * n) K
  have hB := summable_digit_shift b hb (q * n) K
  have hmass : Summable (fun k : ℕ => ((omegaNat (p * n + 1 + (k + K)) : ℝ)
      + omegaNat (q * n + 1 + (k + K))) / (b : ℝ) ^ ((k + K) + 1)) :=
    (hA.add hB).congr fun k => (add_div _ _ _).symm
  refine (norm_pairTail_sub_digitTrunc_le b hb p q K n hmass).trans (le_of_eq ?_)
  rw [tsum_congr (fun k : ℕ => add_div (omegaNat (p * n + 1 + (k + K)) : ℝ)
      (omegaNat (q * n + 1 + (k + K)) : ℝ) ((b : ℝ) ^ ((k + K) + 1))),
    hA.tsum_add hB, tsum_digit_shift b hb (p * n) K, tsum_digit_shift b hb (q * n) K]
  ring

private lemma natLog_two_succ_le (M : ℕ) : Nat.log 2 (M + 1) ≤ M := by
  have h : M + 1 < 2 ^ (M + 1) := Nat.lt_two_pow_self
  have := Nat.log_lt_of_lt_pow (y := M + 1) (b := 2) (x := M + 1) (by omega) h
  omega

lemma omegaTail_le_succ (b : ℕ) (hb : 2 ≤ b) (M : ℕ) : omegaTail b M ≤ (M : ℝ) + 1 := by
  refine (omegaTail_le_log b hb M).trans ?_
  have h : ((Nat.log 2 (M + 1) : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast natLog_two_succ_le M
  linarith

/-- **The truncation error, crudely but uniformly, on an initial segment.** -/
theorem abs_pairTail_sub_digitTrunc_le_crude (b : ℕ) (hb : 2 ≤ b) (p q K n M : ℕ) (hn : n ≤ M) :
    |pairTail b p q n - digitTrunc b p q K n|
      ≤ (((p + q) * M + 2 * K + 2 : ℕ) : ℝ) / (b : ℝ) ^ K := by
  refine (abs_pairTail_sub_digitTrunc_le_omegaTail b hb p q K n).trans ?_
  have hbpos : (0 : ℝ) < (b : ℝ) ^ K := by
    have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    positivity
  rw [div_le_div_iff_of_pos_right hbpos]
  have h1 := omegaTail_le_succ b hb (p * n + K)
  have h2 := omegaTail_le_succ b hb (q * n + K)
  have hpm : (p * n : ℝ) ≤ (p : ℝ) * M := by
    have : ((n : ℕ) : ℝ) ≤ (M : ℕ) := by exact_mod_cast hn
    have hp : (0 : ℝ) ≤ (p : ℝ) := by positivity
    push_cast
    nlinarith
  have hqm : (q * n : ℝ) ≤ (q : ℝ) * M := by
    have : ((n : ℕ) : ℝ) ≤ (M : ℕ) := by exact_mod_cast hn
    have hq : (0 : ℝ) ≤ (q : ℝ) := by positivity
    push_cast
    nlinarith
  push_cast at h1 h2 ⊢
  linarith

/-! ### The small primes cancel out of the shifted difference -/

/-- **The `P`-truncation cancels.**  Both arguments lie in the same class mod `Q = primorialLe P`,
and `truncPairTail` is exactly `Q`-periodic, so the shifted difference of the *remainder* is the
shifted difference of the *full* pair tail.  The cut `P` survives only inside the modulus. -/
theorem shiftPairDiff_eq_pairTail (b P p q c j j' i : ℕ) :
    shiftPairDiff b P p q c j j' i
      = pairTail b p q (c + (i + j) * primorialLe P)
        - pairTail b p q (c + (i + j') * primorialLe P) := by
  rw [shiftPairDiff_eq, truncPairTail_add_mul_primorial, truncPairTail_add_mul_primorial]
  ring

/-! ### The named open hypothesis -/

/-- The `K`-digit truncation of the shifted pair difference along the progression `c mod Q`.
By `phase_digitTrunc` its phase is a product of `4K` root-of-unity powers of `ω`, taken along
`4K` linear forms in `i`. -/
noncomputable def shiftDigitTrunc (b p q Q c j j' K i : ℕ) : ℝ :=
  digitTrunc b p q K (c + (i + j) * Q) - digitTrunc b p q K (c + (i + j') * Q)

/-- A truncation depth is *admissible* when the discarded digits are negligible on `[0, R)`.
`K R = R` qualifies (`admissibleTrunc_id`); so does any `K R ≥ (2+ε) log_b R`, and — with the
sharp mean of `ω` in place of the crude `ω(m) ≤ log₂ m` used here — any
`K R ≥ (1+ε) log_b log log R`. -/
def AdmissibleTrunc (b : ℕ) (K : ℕ → ℕ) : Prop :=
  Tendsto (fun R : ℕ => ((R : ℝ) + (K R : ℝ) + 1) / (b : ℝ) ^ (K R)) atTop (𝓝 0)

/-- **The multi-point correlation at depth `K`.**  Unfolding `shiftDigitTrunc` through
`phase_digitTrunc`, this says: for every small-prime modulus `Q = primorialLe P`, every class `c`
and every pair of distinct shifts `j ≠ j'`,

`(1/R) |Σ_{i<R} ∏_{k<K(R)} ζ_k^{ω(p N_i + 1 + k) − ω(q N_i + 1 + k) − ω(p N'_i + 1 + k)
                                   + ω(q N'_i + 1 + k)}| → 0`,

with `N_i = c + (i+j)Q`, `N'_i = c + (i+j')Q` and `ζ_k = e(t / b^{k+1})`.  That is **Elliott's
conjecture for `4K(R)` linear forms**, for the non-pretentious multiplicative functions `ζ_k^ω`.
The case of ONE form is Selberg–Delange; TWO forms is a theorem of Tao (Forum Math. Pi 4, 2016)
in logarithmic average; `K → ∞` is open, even logarithmically. -/
def MultiElliottAt (b p q : ℕ) (t : ℝ) (K : ℕ → ℕ) : Prop :=
  ∀ P c j j' : ℕ, j ≠ j' →
    Tendsto (fun R : ℕ =>
        ‖∑ i ∈ range R, phase (t * shiftDigitTrunc b p q (primorialLe P) c j j' (K R) i)‖ / R)
      atTop (𝓝 0)

/-- **THE NAMED OPEN INPUT.**  The multi-point Elliott correlation at *some* admissible depth. -/
def MultiElliott (b p q : ℕ) (t : ℝ) : Prop :=
  ∃ K : ℕ → ℕ, AdmissibleTrunc b K ∧ MultiElliottAt b p q t K

/-! ### `K R = R` is admissible -/

lemma admissibleTrunc_id (b : ℕ) (hb : 2 ≤ b) : AdmissibleTrunc b id := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hr0 : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
  have hr1 : (1 : ℝ) / (b : ℝ) < 1 := by
    rw [div_lt_one hb0]; linarith
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) * (1 / (b : ℝ)) ^ n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_lt_one hr0 hr1
  have h2 : Tendsto (fun n : ℕ => ((1 : ℝ) / (b : ℝ)) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have h3 := (h1.const_mul (2 : ℝ)).add h2
  simp only [mul_zero, add_zero] at h3
  refine h3.congr fun R => ?_
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hb0
  simp only [id_eq, div_pow, one_pow]
  field_simp
  ring

/-! ### The comparison -/

private lemma abs_norm_sum_phase_sub_le (t : ℝ) (R : ℕ) (X Y : ℕ → ℝ) (E : ℝ)
    (h : ∀ i ∈ range R, |X i - Y i| ≤ E) :
    |‖∑ i ∈ range R, phase (t * X i)‖ - ‖∑ i ∈ range R, phase (t * Y i)‖|
      ≤ (R : ℝ) * (4 * Real.pi * |t| * E) := by
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ range R, ‖phase (t * X i) - phase (t * Y i)‖
      ≤ ∑ _i ∈ range R, (4 * Real.pi * |t| * E) := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine (norm_phase_sub_phase_le _ _).trans ?_
        have hE : |X i - Y i| ≤ E := h i hi
        rw [show t * X i - t * Y i = t * (X i - Y i) by ring, abs_mul]
        have hmul : |t| * |X i - Y i| ≤ |t| * E := mul_le_mul_of_nonneg_left hE (abs_nonneg t)
        calc 4 * Real.pi * (|t| * |X i - Y i|) ≤ 4 * Real.pi * (|t| * E) :=
              mul_le_mul_of_nonneg_left hmul (by positivity)
          _ = 4 * Real.pi * |t| * E := by ring
    _ = (R : ℝ) * (4 * Real.pi * |t| * E) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The uniform truncation error along `[0, R)` of the progression `c mod primorialLe P`. -/
noncomputable def truncErr (b p q P c j j' : ℕ) (t : ℝ) (K : ℕ → ℕ) (R : ℕ) : ℝ :=
  4 * Real.pi * |t| *
    (2 * (((p + q) * (c + (R + j + j') * primorialLe P) + 2 * K R + 2 : ℕ) : ℝ) / (b : ℝ) ^ K R)

lemma truncErr_nonneg (b p q P c j j' : ℕ) (t : ℝ) (K : ℕ → ℕ) (R : ℕ) (hb : 2 ≤ b) :
    0 ≤ truncErr b p q P c j j' t K R := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have : (0 : ℝ) < (b : ℝ) ^ K R := by positivity
  rw [truncErr]
  positivity

/-- **The digit truncation is uniformly close to the true shifted difference.** -/
theorem abs_shiftCorr_sub_trunc_le (b : ℕ) (hb : 2 ≤ b) (p q : ℕ) (t : ℝ) (K : ℕ → ℕ)
    (P c j j' R : ℕ) :
    |shiftCorr (largeProg b P p q t c) R j j' / R
        - ‖∑ i ∈ range R, phase (t * shiftDigitTrunc b p q (primorialLe P) c j j' (K R) i)‖ / R|
      ≤ truncErr b p q P c j j' t K R := by
  set Q := primorialLe P with hQ
  set M : ℕ := c + (R + j + j') * Q with hM
  set E : ℝ := 2 * (((p + q) * M + 2 * K R + 2 : ℕ) : ℝ) / (b : ℝ) ^ K R with hE
  have hrw : shiftCorr (largeProg b P p q t c) R j j'
      = ‖∑ i ∈ range R, phase (t * (pairTail b p q (c + (i + j) * Q)
          - pairTail b p q (c + (i + j') * Q)))‖ := by
    rw [shiftCorr_largeProg]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [shiftPairDiff_eq_pairTail]
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · simp [hrw, truncErr_nonneg b p q P c j j' t K 0 hb]
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  -- the pointwise bound
  have hpt : ∀ i ∈ range R,
      |(pairTail b p q (c + (i + j) * Q) - pairTail b p q (c + (i + j') * Q))
        - shiftDigitTrunc b p q Q c j j' (K R) i| ≤ E := by
    intro i hi
    have hiR : i < R := Finset.mem_range.mp hi
    have hA : c + (i + j) * Q ≤ M := by
      have : (i + j) * Q ≤ (R + j + j') * Q := Nat.mul_le_mul_right _ (by omega)
      omega
    have hB : c + (i + j') * Q ≤ M := by
      have : (i + j') * Q ≤ (R + j + j') * Q := Nat.mul_le_mul_right _ (by omega)
      omega
    have h1 := abs_pairTail_sub_digitTrunc_le_crude b hb p q (K R) _ M hA
    have h2 := abs_pairTail_sub_digitTrunc_le_crude b hb p q (K R) _ M hB
    rw [shiftDigitTrunc]
    have hsplit : (pairTail b p q (c + (i + j) * Q) - pairTail b p q (c + (i + j') * Q))
        - (digitTrunc b p q (K R) (c + (i + j) * Q) - digitTrunc b p q (K R) (c + (i + j') * Q))
        = (pairTail b p q (c + (i + j) * Q) - digitTrunc b p q (K R) (c + (i + j) * Q))
          - (pairTail b p q (c + (i + j') * Q) - digitTrunc b p q (K R) (c + (i + j') * Q)) := by
      ring
    rw [hsplit]
    refine (abs_sub _ _).trans ?_
    have hEeq : E = (((p + q) * M + 2 * K R + 2 : ℕ) : ℝ) / (b : ℝ) ^ K R
        + (((p + q) * M + 2 * K R + 2 : ℕ) : ℝ) / (b : ℝ) ^ K R := by rw [hE]; ring
    rw [hEeq]
    linarith
  have hmain := abs_norm_sum_phase_sub_le t R
    (fun i => pairTail b p q (c + (i + j) * Q) - pairTail b p q (c + (i + j') * Q))
    (fun i => shiftDigitTrunc b p q Q c j j' (K R) i) E hpt
  rw [hrw, ← sub_div, abs_div, abs_of_pos hRR, div_le_iff₀ hRR]
  refine hmain.trans (le_of_eq ?_)
  rw [truncErr, ← hQ, ← hM, ← hE]
  ring

/-! ### The truncation error vanishes -/

theorem tendsto_truncErr (b : ℕ) (hb : 2 ≤ b) (p q P c j j' : ℕ) (t : ℝ) (K : ℕ → ℕ)
    (hadm : AdmissibleTrunc b K) :
    Tendsto (fun R : ℕ => truncErr b p q P c j j' t K R) atTop (𝓝 0) := by
  have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  set Q : ℕ := primorialLe P with hQdef
  set C : ℕ := (p + q) * (c + (j + j') * Q) + (p + q) * Q + 2 with hC
  have hkey : ∀ R : ℕ, truncErr b p q P c j j' t K R
      ≤ 8 * Real.pi * |t| * (C : ℝ) * (((R : ℝ) + (K R : ℝ) + 1) / (b : ℝ) ^ K R) := by
    intro R
    have hbp : (0 : ℝ) < (b : ℝ) ^ K R := by positivity
    have h1 : (p + q) * Q ≤ C := by rw [hC]; omega
    have h2 : 2 ≤ C := by rw [hC]; omega
    have b3 : (p + q) * c + (p + q) * Q * (j + j') + 2 ≤ C := by
      rw [hC, show (p + q) * (c + (j + j') * Q) = (p + q) * c + (p + q) * Q * (j + j') by ring]
      omega
    have hnat : (p + q) * (c + (R + j + j') * Q) + 2 * K R + 2 ≤ C * (R + K R + 1) :=
      calc (p + q) * (c + (R + j + j') * Q) + 2 * K R + 2
          = (p + q) * Q * R + 2 * K R + ((p + q) * c + (p + q) * Q * (j + j') + 2) := by ring
        _ ≤ C * R + C * K R + C :=
            Nat.add_le_add
              (Nat.add_le_add (Nat.mul_le_mul h1 (le_refl R)) (Nat.mul_le_mul h2 (le_refl (K R)))) b3
        _ = C * (R + K R + 1) := by ring
    have hnum : (((p + q) * (c + (R + j + j') * Q) + 2 * K R + 2 : ℕ) : ℝ)
        ≤ (C : ℝ) * ((R : ℝ) + (K R : ℝ) + 1) := by
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this ⊢
      linarith
    have hfrac : (((p + q) * (c + (R + j + j') * Q) + 2 * K R + 2 : ℕ) : ℝ) / (b : ℝ) ^ K R
        ≤ ((C : ℝ) * ((R : ℝ) + (K R : ℝ) + 1)) / (b : ℝ) ^ K R :=
      (div_le_div_iff_of_pos_right hbp).mpr hnum
    rw [truncErr, ← hQdef]
    calc 4 * Real.pi * |t| *
          (2 * (((p + q) * (c + (R + j + j') * Q) + 2 * K R + 2 : ℕ) : ℝ) / (b : ℝ) ^ K R)
        = (8 * Real.pi * |t|) *
            ((((p + q) * (c + (R + j + j') * Q) + 2 * K R + 2 : ℕ) : ℝ) / (b : ℝ) ^ K R) := by
          ring
      _ ≤ (8 * Real.pi * |t|) * (((C : ℝ) * ((R : ℝ) + (K R : ℝ) + 1)) / (b : ℝ) ^ K R) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = 8 * Real.pi * |t| * (C : ℝ) * (((R : ℝ) + (K R : ℝ) + 1) / (b : ℝ) ^ K R) := by
          ring
  refine squeeze_zero (fun R => truncErr_nonneg b p q P c j j' t K R hb) hkey ?_
  have h := hadm.const_mul (8 * Real.pi * |t| * (C : ℝ))
  simpa using h

/-! ### The equivalence -/

lemma shiftCorr_nonneg (u : ℕ → ℂ) (R j j' : ℕ) : 0 ≤ shiftCorr u R j j' := by
  rw [shiftCorr]; exact norm_nonneg _

/-- **The crux follows from the multi-point correlation.** -/
theorem shiftCorrSmall_of_multiElliott (b : ℕ) (hb : 2 ≤ b) (p q : ℕ) (t : ℝ)
    (h : MultiElliott b p q t) : ShiftCorrSmall b p q t := by
  obtain ⟨K, hadm, hME⟩ := h
  intro P c j j' hjj
  have hg := hME P c j j' hjj
  have herr := tendsto_truncErr b hb p q P c j j' t K hadm
  have hsum : Tendsto (fun R : ℕ =>
      ‖∑ i ∈ range R, phase (t * shiftDigitTrunc b p q (primorialLe P) c j j' (K R) i)‖ / R
        + truncErr b p q P c j j' t K R) atTop (𝓝 0) := by
    simpa using hg.add herr
  refine squeeze_zero (fun R => ?_) (fun R => ?_) hsum
  · exact div_nonneg (shiftCorr_nonneg _ _ _ _) (Nat.cast_nonneg R)
  · have := abs_le.mp (abs_shiftCorr_sub_trunc_le b hb p q t K P c j j' R)
    linarith [this.2]

/-- **The multi-point correlation follows from the crux**, at every admissible depth. -/
theorem multiElliottAt_of_shiftCorrSmall (b : ℕ) (hb : 2 ≤ b) (p q : ℕ) (t : ℝ) (K : ℕ → ℕ)
    (hadm : AdmissibleTrunc b K) (h : ShiftCorrSmall b p q t) : MultiElliottAt b p q t K := by
  intro P c j j' hjj
  have hf := h P c j j' hjj
  have herr := tendsto_truncErr b hb p q P c j j' t K hadm
  have hsum : Tendsto (fun R : ℕ => shiftCorr (largeProg b P p q t c) R j j' / R
      + truncErr b p q P c j j' t K R) atTop (𝓝 0) := by
    simpa using hf.add herr
  refine squeeze_zero (fun R => ?_) (fun R => ?_) hsum
  · exact div_nonneg (norm_nonneg _) (Nat.cast_nonneg R)
  · have := abs_le.mp (abs_shiftCorr_sub_trunc_le b hb p q t K P c j j' R)
    linarith [this.1]

/-- **THE LEAF, AS AN EQUIVALENCE.**  The successor crux of the ratified target is *exactly*
Elliott's conjecture for a growing number of linear forms, for the non-pretentious multiplicative
functions `ζ_k^ω`.  Neither direction loses anything: the digit truncation is a two-sided
approximation. -/
theorem shiftCorrSmall_iff_multiElliott (b : ℕ) (hb : 2 ≤ b) (p q : ℕ) (t : ℝ) :
    ShiftCorrSmall b p q t ↔ MultiElliott b p q t :=
  ⟨fun h => ⟨id, admissibleTrunc_id b hb,
      multiElliottAt_of_shiftCorrSmall b hb p q t id (admissibleTrunc_id b hb) h⟩,
    shiftCorrSmall_of_multiElliott b hb p q t⟩

end NormalNumbers.CastingOut
