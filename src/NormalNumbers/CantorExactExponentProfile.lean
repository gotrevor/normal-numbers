/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorExactExponentStretch

/-!
# The exponent sets the normal profile: `x` is normal to `3ˢt` iff `t > 3^{s(μ₀−1)}`

Ren, 2026-10-06 (`/create`, after the stretch referee).  The stretch points
`x = cantorExpReal μ₀ ω` are normal to every base prime to 3 and to no power of 3; for bases
`b = 3ˢ t` with `s ≥ 1`, `t > 1`, `3 ∤ t`, nothing was claimed
(`CantorExactExponent.not_isNormal_of_three_dvd_of_small` covers only `2 log₃ b < μ₀`).

**Conjecture (frozen here).**  For rational `μ₀ > 2` and almost every `ω`, `x` is normal to base
`b = 3ˢ t` exactly when `t > 3^{s(μ₀−1)}` (`ProfileOK`).  One formula covers all bases: `s = 0`
gives every base prime to 3, and `t = 1` gives no power of 3.  The threshold is power-invariant
(`b ↦ bᵏ` scales `s` and `log t` alike), as normality must be.  It is never attained, because
`3^{s(μ₀−1)}` is an integer prime to 3 only when it is 1.  Examples at `μ₀ ∈ (2, 2.26)`: normal
to 12, 15 and 21, not normal to 6, 18 or 36.  Base 12 switches off at `μ₀ = 1 + log₃ 4 ≈ 2.26`.

**Mechanism: one window, two sides.**  Let the run be `[a, E)`, `E = ⌈μ₀ a⌉`, and write `L = log₃ t`.
* *Not normal* when `μ₀ > 1 + L/s`.  For `j ≥ a/s`, `bʲ P/3^a ∈ ℤ`, so base-`b` digits
  `j ∈ (a/s, E/log₃ b)` are `0`: a zero run of length `≍ a`.  Its block frequency beats
  `b^{−ℓ}` for every `ℓ` (`not_isNormal_of_not_profileOK`, elementary).
* *Normal* when `μ₀ < 1 + L/s`.  The Fourier coefficient of the coin law at `h·bⁿ` sees only the
  ternary places `[sn, (s+L)n]`, where the digits of `h tⁿ` sit.  A run covers that window iff
  `sn ≥ a` and `(s+L)n ≤ μ₀ a`, which is possible iff `μ₀ > 1 + L/s`.  Below the threshold every
  window keeps `≥ a(1 − μ₀ s/(s+L))` free places, linear in `n`, so the Cassels–Schmidt second moment
  (`CantorLiouvilleAll.secondMoment_le_b`, with the orbit of `t` mod `3ᵏ` in place of `b`)
  should go through.  This is `ae_isNormal_of_profileOK` (open node).

So the threshold where the Fourier side breaks is the same threshold where the explicit zero
runs appear.  Known-false sibling: `t = 1` (powers of 3).  There the frequencies' digits are a fixed
word shifted, with no orbit to average over, and the mechanism correctly gives nothing.

Prior art (one search, 2026-10-06): Schmidt (1960) gives sets of normal bases closed under
multiplicative dependence; Becher–Slaman give prescribed simple-normality profiles outside `K`.
We found no profile for points of `K` that depends on the exponent.
-/

open MeasureTheory Filter

namespace NormalNumbers.CantorExactExponentProfile

open CantorLiouville CantorExactExponent CantorExpGeneric Derandomize CantorExactExponentStretch

/-- The profile condition for `b = 3ˢ t` (`s = v₃ b`, `t = b / 3ˢ`): `3^{s(μ₀−1)} < t`. -/
def ProfileOK (μ₀ : ℚ) (b : ℕ) : Prop :=
  (3 : ℝ) ^ ((padicValNat 3 b : ℝ) * ((μ₀ : ℝ) - 1)) < ((b / 3 ^ padicValNat 3 b : ℕ) : ℝ)

/-- Bases prime to 3 always pass. -/
theorem profileOK_of_not_dvd (μ₀ : ℚ) {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) : ProfileOK μ₀ b := by
  unfold ProfileOK
  rw [padicValNat.eq_zero_of_not_dvd h3]
  simp only [CharP.cast_eq_zero, zero_mul, Real.rpow_zero, pow_zero, Nat.div_one]
  exact_mod_cast hb

/-- Powers of 3 never pass (for `μ₀ ≥ 1`). -/
theorem not_profileOK_three_pow (μ₀ : ℚ) (hμ : 1 ≤ μ₀) (s : ℕ) : ¬ ProfileOK μ₀ (3 ^ s) := by
  unfold ProfileOK
  rw [padicValNat.prime_pow (p := 3) s, Nat.div_self (by positivity)]
  push Not
  have : (0 : ℝ) ≤ (s : ℝ) * ((μ₀ : ℝ) - 1) := by
    have : (1 : ℝ) ≤ μ₀ := by exact_mod_cast hμ
    positivity
  simpa using Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) this

/-- **Block lemma.**  On a run, once `3^a ∣ bʲ`, the orbit point `{bʲx}` lies in `[0, b^{−ℓ})`. -/
theorem fract_lt_of_run_block {μ₀ : ℚ} (hμ : 1 < μ₀) (ω : ℕ → Bool) {b s : ℕ} (hb : 2 ≤ b)
    (hs : 3 ^ s ∣ b) {k j ℓ : ℕ} (hj1 : expRunStart μ₀ k ≤ s * j)
    (hj2 : b ^ (j + ℓ + 1) ≤ 3 ^ expRunEnd μ₀ (expRunStart μ₀ k)) :
    Int.fract (cantorExpReal μ₀ ω * (b : ℝ) ^ j) < 1 / (b : ℝ) ^ ℓ := by
  set A := expRunStart μ₀ k
  set T := expRunEnd μ₀ A
  set t := tl (expFree μ₀) ω T
  have hx : cantorExpReal μ₀ ω = (hd (expFree μ₀) ω A : ℝ) / 3 ^ A + t :=
    cantorExpReal_trunc hμ ω k
  have ht0 : 0 ≤ t := tl_nonneg _ _ _
  have ht1 : t ≤ 1 / 3 ^ T := tl_le _ _ _
  obtain ⟨q, hq⟩ : 3 ^ A ∣ b ^ j := by
    refine (pow_dvd_pow 3 hj1).trans ?_
    rw [pow_mul]; exact pow_dvd_pow_of_dvd hs j
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbj : (b : ℝ) ^ j = 3 ^ A * q := by exact_mod_cast hq
  have heq : cantorExpReal μ₀ ω * (b : ℝ) ^ j =
      (((hd (expFree μ₀) ω A * q : ℕ) : ℤ) : ℝ) + t * (b : ℝ) ^ j := by
    rw [hx, add_mul, hbj]; push_cast; field_simp
  have hT : (b : ℝ) ^ (j + ℓ + 1) ≤ 3 ^ T := by exact_mod_cast hj2
  have h3T : (0 : ℝ) < 3 ^ T := by positivity
  have hbl : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
  have hlt : t * (b : ℝ) ^ j < 1 / (b : ℝ) ^ ℓ := by
    have hbj2 : (b : ℝ) ^ j * ((b : ℝ) ^ ℓ * b) ≤ 3 ^ T := by
      rw [← pow_succ, ← pow_add, ← add_assoc]; exact hT
    have hbj0 : (0 : ℝ) ≤ (b : ℝ) ^ j := by positivity
    calc t * (b : ℝ) ^ j ≤ 1 / 3 ^ T * (b : ℝ) ^ j := by gcongr
      _ ≤ 1 / 3 ^ T * (3 ^ T / ((b : ℝ) ^ ℓ * b)) := by
          gcongr; rw [le_div_iff₀ (by positivity)]; exact hbj2
      _ = 1 / ((b : ℝ) ^ ℓ * b) := by field_simp
      _ < 1 / (b : ℝ) ^ ℓ := by
          apply one_div_lt_one_div_of_lt hbl; nlinarith
  have h0 : 0 ≤ t * (b : ℝ) ^ j := by positivity
  rw [heq, Int.fract_intCast_add, Int.fract_eq_self.2 ⟨h0, hlt.trans_le ?_⟩]
  · exact hlt
  · rw [div_le_one hbl]; exact one_le_pow₀ (by linarith)

/-- `3^{s(μ₀−1)}` is never an integer prime to 3 when `s ≥ 1`, `μ₀ > 1`. -/
theorem ne_rpow_of_not_dvd {μ₀ : ℚ} (hμ : 1 < μ₀) {s t : ℕ} (hs : 1 ≤ s) (ht : ¬ 3 ∣ t) :
    (t : ℝ) ≠ (3 : ℝ) ^ ((s : ℝ) * ((μ₀ : ℝ) - 1)) := by
  intro h
  set q := μ₀.den
  have hq : (μ₀ : ℝ) * q = μ₀.num := by exact_mod_cast Rat.mul_den_eq_num μ₀
  have hnum : (q : ℤ) < μ₀.num := by
    have h1 : (1 : ℚ) * q < μ₀ * q := by
      exact mul_lt_mul_of_pos_right hμ (by exact_mod_cast μ₀.den_pos)
    rw [Rat.mul_den_eq_num, one_mul] at h1; exact_mod_cast h1
  set p : ℕ := s * (μ₀.num - q).toNat
  have hp : ((s : ℝ) * ((μ₀ : ℝ) - 1)) * q = (p : ℝ) := by
    have : ((μ₀.num - q).toNat : ℤ) = μ₀.num - q := Int.toNat_of_nonneg (by omega)
    have : (((μ₀.num - q).toNat : ℕ) : ℝ) = (μ₀.num : ℝ) - q := by exact_mod_cast this
    simp only [p]; push_cast; rw [this, ← hq]; ring
  have hpow : (t : ℝ) ^ q = (3 : ℝ) ^ p := by
    rw [h, ← Real.rpow_mul_natCast (by norm_num), hp, Real.rpow_natCast]
  have hN : t ^ q = 3 ^ p := by exact_mod_cast hpow
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (by
    simp only [p]; apply mul_ne_zero (by omega); omega)
  have : 3 ∣ t ^ q := by rw [hN]; exact dvd_pow_self 3 (by omega)
  exact ht (Nat.prime_three.dvd_of_dvd_pow this)

/-- **Not normal past the threshold, for every `ω`.**  Confidence 90%.

English proof.  Let `s = v₃ b ≥ 1` (if `s = 0` then `ProfileOK` holds), `b = 3ˢt`, and
`θ = log₃ b / s`; `¬ ProfileOK` with `t ≠ 3^{s(μ₀−1)}` gives `θ < μ₀`.  Along run `k`
(`a = a_k`, `E = ⌈μ₀ a⌉`), `x = P/3^a + ε` with `0 ≤ ε < 3^{−E}`.  For `j ≥ ⌈a/s⌉`,
`bʲP/3^a ∈ ℤ`, so `{bʲx} = bʲε < b^{j}3^{−E}`, and the base-`b` digit `j + 1` is `0` whenever
`b^{j+1} ≤ 3^E`.  So the digits on `(⌈a/s⌉, ⌊E/log₃ b⌋)` vanish, a run of length
`≥ a(μ₀/log₃ b − 1/s) − 2 = c·N`, `c = 1 − θ/μ₀ > 0`, ending at `N = E/log₃ b`.  For any `ℓ`
with `b^{−ℓ} < c/2`, the block `0^ℓ` then has frequency `≥ c/2` at `N`, infinitely often,
contradicting normality.  The `ℓ = 1` case of this argument is `not_isNormal_of_three_dvd_of_small`. -/
theorem not_isNormal_of_not_profileOK (μ₀ : ℚ) (hμ : 1 < μ₀) (ω : ℕ → Bool) {b : ℕ}
    (hb : 2 ≤ b) (hP : ¬ ProfileOK μ₀ b) : ¬ IsNormal b (cantorExpReal μ₀ ω) := by
  intro hn
  rw [isNormal_iff_equidistributed_orbit b hb] at hn
  by_cases h3 : 3 ∣ b
  swap; · exact hP (profileOK_of_not_dvd μ₀ hb h3)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set s := padicValNat 3 b with hs_def
  set t := b / 3 ^ s with ht_def
  have hs1 : 1 ≤ s := one_le_padicValNat_of_dvd (by omega) h3
  have hsd : 3 ^ s ∣ b := pow_padicValNat_dvd
  have hbt : b = 3 ^ s * t := (Nat.mul_div_cancel' hsd).symm
  have ht3 : ¬ 3 ∣ t := by
    intro h
    have h' : 3 ^ (s + 1) ∣ 3 ^ s * t := by rw [pow_succ]; exact Nat.mul_dvd_mul_left (3 ^ s) h
    rw [← hbt] at h'
    exact pow_succ_padicValNat_not_dvd (by omega) h'
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, mul_zero] at hbt; omega
    · exact h
  have hμR : (1 : ℝ) < μ₀ := by exact_mod_cast hμ
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have htlt : (t : ℝ) < (3 : ℝ) ^ ((s : ℝ) * ((μ₀ : ℝ) - 1)) := by
    unfold ProfileOK at hP; push Not at hP
    exact lt_of_le_of_ne hP (ne_rpow_of_not_dvd hμ hs1 ht3)
  set L := Real.logb 3 b with hL_def
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlb : 0 < Real.log b := Real.log_pos (by linarith)
  have hL0 : 0 < L := Real.logb_pos (by norm_num) (by linarith)
  have hLlt : L < s * μ₀ := by
    have h1 : Real.logb 3 t < (s : ℝ) * ((μ₀ : ℝ) - 1) :=
      (Real.logb_lt_iff_lt_rpow (by norm_num) (by exact_mod_cast htpos)).2 htlt
    have h2 : L = s + Real.logb 3 t := by
      rw [hL_def, hbt]; push_cast
      rw [Real.logb_mul (by positivity) (by exact_mod_cast htpos.ne'), Real.logb_pow,
        Real.logb_self_eq_one (by norm_num), mul_one]
    rw [h2]; nlinarith
  set c := 1 - L / (s * μ₀) with hc_def
  have hsμ : 0 < (s : ℝ) * μ₀ := by positivity
  have hc0 : 0 < c := by rw [hc_def, sub_pos, div_lt_one hsμ]; exact hLlt
  obtain ⟨ℓ, hℓ⟩ := exists_pow_lt_of_lt_one (half_pos hc0)
    (show (1 : ℝ) / b < 1 by rw [div_lt_one (by linarith)]; linarith)
  rw [one_div_pow] at hℓ
  have hbl : (0 : ℝ) < (b : ℝ) ^ ℓ := by positivity
  have hI := hn 0 (1 / (b : ℝ) ^ ℓ) le_rfl (by positivity)
    (by rw [div_le_one hbl]; exact one_le_pow₀ (by linarith))
  rw [sub_zero] at hI
  have hlt : 1 / (b : ℝ) ^ ℓ < 3 * c / 4 := by linarith
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hI.eventually (gt_mem_nhds hlt))
  obtain ⟨K, hK⟩ := exists_nat_gt (L * (4 * (ℓ + 3) / c + N0 + 1))
  set k := K
  set A := expRunStart μ₀ k
  set T := expRunEnd μ₀ A
  set n := Nat.log b (3 ^ T)
  have hkA := lt_expRunStart hμ k
  have hlog : 3 ^ T < b ^ (n + 1) := Nat.lt_pow_succ_log_self (by omega) _
  have hpow : b ^ n ≤ 3 ^ T := Nat.pow_log_le_self b (by positivity)
  have hTn : (T : ℝ) < (n + 1) * L := by
    have h1 : (T : ℝ) * Real.log 3 < (n + 1) * Real.log b := by
      have : ((3 ^ T : ℕ) : ℝ) < ((b ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast hlog
      have := Real.log_lt_log (by positivity) this
      push_cast at this; rw [Real.log_pow, Real.log_pow] at this; push_cast at this; linarith
    rw [hL_def, Real.logb, mul_div_assoc', lt_div_iff₀ hl3]; exact h1
  have hTA : (μ₀ : ℝ) * A ≤ T := expRunEnd_ge_r μ₀ A
  have hkAR : (k : ℝ) < A := by exact_mod_cast hkA
  have hA0 : (0 : ℝ) ≤ A := by positivity
  -- `A / s ≤ (n+1)(1-c)`
  have hAs : (A : ℝ) / s ≤ (n + 1) * (1 - c) := by
    rw [hc_def, sub_sub_cancel, div_le_iff₀ (by linarith)]
    have : (n + 1) * (L / (s * μ₀)) * s = (n + 1) * L / μ₀ := by field_simp
    rw [this, le_div_iff₀ (by linarith)]; nlinarith
  -- `n` is large
  have hnbig : 4 * (ℓ + 3) / c + N0 < n := by
    have : (k : ℝ) < (n + 1) * L := by nlinarith
    have h2 : L * (4 * (ℓ + 3) / c + N0 + 1) < (n + 1) * L := by
      have : (K : ℝ) = k := rfl
      linarith
    nlinarith
  have hnN0 : N0 ≤ n := by
    have : (N0 : ℝ) < n := by
      have : 0 ≤ 4 * (ℓ + 3) / c := by positivity
      linarith
    exact_mod_cast this.le
  have hcn : 4 * (ℓ + 3) < c * n := by
    have : 4 * (ℓ + 3) / c < n := by
      have : (0 : ℝ) ≤ N0 := by positivity
      linarith
    rw [div_lt_iff₀ hc0] at this; linarith
  set J0 := A / s + 1
  have hJ0 : (J0 : ℝ) ≤ A / s + 1 := by
    simp only [J0]; push_cast; gcongr; exact Nat.cast_div_le
  have hvis : n - ℓ - 1 - J0 ≤ visitCount (orbit b (cantorExpReal μ₀ ω)) 0 (1 / (b : ℝ) ^ ℓ) n := by
    unfold visitCount
    have : Finset.Ico J0 (n - ℓ - 1) ⊆ (Finset.range n).filter
        (fun j => orbit b (cantorExpReal μ₀ ω) j ∈ Set.Ico 0 (1 / (b : ℝ) ^ ℓ)) := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ico, orbit]
      refine ⟨by omega, Int.fract_nonneg _, fract_lt_of_run_block (k := k) hμ ω hb hsd ?_ ?_⟩
      · have := Nat.lt_div_mul_add (a := A) (show 0 < s by omega)
        have h2 : s * J0 ≤ s * j := Nat.mul_le_mul_left _ hj.1
        have h3 : s * J0 = A / s * s + s := by rw [mul_add, mul_one, mul_comm]
        omega
      · exact (Nat.pow_le_pow_right (by omega) (by omega)).trans hpow
    simpa using Finset.card_le_card this
  have hcnt : (n : ℝ) - ℓ - 1 - J0 ≤ visitCount (orbit b (cantorExpReal μ₀ ω)) 0 (1 / (b : ℝ) ^ ℓ) n := by
    have h1 : ((n - ℓ - 1 - J0 : ℕ) : ℝ) ≤ visitCount (orbit b (cantorExpReal μ₀ ω)) 0 (1 / (b : ℝ) ^ ℓ) n := by
      exact_mod_cast hvis
    have h2 : (n : ℝ) ≤ ((n - ℓ - 1 - J0 : ℕ) : ℝ) + ℓ + 1 + J0 := by
      have : n ≤ (n - ℓ - 1 - J0) + ℓ + 1 + J0 := by omega
      exact_mod_cast this
    linarith
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℝ) ≤ 4 * (ℓ + 3) / c := by positivity
    have : (0 : ℝ) ≤ N0 := by positivity
    linarith
  have := hN0 n hnN0
  rw [div_lt_iff₀ hnpos] at this
  have hc1 : c ≤ 1 := by
    rw [hc_def]; have : 0 ≤ L / (s * μ₀) := by positivity
    linarith
  nlinarith

/-! ## The crux: what the window sees (2026-10-06 lap 1)

The kickoff's port of `CantorLiouvilleAll.secondMoment_le_b` controls the ternary digits of
`h(bᵈ−1)tᵐ` mod `3ʲ` with `3ʲ ≤ N`, i.e. the *low* `O(log N)` digits, through the orbit of `t`.
For `m` in the **shadow** of a run (`a ≤ sm < E`), the places `[sm, E)` are forced, so the
Fourier coefficient sees only digits of `h(bᵈ−1)tᵐ` at relative positions `≥ E − sm`, which is
linear in `N` for most shadow `m`.  No orbit mod `3ʲ` with `3ʲ ≤ N` reaches them
(`t^{m₀+3^{r−v}i}` moves digit `r` only along steps `3^{r−v} ≫ N`).  The shadow is a positive
fraction of `[0, E/s)` (`shadow_card_ge`), so the trivial bound on it contributes `O(1)` per run
to the Davenport–Erdős–LeVeque sum, which diverges.  The digits that remain controllable are
the *top* ones, set by `{m log₃ t}`; with a power discrepancy bound (`LogDiscrepancy`, from
Baker's theorem) the top `ε log N` digits suffice, and they are free because
`(s+L)m > μ₀ a` below the threshold (`window_covered_imp`). -/

/-- **Window lemma.**  A run `[a, μ₀a]` covers the frequency window `[sm, (s+L)m]` only past
the threshold `μ₀ ≥ 1 + L/s`. -/
theorem window_covered_imp {s m a L μ₀ : ℝ} (hs : 0 < s) (hm : 0 < m) (hL : 0 ≤ L) (ha : 0 < a)
    (h1 : a ≤ s * m) (h2 : (s + L) * m ≤ μ₀ * a) : 1 + L / s ≤ μ₀ := by
  have hμ : 0 ≤ μ₀ := by
    by_contra h; push Not at h; nlinarith
  have : (s + L) * m ≤ μ₀ * (s * m) := h2.trans (mul_le_mul_of_nonneg_left h1 hμ)
  rw [show 1 + L / s = (s + L) / s by field_simp, div_le_iff₀ hs]
  nlinarith

/-- **The shadow is a positive fraction.**  Among `m < E/s` (where the frequencies `bᵐ` reach the
run end), those with `a ≤ sm` (window start inside or past the run start) number at least
`E/s − a/s − 1`; with `E ≥ μ₀ a` this is `≥ (1 − 1/μ₀)·E/s − 1`. -/
theorem shadow_card_ge (s a E : ℕ) (hs : 0 < s) :
    E / s - a / s - 1 ≤ ((Finset.range (E / s)).filter (fun m => a ≤ s * m)).card := by
  have : Finset.Ico (a / s + 1) (E / s) ⊆ (Finset.range (E / s)).filter (fun m => a ≤ s * m) := by
    intro m hm
    simp only [Finset.mem_Ico] at hm
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hm.2, ?_⟩
    have := Nat.lt_div_mul_add (a := a) hs
    have h2 : s * (a / s + 1) ≤ s * m := Nat.mul_le_mul_left _ hm.1
    have h3 : s * (a / s + 1) = a / s * s + s := by rw [mul_add, mul_one, mul_comm]
    omega
  have := Finset.card_le_card this
  simp at this; omega

/-- **Reopen condition: power discrepancy of `{m log₃ t + β}`**, uniformly in the shift `β`. -/
def LogDiscrepancy (t : ℕ) : Prop :=
  ∃ C κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 1 ≤ N → ∀ β u v : ℝ, 0 ≤ u → u ≤ v → v ≤ 1 →
    |(visitCount (fun m => Int.fract (m * Real.logb 3 t + β)) u v N : ℝ) - N * (v - u)| ≤
      C * (N : ℝ) ^ (1 - κ)

/-- **Literature (Baker 1966; Baker–Wüstholz 1993, with Erdős–Turán).**  For `t ≥ 2` prime to 3,
`|q log t − p log 3| ≥ q^{−C}` (effective linear forms in two logarithms), hence a power
discrepancy bound for `{m log₃ t + β}`, uniform in `β` (Erdős–Turán with `H = N^κ`).  Faithful
or weaker: the transcription asks only for some `κ > 0`. -/
def Literature.BakerLogDiscrepancy : Prop :=
  ∀ t : ℕ, 2 ≤ t → ¬ 3 ∣ t → LogDiscrepancy t

/-- Power savings are summable along `CantorLiouville.sched` (`sched j ≥ e^{√j}`). -/
theorem summable_sched_rpow {δ : ℝ} (hδ : 0 < δ) :
    Summable fun j => ((sched j : ℕ) : ℝ) ^ (-δ) := by
  have hB := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (ev_log_le (r := 1 / 2) (ε := δ / 2)
    (by norm_num) (by positivity))
  refine Summable.of_norm_bounded_eventually summable_inv_sq_nat ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hB, eventually_ge_atTop 1] with j hjB hj1
  have hs : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hs.le _), ← exp_neg_two_log j hj1]
  calc (sched j : ℝ) ^ (-δ) ≤ (Real.exp (Real.sqrt j)) ^ (-δ) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) (exp_sqrt_le_sched j hj1) (by linarith)
    _ = Real.exp (-(δ * Real.sqrt j)) := by rw [← Real.exp_mul]; ring_nf
    _ ≤ _ := by
        apply Real.exp_le_exp.2
        rw [Real.sqrt_eq_rpow]; nlinarith

/-! ### Leaves of `secondMoment_le_profile` -/

/-- The top-digit product: `∏_{k<K} |cos(2π·3^{k+y})|`. -/
noncomputable def topProd (K : ℕ) (y : ℝ) : ℝ :=
  ∏ k ∈ Finset.range K, |Real.cos (2 * Real.pi * (3 : ℝ) ^ ((k : ℝ) + y))|

/-- **Top window.**  If the `K` places just below the top digit of `ξ` are free, the
coefficient is bounded by `topProd K` at `{log₃|ξ|}`. -/
theorem bf_le_topProd (free : ℕ → Bool) (M K : ℕ) (ξ : ℝ) (hξ : 1 ≤ |ξ|)
    (hK : K ≤ ⌊Real.logb 3 |ξ|⌋₊)
    (hfree : ∀ k < K, free (⌊Real.logb 3 |ξ|⌋₊ - 1 - k) = true)
    (hM : ⌊Real.logb 3 |ξ|⌋₊ ≤ M) :
    Bf free M ξ ≤ topProd K (Int.fract (Real.logb 3 |ξ|)) := by
  set n := ⌊Real.logb 3 |ξ|⌋₊
  set y := Int.fract (Real.logb 3 |ξ|)
  have hl0 : 0 ≤ Real.logb 3 |ξ| := Real.logb_nonneg (by norm_num) hξ
  have hny : Real.logb 3 |ξ| = n + y := by
    have : ((n : ℤ) : ℝ) = (⌊Real.logb 3 |ξ|⌋ : ℝ) := by
      rw [Int.natCast_floor_eq_floor hl0]
    simp only [y, Int.fract]; push_cast at this; rw [this]; ring
  set S := (Finset.range K).image (fun k => n - 1 - k)
  have hS : S ⊆ (Finset.range M).filter (fun p => free p = true) := by
    intro p hp
    simp only [S, Finset.mem_image, Finset.mem_range] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hfree k hk⟩
  unfold Bf
  rw [← Finset.prod_sdiff hS]
  have h1 : ∏ p ∈ (Finset.range M).filter (fun p => free p = true) \ S,
      |Real.cos (2 * Real.pi * ξ / 3 ^ (p + 1))| ≤ 1 :=
    Finset.prod_le_one (fun _ _ => abs_nonneg _) fun _ _ => Real.abs_cos_le_one _
  have h2 : ∏ p ∈ S, |Real.cos (2 * Real.pi * ξ / 3 ^ (p + 1))| = topProd K y := by
    simp only [S]
    rw [Finset.prod_image]
    · unfold topProd
      refine Finset.prod_congr rfl fun k hk => ?_
      simp only [Finset.mem_range] at hk
      have hp : ((n - 1 - k + 1 : ℕ) : ℝ) = n - k := by
        rw [show n - 1 - k + 1 = n - k by omega, Nat.cast_sub (by omega)]
      have habs : |ξ| = (3 : ℝ) ^ ((n : ℝ) + y) := by
        rw [← hny, Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
      have key : |ξ| / 3 ^ (n - 1 - k + 1) = (3 : ℝ) ^ ((k : ℝ) + y) := by
        rw [← Real.rpow_natCast, hp, habs, ← Real.rpow_sub (by norm_num)]; congr 1; ring
      rcases abs_cases ξ with ⟨h, _⟩ | ⟨h, _⟩
      · rw [mul_div_assoc, ← key, h]
      · rw [mul_div_assoc, ← key, h, neg_div, mul_neg, Real.cos_neg]
    · intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      simp only at hab; omega
  rw [h2]
  have : 0 ≤ topProd K y := Finset.prod_nonneg fun _ _ => abs_nonneg _
  nlinarith [Finset.prod_nonneg (s := (Finset.range M).filter (fun p => free p = true) \ S)
    (f := fun p => |Real.cos (2 * Real.pi * ξ / 3 ^ (p + 1))|) (fun _ _ => abs_nonneg _)]

/-- **Top window of a shadow term.**  If `3^{n_Y} ∣ Ξ + Y` (`n_Y` the top place of `Y`), the
places below `n_Y` see `Ξ` exactly as they see `Y`.  For a pair frequency
`Ξ = h bᵐ⁺ᵈ − h bᵐ` with `Y = h bᵐ` this holds once `n_Y ≤ s(m+d)`: the top digits of the
lower term `h bᵐ` are visible through the difference. -/
theorem bf_le_topProd_of_dvd (free : ℕ → Bool) (M K : ℕ) (Ξ Y : ℤ) (hξ : 1 ≤ |(Y : ℝ)|)
    (hK : K ≤ ⌊Real.logb 3 |(Y : ℝ)|⌋₊)
    (hfree : ∀ k < K, free (⌊Real.logb 3 |(Y : ℝ)|⌋₊ - 1 - k) = true)
    (hM : ⌊Real.logb 3 |(Y : ℝ)|⌋₊ ≤ M)
    (hdvd : (3 : ℤ) ^ ⌊Real.logb 3 |(Y : ℝ)|⌋₊ ∣ Ξ + Y) :
    Bf free M Ξ ≤ topProd K (Int.fract (Real.logb 3 |(Y : ℝ)|)) := by
  set ξ : ℝ := (Y : ℝ) with hξdef
  set n := ⌊Real.logb 3 |ξ|⌋₊
  set y := Int.fract (Real.logb 3 |ξ|)
  have hl0 : 0 ≤ Real.logb 3 |ξ| := Real.logb_nonneg (by norm_num) hξ
  have hny : Real.logb 3 |ξ| = n + y := by
    have : ((n : ℤ) : ℝ) = (⌊Real.logb 3 |ξ|⌋ : ℝ) := by
      rw [Int.natCast_floor_eq_floor hl0]
    simp only [y, Int.fract]; push_cast at this; rw [this]; ring
  set S := (Finset.range K).image (fun k => n - 1 - k)
  have hS : S ⊆ (Finset.range M).filter (fun p => free p = true) := by
    intro p hp
    simp only [S, Finset.mem_image, Finset.mem_range] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hfree k hk⟩
  obtain ⟨j, hj⟩ := hdvd
  have hfac : ∀ p ∈ S, |Real.cos (2 * Real.pi * (Ξ : ℝ) / 3 ^ (p + 1))| =
      |Real.cos (2 * Real.pi * ξ / 3 ^ (p + 1))| := by
    intro p hp
    simp only [S, Finset.mem_image, Finset.mem_range] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    have hΞ : (Ξ : ℝ) = 3 ^ n * j - ξ := by
      have : ((Ξ + Y : ℤ) : ℝ) = ((3 ^ n * j : ℤ) : ℝ) := by rw [hj]
      push_cast at this; simp only [ξ]; linarith
    have he : (3 : ℝ) ^ n = 3 ^ (n - 1 - k + 1) * 3 ^ (k) := by
      rw [← pow_add]; congr 1; omega
    have : 2 * Real.pi * (Ξ : ℝ) / 3 ^ (n - 1 - k + 1) =
        -(2 * Real.pi * ξ / 3 ^ (n - 1 - k + 1)) + ((j * 3 ^ k : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hΞ, he]; push_cast; field_simp; ring
    rw [this, Real.cos_add_int_mul_two_pi, Real.cos_neg]
  unfold Bf
  rw [← Finset.prod_sdiff hS, Finset.prod_congr rfl hfac]
  have h1 : ∏ p ∈ (Finset.range M).filter (fun p => free p = true) \ S,
      |Real.cos (2 * Real.pi * (Ξ : ℝ) / 3 ^ (p + 1))| ≤ 1 :=
    Finset.prod_le_one (fun _ _ => abs_nonneg _) fun _ _ => Real.abs_cos_le_one _
  have h2 : ∏ p ∈ S, |Real.cos (2 * Real.pi * ξ / 3 ^ (p + 1))| = topProd K y := by
    simp only [S]
    rw [Finset.prod_image]
    · unfold topProd
      refine Finset.prod_congr rfl fun k hk => ?_
      simp only [Finset.mem_range] at hk
      have hp : ((n - 1 - k + 1 : ℕ) : ℝ) = n - k := by
        rw [show n - 1 - k + 1 = n - k by omega, Nat.cast_sub (by omega)]
      have habs : |ξ| = (3 : ℝ) ^ ((n : ℝ) + y) := by
        rw [← hny, Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
      have key : |ξ| / 3 ^ (n - 1 - k + 1) = (3 : ℝ) ^ ((k : ℝ) + y) := by
        rw [← Real.rpow_natCast, hp, habs, ← Real.rpow_sub (by norm_num)]; congr 1; ring
      rcases abs_cases ξ with ⟨h, _⟩ | ⟨h, _⟩
      · rw [mul_div_assoc, ← key, h]
      · rw [mul_div_assoc, ← key, h, neg_div, mul_neg, Real.cos_neg]
    · intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      simp only at hab; omega
  rw [h2]
  have : 0 ≤ topProd K y := Finset.prod_nonneg fun _ _ => abs_nonneg _
  nlinarith [Finset.prod_nonneg (s := (Finset.range M).filter (fun p => free p = true) \ S)
    (f := fun p => |Real.cos (2 * Real.pi * (Ξ : ℝ) / 3 ^ (p + 1))|) (fun _ _ => abs_nonneg _)]

theorem bf_mono (free : ℕ → Bool) {M M' : ℕ} (h : M ≤ M') (ξ : ℝ) :
    Bf free M' ξ ≤ Bf free M ξ := by
  unfold Bf
  have hS : (Finset.range M).filter (fun p => free p = true) ⊆
      (Finset.range M').filter (fun p => free p = true) :=
    Finset.filter_subset_filter _ (Finset.range_subset_range.2 h)
  rw [← Finset.prod_sdiff hS]
  have h1 : ∏ p ∈ (Finset.range M').filter (fun p => free p = true) \
      (Finset.range M).filter (fun p => free p = true),
      |Real.cos (2 * Real.pi * ξ / 3 ^ (p + 1))| ≤ 1 :=
    Finset.prod_le_one (fun _ _ => abs_nonneg _) fun _ _ => Real.abs_cos_le_one _
  have h0 : 0 ≤ ∏ p ∈ (Finset.range M).filter (fun p => free p = true),
      |Real.cos (2 * Real.pi * ξ / 3 ^ (p + 1))| := Finset.prod_nonneg fun _ _ => abs_nonneg _
  nlinarith

/-- The all-free Riesz majorant does not depend on the offset. -/
theorem hf_true_eq (v k : ℕ) (u : ℝ) :
    Hf (fun _ => true) v k u = ∏ q ∈ Finset.Ico 1 k, |Real.cos (2 * Real.pi * u / 3 ^ (q + 1))| := by
  unfold Hf
  have : posSet (fun _ => true) v k = (Finset.Ico 1 k).map (addLeftEmbedding v) := by
    ext p
    simp only [posSet, Finset.mem_filter, Finset.mem_range, Finset.mem_map, Finset.mem_Ico,
      addLeftEmbedding_apply, and_true]
    constructor
    · intro hp; exact ⟨p - v, by omega, by omega⟩
    · rintro ⟨q, hq, rfl⟩; omega
  rw [this, Finset.prod_map]
  refine Finset.prod_congr rfl fun q _ => ?_
  simp only [addLeftEmbedding_apply]
  congr 2
  rw [show v + q + 1 = v + (q + 1) by ring, pow_add]
  field_simp

/-- **Free low window.**  If the places `[v+1, v+k)` are free and `v + k ≤ M`, the coefficient at
`3ᵛu` is bounded by the offset-free majorant. -/
theorem bf_le_hf_true (free : ℕ → Bool) {M v k : ℕ} (hM : v + k ≤ M)
    (hfree : ∀ p, v + 1 ≤ p → p < v + k → free p = true) (u : ℝ) :
    Bf free M (3 ^ v * u) ≤ Hf (fun _ => true) 0 k u := by
  refine (bf_mono free hM _).trans ((Bf_le_Hf free v k u).trans (le_of_eq ?_))
  have hpos : posSet free v k = posSet (fun _ => true) v k := by
    ext p; simp only [posSet, Finset.mem_filter, Finset.mem_range, and_true]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, hfree p h2 h1⟩
  have : Hf free v k u = Hf (fun _ => true) v k u := by unfold Hf; rw [hpos]
  rw [this, hf_true_eq, hf_true_eq]

/-- **Orbit sum for the all-free majorant**, base `t` prime to 3. -/
theorem sum_hf_true_le {t : ℕ} (ht : 2 ≤ t) (h3 : ¬ 3 ∣ t) (j c : ℕ) (hc : ¬ 3 ∣ c) (N : ℕ) :
    ∑ m ∈ Finset.range N, Hf (fun _ => true) 0 (j + 1) ((c * t ^ m : ℕ) : ℝ) ≤
      (N + 2 * 3 ^ j) * (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t * (2 / 3 : ℝ) ^ j := by
  have := CantorLiouvilleAll.sum_Hf_le_b (fun _ => true) ht h3 0 j c hc N
  have hcard : (posSet (fun _ => true) 0 (j + 1)).card = j := by
    have : posSet (fun _ => true) 0 (j + 1) = Finset.Ico 1 (j + 1) := by
      ext p; simp [posSet]; omega
    rw [this]; simp
  rwa [hcard] at this

theorem abs_prod_sub_prod_le (s : Finset ℕ) (f g : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k ∧ f k ≤ 1)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1) :
    |∏ k ∈ s, f k - ∏ k ∈ s, g k| ≤ ∑ k ∈ s, |f k - g k| := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hF0 : 0 ≤ ∏ k ∈ s, f k := Finset.prod_nonneg fun k _ => (hf k).1
    have hF1 : ∏ k ∈ s, f k ≤ 1 := Finset.prod_le_one (fun k _ => (hf k).1) fun k _ => (hf k).2
    have hG0 : 0 ≤ ∏ k ∈ s, g k := Finset.prod_nonneg fun k _ => (hg k).1
    have e : f a * ∏ k ∈ s, f k - g a * ∏ k ∈ s, g k =
        (f a - g a) * ∏ k ∈ s, f k + g a * (∏ k ∈ s, f k - ∏ k ∈ s, g k) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hF0]; nlinarith [abs_nonneg (f a - g a)]
    · rw [abs_mul, abs_of_nonneg (hg a).1]; nlinarith [abs_nonneg (∏ k ∈ s, f k - ∏ k ∈ s, g k), (hg a).2]

/-- `F_K(z) = ∏_{k<K} |cos(2π 3^k z)|`. -/
noncomputable def cantorProd (K : ℕ) (z : ℝ) : ℝ :=
  ∏ k ∈ Finset.range K, |Real.cos (2 * Real.pi * (3 ^ k * z))|

theorem cantorProd_lip (K : ℕ) (z z' : ℝ) :
    |cantorProd K z - cantorProd K z'| ≤ Real.pi * 3 ^ K * |z - z'| := by
  unfold cantorProd
  have hb : ∀ x : ℝ, 0 ≤ |Real.cos x| ∧ |Real.cos x| ≤ 1 := fun x => ⟨abs_nonneg _, Real.abs_cos_le_one _⟩
  refine (abs_prod_sub_prod_le _ _ _ (fun k => hb _) (fun k => hb _)).trans ?_
  have hterm : ∀ k ∈ Finset.range K, abs (|Real.cos (2 * Real.pi * (3 ^ k * z))| -
      |Real.cos (2 * Real.pi * (3 ^ k * z'))|) ≤ 2 * Real.pi * 3 ^ k * |z - z'| := by
    intro k _
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ((Real.abs_cos_sub_cos_le _ _).trans (le_of_eq ?_))
    rw [show 2 * Real.pi * (3 ^ k * z) - 2 * Real.pi * (3 ^ k * z') =
      (2 * Real.pi * 3 ^ k) * (z - z') by ring, abs_mul, abs_of_pos (by positivity)]
  refine (Finset.sum_le_sum hterm).trans ?_
  have e : ∑ k ∈ Finset.range K, 2 * Real.pi * 3 ^ k * |z - z'| =
      (∑ k ∈ Finset.range K, (3 : ℝ) ^ k) * (2 * Real.pi * |z - z'|) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  have hgeom : (∑ k ∈ Finset.range K, (3 : ℝ) ^ k) * 2 = 3 ^ K - 1 := by
    have := geom_sum_mul (3 : ℝ) K; norm_num at this; linarith
  have : 0 ≤ Real.pi * |z - z'| := by positivity
  nlinarith

theorem topProd_eq (K : ℕ) (y : ℝ) : topProd K y = cantorProd K ((3 : ℝ) ^ y) := by
  unfold topProd cantorProd
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Real.rpow_add (by norm_num), Real.rpow_natCast]

/-- The window of places `[K+1, 2K]`. -/
def winFree (K : ℕ) (p : ℕ) : Bool := decide (K + 1 ≤ p ∧ p ≤ 2 * K)

theorem posSet_winFree (K : ℕ) :
    posSet (winFree K) 0 (2 * K + 2) = Finset.Icc (K + 1) (2 * K) := by
  ext p; simp only [posSet, winFree, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc,
    decide_eq_true_eq]; omega

theorem cantorProd_grid (K i : ℕ) :
    cantorProd K ((i : ℝ) / 3 ^ (2 * K + 1)) = Hf (winFree K) 0 (2 * K + 2) i := by
  unfold cantorProd Hf
  rw [posSet_winFree]
  refine Finset.prod_nbij' (fun k => 2 * K - k) (fun p => 2 * K - p) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_range, Finset.mem_Icc] at *; omega
  · intro p hp; simp only [Finset.mem_range, Finset.mem_Icc] at *; omega
  · intro k hk; simp only [Finset.mem_range, Finset.mem_Icc] at *; omega
  · intro p hp; simp only [Finset.mem_range, Finset.mem_Icc] at *; omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    congr 2
    have : (3 : ℝ) ^ (2 * K + 1) = 3 ^ k * 3 ^ (2 * K - k + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [pow_zero, one_mul, this]; field_simp

theorem sum_cantorProd_grid (K : ℕ) :
    ∑ i ∈ Finset.range (3 * 3 ^ (2 * K + 1)), cantorProd K ((i : ℝ) / 3 ^ (2 * K + 1)) ≤
      3 * 3 ^ (2 * K + 1) * (2 / 3 : ℝ) ^ K := by
  simp_rw [cantorProd_grid]
  rw [CantorLiouville.sum_range_mul_eq _ 3 (3 ^ (2 * K + 1)), Finset.sum_comm]
  have hc1 : (posSet (winFree K) 0 1).card = 0 := by
    rw [Finset.card_eq_zero]; ext p; simp [posSet]; omega
  have hcK : (posSet (winFree K) 0 (1 + (2 * K + 1))).card = K := by
    rw [show 1 + (2 * K + 1) = 2 * K + 2 by ring, posSet_winFree]; simp; omega
  calc _ ≤ ∑ u ∈ Finset.range 3, (3 : ℝ) ^ (2 * K + 1) * (2 / 3 : ℝ) ^ K := by
        refine Finset.sum_le_sum fun u _ => ?_
        have := CantorLiouvilleAll.residue_sum_from (winFree K) 0 1 le_rfl (2 * K + 1) u
        rw [hc1, hcK, pow_zero, mul_one, show 1 + (2 * K + 1) = 2 * K + 2 by ring] at this
        simpa [pow_one] using this
    _ = _ := by simp; ring

/-- Cell index of `y ∈ [0,1)` on the grid `i/Q`, `Q = 3^{2K+1}`, in the variable `z = 3^y`. -/
theorem cell_bounds (K : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    let Q : ℝ := 3 ^ (2 * K + 1)
    let i := ⌊(3 : ℝ) ^ y * Q⌋₊
    (3 : ℕ) ^ (2 * K + 1) ≤ i ∧ i < 3 * 3 ^ (2 * K + 1) ∧
      (i : ℝ) / Q ≤ (3 : ℝ) ^ y ∧ (3 : ℝ) ^ y - i / Q < 1 / Q := by
  intro Q i
  have hQ : (0 : ℝ) < Q := by positivity
  have hz1 : (1 : ℝ) ≤ (3 : ℝ) ^ y := Real.one_le_rpow (by norm_num) hy0
  have hz3 : (3 : ℝ) ^ y < 3 := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3) hy1
    simpa using this
  have hzQ : 0 ≤ (3 : ℝ) ^ y * Q := by positivity
  have hfl := Nat.floor_le hzQ
  have hlt := Nat.lt_floor_add_one ((3 : ℝ) ^ y * Q)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Nat.le_floor; push_cast; simp only [Q]; nlinarith
  · have : (i : ℝ) < 3 * 3 ^ (2 * K + 1) := by
      calc (i : ℝ) ≤ (3 : ℝ) ^ y * Q := hfl
        _ < 3 * Q := by nlinarith
        _ = _ := rfl
    exact_mod_cast this
  · rw [div_le_iff₀ hQ]; exact hfl
  · rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hQ]; linarith

/-- **Top-window sum from the discrepancy input.**  Proved: sample `z = 3^y` on the grid of mesh
`3^{−(2K+1)}` (Lipschitz error `π 3^K` per unit), count each cell with `LogDiscrepancy`, and sum
the grid values by the Riesz residue sum (`sum_cantorProd_grid`). -/
theorem sum_topProd_le_of {t : ℕ} (C κ : ℝ) (hC : ∀ N : ℕ, 1 ≤ N → ∀ β u v : ℝ, 0 ≤ u → u ≤ v →
    v ≤ 1 → |(visitCount (fun m => Int.fract (m * Real.logb 3 t + β)) u v N : ℝ) - N * (v - u)| ≤
      C * (N : ℝ) ^ (1 - κ)) (N : ℕ) (hN : 1 ≤ N) (K : ℕ) (β : ℝ) :
    ∑ m ∈ Finset.range N, topProd K (Int.fract (m * Real.logb 3 t + β)) ≤
      3 * N * (2 / 3 : ℝ) ^ K + 4 * N * (1 / 3 : ℝ) ^ K + 9 * |C| * 9 ^ K * (N : ℝ) ^ (1 - κ) := by
  set y : ℕ → ℝ := fun m => Int.fract (m * Real.logb 3 t + β)
  set Q : ℝ := 3 ^ (2 * K + 1)
  set Qn : ℕ := 3 ^ (2 * K + 1)
  have hQ : (0 : ℝ) < Q := by positivity
  have hQn : (Qn : ℝ) = Q := by simp [Qn, Q]
  set idx : ℕ → ℕ := fun m => ⌊(3 : ℝ) ^ y m * Q⌋₊
  have hcell := fun m : ℕ => cell_bounds K (Int.fract_nonneg (m * Real.logb 3 t + β))
    (Int.fract_lt_one (m * Real.logb 3 t + β))
  have hpt : ∀ m, topProd K (y m) ≤ cantorProd K ((idx m : ℝ) / Q) + Real.pi * 3 ^ K / Q := by
    intro m
    obtain ⟨-, -, h1, h2⟩ := hcell m
    rw [topProd_eq]
    have hl := cantorProd_lip K ((3 : ℝ) ^ y m) ((idx m : ℝ) / Q)
    have : |(3 : ℝ) ^ y m - (idx m : ℝ) / Q| ≤ 1 / Q := by
      rw [abs_of_nonneg (by linarith)]; exact h2.le
    have : Real.pi * 3 ^ K * |(3 : ℝ) ^ y m - (idx m : ℝ) / Q| ≤ Real.pi * 3 ^ K / Q := by
      calc _ ≤ Real.pi * 3 ^ K * (1 / Q) := by gcongr
        _ = _ := by ring
    have := (abs_le.1 hl).2
    linarith
  have hcount : ∀ i ∈ Finset.range (3 * Qn),
      (((Finset.range N).filter (fun m => idx m = i)).card : ℝ) ≤ N / Q + |C| * (N : ℝ) ^ (1 - κ) := by
    intro i _
    by_cases hi : Qn ≤ i ∧ i < 3 * Qn
    swap
    · have : (Finset.range N).filter (fun m => idx m = i) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro m _ hm
        obtain ⟨h1, h2, -, -⟩ := hcell m
        exact hi ⟨hm ▸ h1, hm ▸ h2⟩
      rw [this]; simp; positivity
    have hiR : (1 : ℝ) ≤ i := by
      have : 1 ≤ i := le_trans (Nat.one_le_pow _ _ (by norm_num)) hi.1
      exact_mod_cast this
    set u := Real.logb 3 ((i : ℝ) / Q)
    set v := Real.logb 3 (((i : ℝ) + 1) / Q)
    have hiQ : Q ≤ i := by rw [← hQn]; exact_mod_cast hi.1
    have hi3 : (i : ℝ) + 1 ≤ 3 * Q := by
      rw [← hQn]; have : i + 1 ≤ 3 * Qn := hi.2; exact_mod_cast this
    have hu0 : 0 ≤ u := Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hQ]; linarith)
    have huv : u ≤ v := Real.logb_le_logb_of_le (by norm_num) (by positivity) (by gcongr; linarith)
    have hv1 : v ≤ 1 := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_one, div_le_iff₀ hQ]
      linarith
    have hsub : (Finset.range N).filter (fun m => idx m = i) ⊆
        (Finset.range N).filter (fun m => y m ∈ Set.Ico u v) := by
      intro m hm
      simp only [Finset.mem_filter] at hm ⊢
      refine ⟨hm.1, ?_, ?_⟩
      · obtain ⟨-, -, h1, -⟩ := hcell m
        have h1' : (i : ℝ) / Q ≤ (3 : ℝ) ^ y m := by rw [← hm.2]; exact h1
        rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity)]; exact h1'
      · obtain ⟨-, -, -, h2⟩ := hcell m
        have h2' : (3 : ℝ) ^ y m < ((i : ℝ) + 1) / Q := by
          rw [add_div, ← hm.2]; linarith
        rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity)]; exact h2'
    have hvc := hC N hN β u v hu0 huv hv1
    have hcard : (((Finset.range N).filter (fun m => idx m = i)).card : ℝ) ≤
        visitCount y u v N := by exact_mod_cast Finset.card_le_card hsub
    have hvu : v - u ≤ 1 / Q := by
      have e : v - u = Real.log (((i : ℝ) + 1) / i) / Real.log 3 := by
        simp only [u, v, Real.logb]
        rw [← sub_div, ← Real.log_div (by positivity) (by positivity)]
        congr 1; field_simp
      rw [e, div_le_iff₀ (Real.log_pos (by norm_num))]
      have h1 : Real.log (((i : ℝ) + 1) / i) ≤ ((i : ℝ) + 1) / i - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : ((i : ℝ) + 1) / i - 1 = 1 / i := by field_simp; ring
      have h3 : (1 : ℝ) / i ≤ 1 / Q := one_div_le_one_div_of_le hQ hiQ
      have h4 : (1 : ℝ) < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        linarith
      have h5 : (0 : ℝ) ≤ 1 / Q := by positivity
      nlinarith
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have := (abs_le.1 hvc).2
    have hCN : C * (N : ℝ) ^ (1 - κ) ≤ |C| * (N : ℝ) ^ (1 - κ) := by
      gcongr; exact le_abs_self C
    calc _ ≤ (visitCount y u v N : ℝ) := hcard
      _ ≤ N * (v - u) + C * (N : ℝ) ^ (1 - κ) := by linarith
      _ ≤ N * (1 / Q) + |C| * (N : ℝ) ^ (1 - κ) := by gcongr
      _ = _ := by ring
  have hmaps : ∀ m ∈ Finset.range N, idx m ∈ Finset.range (3 * Qn) := by
    intro m _; simp only [Finset.mem_range]; exact (hcell m).2.1
  have hgrid := sum_cantorProd_grid K
  have hF0 : ∀ i, 0 ≤ cantorProd K ((i : ℝ) / Q) := fun i => Finset.prod_nonneg fun _ _ => abs_nonneg _
  have hsum1 : ∑ m ∈ Finset.range N, cantorProd K ((idx m : ℝ) / Q) ≤
      ∑ i ∈ Finset.range (3 * Qn), cantorProd K ((i : ℝ) / Q) * (N / Q + |C| * (N : ℝ) ^ (1 - κ)) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_le_sum fun i hi => ?_
    have : ∑ m ∈ (Finset.range N).filter (fun m => idx m = i), cantorProd K ((idx m : ℝ) / Q) =
        ((Finset.range N).filter (fun m => idx m = i)).card * cantorProd K ((i : ℝ) / Q) := by
      rw [Finset.sum_congr rfl (g := fun _ => cantorProd K ((i : ℝ) / Q)), Finset.sum_const,
        nsmul_eq_mul]
      intro m hm; simp only [Finset.mem_filter] at hm; rw [hm.2]
    rw [this, mul_comm]
    exact mul_le_mul_of_nonneg_left (hcount i hi) (hF0 i)
  have hgrid' : ∑ i ∈ Finset.range (3 * Qn), cantorProd K ((i : ℝ) / Q) ≤ 3 * Q * (2 / 3 : ℝ) ^ K := by
    simpa [Qn, Q] using hgrid
  have hB0 : (0 : ℝ) ≤ N / Q + |C| * (N : ℝ) ^ (1 - κ) := by positivity
  rw [← Finset.sum_mul] at hsum1
  have hsum2 := hsum1.trans (mul_le_mul_of_nonneg_right hgrid' hB0)
  have hpts : ∑ m ∈ Finset.range N, topProd K (y m) ≤
      ∑ m ∈ Finset.range N, cantorProd K ((idx m : ℝ) / Q) + N * (Real.pi * 3 ^ K / Q) := by
    refine (Finset.sum_le_sum fun m _ => hpt m).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib]; simp
  have hQe : Q = 3 * 9 ^ K := by simp only [Q]; rw [pow_succ, pow_mul]; norm_num; ring
  have h1 : 3 * Q * (2 / 3 : ℝ) ^ K * (N / Q) = 3 * N * (2 / 3 : ℝ) ^ K := by field_simp
  have h2 : N * (Real.pi * 3 ^ K / Q) ≤ 4 * N * (1 / 3 : ℝ) ^ K := by
    rw [hQe, show (9 : ℝ) ^ K = 3 ^ K * 3 ^ K by rw [← mul_pow]; norm_num]
    have : Real.pi * 3 ^ K / (3 * (3 ^ K * 3 ^ K)) = Real.pi / 3 * (1 / 3 : ℝ) ^ K := by
      field_simp; rw [← mul_pow]; norm_num
    rw [this]
    have := Real.pi_lt_four
    have : (0 : ℝ) ≤ N * (1 / 3 : ℝ) ^ K := by positivity
    nlinarith
  have h3 : 3 * Q * (2 / 3 : ℝ) ^ K * (|C| * (N : ℝ) ^ (1 - κ)) ≤ 9 * |C| * 9 ^ K * (N : ℝ) ^ (1 - κ) := by
    rw [hQe]
    have : (2 / 3 : ℝ) ^ K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have : 0 ≤ |C| * (N : ℝ) ^ (1 - κ) * 9 ^ K := by positivity
    nlinarith
  calc _ ≤ _ := hpts
    _ ≤ 3 * Q * (2 / 3 : ℝ) ^ K * (N / Q + |C| * (N : ℝ) ^ (1 - κ)) + N * (Real.pi * 3 ^ K / Q) := by
        linarith
    _ ≤ _ := by rw [mul_add, h1]; linarith

theorem sum_topProd_le {t : ℕ} (hD : LogDiscrepancy t) : ∃ C κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 1 ≤ N →
    ∀ (K : ℕ) (β : ℝ), ∑ m ∈ Finset.range N, topProd K (Int.fract (m * Real.logb 3 t + β)) ≤
      3 * N * (2 / 3 : ℝ) ^ K + 4 * N * (1 / 3 : ℝ) ^ K + C * 9 ^ K * (N : ℝ) ^ (1 - κ) := by
  obtain ⟨C, κ, hκ, hC⟩ := hD
  exact ⟨9 * |C|, κ, hκ, sum_topProd_le_of C κ hC⟩

set_option maxHeartbeats 2000000 in
/-- **Pair classification.**  Below the threshold, for `m ≥ A·W + B` every pair `(m, d)` has a
free window of length `W`: the low window `[v+1, v+W)` (`v ≈ sm`), or the top window of
`Y = h bᵐ` (when `n_Y ≤ s(m+d)`), or the top window of `ξ = h bᵐ(bᵈ−1)`.  The last two lie in
the gap after the run that hits the low window. -/
theorem pair_classify_expl {μ₀ : ℚ} (hμ : 2 < μ₀) {s : ℕ} (hs : 1 ≤ s) {L H : ℝ}
    (hL : (s : ℝ) * (μ₀ - 1) < L) (hH : 0 ≤ H) :
    ∀ W m d v nY nξ : ℕ, ⌈((μ₀ : ℝ) + 1) / (s + L - μ₀ * s)⌉₊ * W +
        (expRunEnd μ₀ (expRunStart μ₀ ⌈((s + L) ^ 2 / s + ((s + L) * H / s + H)) / s⌉₊) +
          ⌈((μ₀ : ℝ) * H + 4) / (s + L - μ₀ * s)⌉₊ + 1) ≤ m →
      (s * m : ℝ) ≤ v → (v : ℝ) ≤ s * m + H →
      (s + L) * m - 1 ≤ nY → (nY : ℝ) ≤ (s + L) * m + H →
      (s + L) * (m + d) - 2 ≤ nξ → (nξ : ℝ) ≤ (s + L) * (m + d) + H →
      (∀ p, v + 1 ≤ p → p < v + W → expFree μ₀ p = true) ∨
      (W ≤ nY ∧ nY ≤ s * (m + d) ∧ ∀ k < W, expFree μ₀ (nY - 1 - k) = true) ∨
      (W ≤ nξ ∧ ∀ k < W, expFree μ₀ (nξ - 1 - k) = true) := by
  have hμ1 : (1 : ℚ) < μ₀ := by linarith
  have hμR : (2 : ℝ) < μ₀ := by exact_mod_cast hμ
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  set g : ℝ := s + L - μ₀ * s
  have hg : 0 < g := by simp only [g]; nlinarith
  have hL0 : 0 ≤ L := by nlinarith
  set c1 : ℝ := (s + L) * H / s + H
  set k1 : ℕ := ⌈((s + L) ^ 2 / s + c1) / s⌉₊
  set Ek1 : ℕ := expRunEnd μ₀ (expRunStart μ₀ k1)
  intro W m d v nY nξ hm hv1 hv2 hY1 hY2 hξ1 hξ2
  by_cases hlow : ∀ p, v + 1 ≤ p → p < v + W → expFree μ₀ p = true
  · exact Or.inl hlow
  right
  push Not at hlow
  obtain ⟨p, hp1, hp2, hpf⟩ := hlow
  have hpf' : expForced μ₀ p = true := by
    unfold expFree at hpf; simpa using hpf
  obtain ⟨k, hk1, hk2⟩ := (expForced_iff hμ1 p).1 hpf'
  set a := expRunStart μ₀ k
  set E := expRunEnd μ₀ a
  -- real facts
  have hmR : ((⌈((μ₀ : ℝ) + 1) / g⌉₊ * W + (Ek1 + ⌈((μ₀ : ℝ) * H + 4) / g⌉₊ + 1) : ℕ) : ℝ) ≤ m := by
    exact_mod_cast hm
  push_cast at hmR
  have hA := Nat.le_ceil (((μ₀ : ℝ) + 1) / g)
  have hB := Nat.le_ceil (((μ₀ : ℝ) * H + 4) / g)
  have hW0 : (0 : ℝ) ≤ W := by positivity
  have hgm : (μ₀ + 1) * W + (μ₀ * H + 4) ≤ g * m := by
    have h1 : (μ₀ + 1 : ℝ) * W ≤ g * (⌈((μ₀ : ℝ) + 1) / g⌉₊ * W) := by
      have := mul_le_mul_of_nonneg_right hA hW0
      rw [div_mul_eq_mul_div, div_le_iff₀ hg] at this; linarith
    have h2 : (μ₀ * H + 4 : ℝ) ≤ g * ⌈((μ₀ : ℝ) * H + 4) / g⌉₊ := by
      rw [div_le_iff₀ hg] at hB; linarith
    have h3 : (0 : ℝ) ≤ Ek1 + 1 := by positivity
    nlinarith
  -- the run index is large
  have hkk : k1 ≤ k := by
    by_contra hc; push Not at hc
    have : E ≤ Ek1 := (expRunEnd_strictMono hμ1).monotone hc.le
    have h0 : (0:ℝ) ≤ ⌈((μ₀ : ℝ) * H + 4) / g⌉₊ := by positivity
    have h00 : (0:ℝ) ≤ ⌈((μ₀ : ℝ) + 1) / g⌉₊ * W := by positivity
    have hEm : (Ek1 : ℝ) ≤ m := by linarith
    have hpR : (p : ℝ) < E := by exact_mod_cast hk2
    have hEk : (E : ℝ) ≤ Ek1 := by exact_mod_cast this
    have : (v : ℝ) + 1 ≤ p := by exact_mod_cast hp1
    nlinarith
  have hpR1 : (v : ℝ) + 1 ≤ p := by exact_mod_cast hp1
  have hpR2 : (p : ℝ) < v + W := by exact_mod_cast hp2
  have haR : (a : ℝ) ≤ p := by exact_mod_cast hk1
  have hER : (p : ℝ) < E := by exact_mod_cast hk2
  have hEup : (E : ℝ) < μ₀ * a + 1 := expRunEnd_lt_r hμ1 a
  have ha0 : (0 : ℝ) ≤ a := by positivity
  -- lower edges clear the run
  have hEW : (E : ℝ) + W + 2 ≤ (s + L) * m - 1 := by
    have hμ0 : (0 : ℝ) ≤ μ₀ := by linarith
    have e1 : (μ₀ : ℝ) * a ≤ μ₀ * p := mul_le_mul_of_nonneg_left haR hμ0
    have e2 : (μ₀ : ℝ) * p ≤ μ₀ * (v + W) := mul_le_mul_of_nonneg_left hpR2.le hμ0
    have e3 : (μ₀ : ℝ) * v ≤ μ₀ * (s * m + H) := mul_le_mul_of_nonneg_left hv2 hμ0
    have : g * m = (s + L) * m - μ₀ * (s * m) := by simp only [g]; ring
    nlinarith
  -- upper edges stay below the next run
  have hnext : (expRunStart μ₀ (k + 1) : ℝ) = (k + 2) * E := by
    rw [expRunStart_succ]; push_cast; ring
  have hm1 : (1 : ℝ) ≤ m := by
    have : 1 ≤ m := by omega
    exact_mod_cast this
  have hk1R : ((s + L) ^ 2 / s + c1) / s ≤ k := by
    have := Nat.le_ceil (((s + L) ^ 2 / s + c1) / s)
    have : (k1 : ℝ) ≤ k := by exact_mod_cast hkk
    linarith
  have hsm : (s : ℝ) * m < E := by linarith
  have hbig : (s + L) ^ 2 / s * m + c1 < (k + 2) * E := by
    have h1 : (s + L) ^ 2 / s + c1 ≤ k * s := by rwa [div_le_iff₀ (by linarith)] at hk1R
    have hc1 : 0 ≤ c1 := by positivity
    have hq : 0 ≤ (s + L) ^ 2 / s := by positivity
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have e1 : ((s + L) ^ 2 / s + c1) * m ≤ k * s * m := mul_le_mul_of_nonneg_right h1 hm0
    have e2 : c1 ≤ c1 * m := le_mul_of_one_le_right hc1 hm1
    have e3 : (k : ℝ) * (s * m) ≤ k * E := mul_le_mul_of_nonneg_left hsm.le hk0
    have hE0 : (0 : ℝ) < E := by linarith [mul_pos (by linarith : (0:ℝ) < s) (by linarith : (0:ℝ) < m)]
    have e4 : ((s + L) ^ 2 / s + c1) * m = (s + L) ^ 2 / s * m + c1 * m := by ring
    have e5 : (k : ℝ) * s * m = k * (s * m) := by ring
    linarith
  have hYup : (nY : ℝ) < (k + 2) * E := by
    have : (s + L) * m ≤ (s + L) ^ 2 / s * m := by
      have : (s + L) ≤ (s + L) ^ 2 / s := by
        rw [le_div_iff₀ (by linarith)]; nlinarith
      nlinarith
    have hc : 0 ≤ (s + L) * H / s := by positivity
    have : H ≤ c1 := by simp only [c1]; linarith
    linarith
  -- freeness of a top window below `n`
  have hwin : ∀ n : ℕ, (E : ℝ) + W ≤ n → (n : ℝ) < (k + 2) * E →
      W ≤ n ∧ ∀ j < W, expFree μ₀ (n - 1 - j) = true := by
    intro n h1 h2
    have hn : E + W ≤ n := by exact_mod_cast h1
    have hn2 : n < expRunStart μ₀ (k + 1) := by
      have : (n : ℝ) < expRunStart μ₀ (k + 1) := by rw [hnext]; exact h2
      exact_mod_cast this
    refine ⟨by omega, fun j hj => expFree_of_gap hμ1 (k := k) (show E ≤ n - 1 - j by omega) (by omega)⟩
  by_cases hd : nY ≤ s * (m + d)
  · left
    obtain ⟨h1, h2⟩ := hwin nY (by linarith) hYup
    exact ⟨h1, hd, h2⟩
  · right
    push Not at hd
    have hdR : (s : ℝ) * (m + d) < nY := by exact_mod_cast hd
    have hξup : (nξ : ℝ) < (k + 2) * E := by
      have hsd : (s : ℝ) * d < L * m + H := by nlinarith
      have hd' : (d : ℝ) < (L * m + H) / s := by rw [lt_div_iff₀ (by linarith)]; linarith
      have : (s + L) * (m + d) + H ≤ (s + L) ^ 2 / s * m + c1 := by
        have e : (s + L) ^ 2 / s * m + c1 = (s + L) * (m + (L * m + H) / s) + H := by
          simp only [c1]; field_simp; ring
        rw [e]
        have : (s + L) * d ≤ (s + L) * ((L * m + H) / s) := by
          apply mul_le_mul_of_nonneg_left hd'.le; linarith
        linarith
      linarith
    have hd0 : (0 : ℝ) ≤ d := by positivity
    exact hwin nξ (by nlinarith) hξup
theorem pair_classify {μ₀ : ℚ} (hμ : 2 < μ₀) {s : ℕ} (hs : 1 ≤ s) {L H : ℝ}
    (hL : (s : ℝ) * (μ₀ - 1) < L) (hH : 0 ≤ H) :
    ∃ A B : ℕ, ∀ W m d v nY nξ : ℕ, A * W + B ≤ m →
      (s * m : ℝ) ≤ v → (v : ℝ) ≤ s * m + H →
      (s + L) * m - 1 ≤ nY → (nY : ℝ) ≤ (s + L) * m + H →
      (s + L) * (m + d) - 2 ≤ nξ → (nξ : ℝ) ≤ (s + L) * (m + d) + H →
      (∀ p, v + 1 ≤ p → p < v + W → expFree μ₀ p = true) ∨
      (W ≤ nY ∧ nY ≤ s * (m + d) ∧ ∀ k < W, expFree μ₀ (nY - 1 - k) = true) ∨
      (W ≤ nξ ∧ ∀ k < W, expFree μ₀ (nξ - 1 - k) = true) :=
  ⟨_, _, pair_classify_expl hμ hs hL hH⟩

/-- The explicit constants of `pair_classify_expl`. -/
noncomputable def pcA (μ₀ : ℚ) (s : ℕ) (L : ℝ) : ℕ := ⌈((μ₀ : ℝ) + 1) / (s + L - μ₀ * s)⌉₊

noncomputable def pcB (μ₀ : ℚ) (s : ℕ) (L H : ℝ) : ℕ :=
  expRunEnd μ₀ (expRunStart μ₀ ⌈((s + L) ^ 2 / s + ((s + L) * H / s + H)) / s⌉₊) +
    ⌈((μ₀ : ℝ) * H + 4) / (s + L - μ₀ * s)⌉₊ + 1

/-- The structure of `b = 3ˢt` under `ProfileOK`. -/
theorem profile_data {μ₀ : ℚ} (hμ : 1 < μ₀) {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b)
    (hP : ProfileOK μ₀ b) :
    1 ≤ padicValNat 3 b ∧ b = 3 ^ padicValNat 3 b * (b / 3 ^ padicValNat 3 b) ∧
      ¬ 3 ∣ b / 3 ^ padicValNat 3 b ∧ 2 ≤ b / 3 ^ padicValNat 3 b ∧
      (padicValNat 3 b : ℝ) * (μ₀ - 1) < Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ) ∧
      Real.logb 3 b = padicValNat 3 b + Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set s := padicValNat 3 b
  set t := b / 3 ^ s
  have hs1 : 1 ≤ s := one_le_padicValNat_of_dvd (by omega) h3
  have hsd : 3 ^ s ∣ b := pow_padicValNat_dvd
  have hbt : b = 3 ^ s * t := (Nat.mul_div_cancel' hsd).symm
  have ht3 : ¬ 3 ∣ t := by
    intro h
    have h' : 3 ^ (s + 1) ∣ 3 ^ s * t := by rw [pow_succ]; exact Nat.mul_dvd_mul_left (3 ^ s) h
    rw [← hbt] at h'
    exact pow_succ_padicValNat_not_dvd (by omega) h'
  have hP' : (3 : ℝ) ^ ((s : ℝ) * ((μ₀ : ℝ) - 1)) < t := hP
  have hμR : (1 : ℝ) < μ₀ := by exact_mod_cast hμ
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have h1 : (1 : ℝ) < (3 : ℝ) ^ ((s : ℝ) * ((μ₀ : ℝ) - 1)) :=
    Real.one_lt_rpow (by norm_num) (by nlinarith)
  have htpos : (0 : ℝ) < t := by linarith
  have ht2 : 2 ≤ t := by
    have : (1 : ℝ) < t := by linarith
    have : 1 < t := by exact_mod_cast this
    omega
  refine ⟨hs1, hbt, ht3, ht2, (Real.lt_logb_iff_rpow_lt (by norm_num) htpos).2 hP', ?_⟩
  conv_lhs => rw [hbt]
  push_cast
  rw [Real.logb_mul (by positivity) htpos.ne', Real.logb_pow, Real.logb_self_eq_one (by norm_num),
    mul_one]

theorem hf_neg (v k : ℕ) (u : ℝ) : Hf (fun _ => true) v k (-u) = Hf (fun _ => true) v k u := by
  unfold Hf
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [mul_neg, mul_neg, neg_div, Real.cos_neg]

set_option maxHeartbeats 4000000 in
/-- **Per-pair bound.**  Every pair coefficient is bounded by the low-window majorant, the two
top-window products, or (for small `m`) by `1`. -/
theorem pair_bound_expl {μ₀ : ℚ} (hμ : 2 < μ₀) {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b)
    (hP : ProfileOK μ₀ b) (h : ℤ) (hh : h ≠ 0) :
    ∀ W N d m : ℕ, 1 ≤ d → d < N → m < N →
      Bf (expFree μ₀) (2 * b * N + ⌈Real.logb 3 |(h : ℝ)|⌉₊ + W + 1)
          (h * ((b : ℝ) ^ d - 1) * (b : ℝ) ^ m) ≤
        Hf (fun _ => true) 0 W
            (((h.natAbs / 3 ^ padicValNat 3 h.natAbs) * (b ^ d - 1) *
              (b / 3 ^ padicValNat 3 b) ^ m : ℕ) : ℝ) +
          topProd W (Int.fract (m * Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ) +
            Real.logb 3 (|(h : ℝ)| * ((b : ℝ) ^ d - 1)))) +
          topProd W (Int.fract (m * Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ) +
            Real.logb 3 |(h : ℝ)|)) +
          (if m < pcA μ₀ (padicValNat 3 b) (Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ)) * W +
            pcB μ₀ (padicValNat 3 b) (Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ))
              (Real.logb 3 |(h : ℝ)|) then 1 else 0) := by
  have hμ1 : (1 : ℚ) < μ₀ := by linarith
  obtain ⟨hs1, hbt, ht3, ht2, hL, hlogb⟩ := profile_data hμ1 hb h3 hP
  set s := padicValNat 3 b
  set t := b / 3 ^ s
  set L := Real.logb 3 (t : ℝ)
  set H := Real.logb 3 |(h : ℝ)|
  have hhR : (1 : ℝ) ≤ |(h : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hh
  have hH0 : 0 ≤ H := Real.logb_nonneg (by norm_num) hhR
  have hAB := pair_classify_expl hμ hs1 (L := L) hL hH0
  set A := pcA μ₀ s L
  set B := pcB μ₀ s L H
  intro W N d m hd hdN hmN
  set e := padicValNat 3 h.natAbs
  set h' := h.natAbs / 3 ^ e
  set c := h' * (b ^ d - 1)
  set M := 2 * b * N + ⌈H⌉₊ + W + 1
  set ξ : ℝ := h * ((b : ℝ) ^ d - 1) * (b : ℝ) ^ m
  -- nonnegativity of the right side
  have hT : ∀ y, 0 ≤ topProd W y := fun y => Finset.prod_nonneg fun _ _ => abs_nonneg _
  have hHf : ∀ u, 0 ≤ Hf (fun _ => true) 0 W u := fun u => Hf_nonneg _ _ _ _
  have hBf1 : Bf (expFree μ₀) M ξ ≤ 1 := Bf_le_one _ _ _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hb3 : (3 : ℝ) ≤ b := by
    have := Nat.le_of_dvd (by omega) h3; exact_mod_cast this
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ t))
  -- `|h| = 3^e h'`
  have hna : h.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hh
  have hhe : h.natAbs = 3 ^ e * h' := (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
  have he : (e : ℝ) ≤ H := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_natCast]
    have : 3 ^ e ≤ h.natAbs := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    rw [← Int.cast_abs, ← Int.natCast_natAbs]; exact_mod_cast this
  have hbpos : (0 : ℝ) < b := by linarith
  have hbm : (0 : ℝ) < (b : ℝ) ^ m := pow_pos hbpos m
  have hhpos : (0 : ℝ) < |(h : ℝ)| := by linarith
  have hbd : (1 : ℝ) ≤ (b : ℝ) ^ d := one_le_pow₀ hb1
  have hbd3 : (3 : ℝ) ≤ (b : ℝ) ^ d := hb3.trans (le_self_pow₀ hb1 (by omega))
  -- logarithms
  have hlb : Real.logb 3 (b : ℝ) = s + L := hlogb
  have hlogbm : ∀ k : ℕ, Real.logb 3 ((b : ℝ) ^ k) = k * (s + L) := by
    intro k; rw [Real.logb_pow, hlb]
  have hbd1 : (0 : ℝ) < (b : ℝ) ^ d - 1 := by linarith
  have hlogd1 : Real.logb 3 ((b : ℝ) ^ d - 1) ≤ d * (s + L) := by
    rw [← hlogbm]; exact Real.logb_le_logb_of_le (by norm_num) hbd1 (by linarith)
  have hlogd2 : d * (s + L) - 1 ≤ Real.logb 3 ((b : ℝ) ^ d - 1) := by
    rw [← hlogbm]
    have : (b : ℝ) ^ d / 3 ≤ (b : ℝ) ^ d - 1 := by linarith
    have h1 := Real.logb_le_logb_of_le (b := 3) (by norm_num) (by positivity) this
    rw [Real.logb_div (by positivity) (by norm_num), Real.logb_self_eq_one (by norm_num)] at h1
    exact h1
  have hξabs : |ξ| = |(h : ℝ)| * ((b : ℝ) ^ d - 1) * (b : ℝ) ^ m := by
    simp only [ξ]; rw [abs_mul, abs_mul, abs_of_pos hbd1, abs_of_pos hbm]
  have hξ1 : 1 ≤ |ξ| := by
    rw [hξabs]
    have h1 : (1 : ℝ) ≤ ((b : ℝ) ^ d - 1) := by linarith
    have h2 : (1 : ℝ) ≤ (b : ℝ) ^ m := one_le_pow₀ hb1
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hhR h1) h2
  have hlogξ : Real.logb 3 |ξ| = (m * L + Real.logb 3 (|(h : ℝ)| * ((b : ℝ) ^ d - 1))) + (s * m : ℕ) := by
    rw [hξabs, Real.logb_mul (mul_pos hhpos hbd1).ne' hbm.ne', hlogbm]; push_cast; ring
  have hlogξ' : Real.logb 3 |ξ| = H + Real.logb 3 ((b : ℝ) ^ d - 1) + m * (s + L) := by
    rw [hξabs, Real.logb_mul (mul_pos hhpos hbd1).ne' hbm.ne', hlogbm,
      Real.logb_mul hhpos.ne' hbd1.ne']
  set Y : ℤ := h * (b : ℤ) ^ m
  have hYabs : |(Y : ℝ)| = |(h : ℝ)| * (b : ℝ) ^ m := by
    simp only [Y]; push_cast; rw [abs_mul, abs_of_pos hbm]
  have hY1 : 1 ≤ |(Y : ℝ)| := by
    rw [hYabs]; exact one_le_mul_of_one_le_of_one_le hhR (one_le_pow₀ hb1)
  have hlogY : Real.logb 3 |(Y : ℝ)| = H + m * (s + L) := by
    rw [hYabs, Real.logb_mul hhpos.ne' hbm.ne', hlogbm]
  set v := s * m + e
  set nY := ⌊Real.logb 3 |(Y : ℝ)|⌋₊
  set nξ := ⌊Real.logb 3 |ξ|⌋₊
  have hmL : (0 : ℝ) ≤ m * (s + L) := by positivity
  have hlY0 : 0 ≤ Real.logb 3 |(Y : ℝ)| := Real.logb_nonneg (by norm_num) hY1
  have hlξ0 : 0 ≤ Real.logb 3 |ξ| := Real.logb_nonneg (by norm_num) hξ1
  have hnY1 : H + m * (s + L) - 1 ≤ (nY : ℝ) := by
    rw [← hlogY]; linarith [Nat.lt_floor_add_one (Real.logb 3 |(Y : ℝ)|)]
  have hnY2 : (nY : ℝ) ≤ H + m * (s + L) := (Nat.floor_le hlY0).trans (le_of_eq hlogY)
  have hnξ1 : H + Real.logb 3 ((b : ℝ) ^ d - 1) + m * (s + L) - 1 ≤ (nξ : ℝ) := by
    rw [← hlogξ']; linarith [Nat.lt_floor_add_one (Real.logb 3 |ξ|)]
  have hnξ2 : (nξ : ℝ) ≤ H + Real.logb 3 ((b : ℝ) ^ d - 1) + m * (s + L) :=
    (Nat.floor_le hlξ0).trans (le_of_eq hlogξ')
  -- the M-bounds
  have hsLb : s + L ≤ (b : ℝ) := by
    rw [← hlb]
    have := Real.logb_le_logb_of_le (b := 3) (by norm_num) (by linarith)
      (show (b : ℝ) ≤ 3 ^ (b : ℝ) by
        have := Real.add_one_le_exp ((b : ℝ) * Real.log 3)
        rw [Real.rpow_def_of_pos (by norm_num)]
        have hl : 1 ≤ Real.log 3 := by
          rw [Real.le_log_iff_exp_le (by norm_num)]
          have : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
          linarith
        have : (b : ℝ) ≤ b * Real.log 3 := le_mul_of_one_le_right hbpos.le hl
        rw [mul_comm (Real.log 3)]; linarith)
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at this
  have hNR : (m : ℝ) + 1 ≤ N ∧ (d : ℝ) + 1 ≤ N := by
    constructor <;> [exact_mod_cast hmN; exact_mod_cast hdN]
  have hHc : H ≤ ⌈H⌉₊ := Nat.le_ceil H
  have hMR : (M : ℝ) = 2 * b * N + ⌈H⌉₊ + W + 1 := by simp only [M]; push_cast; ring
  have hmd : (s + L) * (m + d) ≤ 2 * b * N := by
    have h1 : (m : ℝ) + d ≤ 2 * N := by linarith [hNR.1, hNR.2]
    have h2 : (0 : ℝ) ≤ m + d := by positivity
    have h3 : (0 : ℝ) ≤ s + L := by linarith
    calc (s + L) * (m + d) ≤ b * (m + d) := mul_le_mul_of_nonneg_right hsLb h2
      _ ≤ b * (2 * N) := mul_le_mul_of_nonneg_left h1 hbpos.le
      _ = _ := by ring
  have hnξM : nξ ≤ M := by
    have : (nξ : ℝ) ≤ M := by
      rw [hMR]
      have : (d : ℝ) * (s + L) + m * (s + L) = (s + L) * (m + d) := by ring
      have : (0 : ℝ) ≤ W := by positivity
      linarith
    exact_mod_cast this
  have hnYM : nY ≤ M := by
    have : (nY : ℝ) ≤ M := by
      rw [hMR]
      have : (m : ℝ) * (s + L) ≤ (s + L) * (m + d) := by
        have : (0 : ℝ) ≤ (s + L) * d := by positivity
        nlinarith
      have : (0 : ℝ) ≤ W := by positivity
      linarith
    exact_mod_cast this
  have hvM : v + W ≤ M := by
    have : (v : ℝ) + W ≤ M := by
      rw [hMR]; simp only [v]; push_cast
      have : (s : ℝ) * m ≤ (s + L) * (m + d) := by
        have : (0 : ℝ) ≤ L * m + (s + L) * d := by positivity
        nlinarith
      linarith
    exact_mod_cast this
  by_cases hsmall : m < A * W + B
  · rw [if_pos hsmall]
    have := hT (Int.fract (m * L + Real.logb 3 (|(h : ℝ)| * ((b : ℝ) ^ d - 1))))
    have := hT (Int.fract (m * L + H))
    have := hHf ((c * t ^ m : ℕ) : ℝ)
    linarith
  rw [if_neg hsmall, add_zero]
  push Not at hsmall
  have hcl := hAB W m d v nY nξ hsmall (by simp only [v]; push_cast; linarith)
    (by simp only [v]; push_cast; linarith) (by linarith) (by linarith)
    (by push_cast; linarith) (by push_cast; linarith)
  rcases hcl with hlow | ⟨hWY, hYd, hYfree⟩ | ⟨hWξ, hξfree⟩
  · -- low window
    have hct : |ξ| = 3 ^ v * ((c * t ^ m : ℕ) : ℝ) := by
      rw [hξabs]
      have h1 : |(h : ℝ)| = 3 ^ e * h' := by
        rw [← Int.cast_abs, ← Int.natCast_natAbs, hhe]; push_cast; ring
      have h2 : ((b ^ d - 1 : ℕ) : ℝ) = (b : ℝ) ^ d - 1 := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]; push_cast; ring
      have h4 : (b : ℝ) ^ m = 3 ^ (s * m) * (t : ℝ) ^ m := by
        have : (b : ℝ) = 3 ^ s * t := by exact_mod_cast hbt
        rw [this, mul_pow, pow_mul]
      simp only [c, v]; push_cast; rw [h1, ← h2, h4, pow_add]; push_cast; ring
    have := bf_le_hf_true (expFree μ₀) hvM hlow ((c * t ^ m : ℕ) : ℝ)
    rw [← hct, Bf_abs] at this
    have := hT (Int.fract (m * L + Real.logb 3 (|(h : ℝ)| * ((b : ℝ) ^ d - 1))))
    have := hT (Int.fract (m * L + H))
    linarith
  · -- top of the lower term
    have hdvd : (3 : ℤ) ^ nY ∣ h * ((b : ℤ) ^ d - 1) * (b : ℤ) ^ m + Y := by
      have e1 : h * ((b : ℤ) ^ d - 1) * (b : ℤ) ^ m + Y = h * (b : ℤ) ^ (m + d) := by
        simp only [Y]; ring
      rw [e1]
      refine Dvd.dvd.mul_left ?_ h
      have : (3 : ℤ) ^ s ∣ (b : ℤ) := by exact_mod_cast (pow_padicValNat_dvd : 3 ^ s ∣ b)
      exact (pow_dvd_pow 3 hYd).trans (by rw [pow_mul]; exact pow_dvd_pow_of_dvd this _)
    have := bf_le_topProd_of_dvd (expFree μ₀) M W _ Y hY1 hWY hYfree hnYM hdvd
    have hcast : (((h * ((b : ℤ) ^ d - 1) * (b : ℤ) ^ m : ℤ)) : ℝ) = ξ := by
      simp only [ξ]; push_cast; ring
    rw [hcast] at this
    have hl : Real.logb 3 |(Y : ℝ)| = (m * L + H) + (s * m : ℕ) := by
      rw [hlogY]; push_cast; ring
    rw [hl, Int.fract_add_natCast] at this
    have := hT (Int.fract (m * L + Real.logb 3 (|(h : ℝ)| * ((b : ℝ) ^ d - 1))))
    have := hHf ((c * t ^ m : ℕ) : ℝ)
    linarith
  · -- top of the pair frequency
    have := bf_le_topProd (expFree μ₀) M W ξ hξ1 hWξ hξfree hnξM
    rw [hlogξ, Int.fract_add_natCast] at this
    have := hT (Int.fract (m * L + H))
    have := hHf ((c * t ^ m : ℕ) : ℝ)
    linarith
theorem pair_bound {μ₀ : ℚ} (hμ : 2 < μ₀) {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b)
    (hP : ProfileOK μ₀ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ A B : ℕ, ∀ W N d m : ℕ, 1 ≤ d → d < N → m < N →
      Bf (expFree μ₀) (2 * b * N + ⌈Real.logb 3 |(h : ℝ)|⌉₊ + W + 1)
          (h * ((b : ℝ) ^ d - 1) * (b : ℝ) ^ m) ≤
        Hf (fun _ => true) 0 W
            (((h.natAbs / 3 ^ padicValNat 3 h.natAbs) * (b ^ d - 1) *
              (b / 3 ^ padicValNat 3 b) ^ m : ℕ) : ℝ) +
          topProd W (Int.fract (m * Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ) +
            Real.logb 3 (|(h : ℝ)| * ((b : ℝ) ^ d - 1)))) +
          topProd W (Int.fract (m * Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ) +
            Real.logb 3 |(h : ℝ)|)) +
          (if m < A * W + B then 1 else 0) :=
  ⟨_, _, pair_bound_expl hμ hb h3 hP h hh⟩

/-- Scale bookkeeping: with `r = ⌊log₃ N⌋ / q` and `x = N^{1/q}`, `3^r ≤ x ≤ 3·3^r`. -/
theorem three_pow_div_log_bounds (q N : ℕ) (hq : 1 ≤ q) (hN : 1 ≤ N) :
    (3 : ℝ) ^ (Nat.log 3 N / q) ≤ (N : ℝ) ^ (1 / q : ℝ) ∧
      (N : ℝ) ^ (1 / q : ℝ) ≤ 3 * 3 ^ (Nat.log 3 N / q) := by
  set r := Nat.log 3 N / q
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have key : ∀ k : ℕ, ((3 : ℝ) ^ (k * q)) ^ (1 / q : ℝ) = 3 ^ k := by
    intro k
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    push_cast
    rw [show (k : ℝ) * q * (1 / q) = k by field_simp, Real.rpow_natCast]
  constructor
  · have h1 : 3 ^ (r * q) ≤ N :=
      (Nat.pow_le_pow_right (by norm_num) (Nat.div_mul_le_self _ _)).trans
        (Nat.pow_log_le_self 3 (by omega))
    rw [← key r]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast h1) (by positivity)
  · have h1 : N < 3 ^ ((r + 1) * q) := by
      refine (Nat.lt_pow_succ_log_self (by norm_num) N).trans_le
        (Nat.pow_le_pow_right (by norm_num) ?_)
      have := Nat.lt_div_mul_add (a := Nat.log 3 N) hq
      simp only [r]; nlinarith
    rw [show (3 : ℝ) * 3 ^ r = 3 ^ (r + 1) by ring, ← key (r + 1)]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast h1.le) (by positivity)

set_option maxHeartbeats 4000000 in
/-- **Explicit second moment.**  The proof of `secondMoment_le_profile` with the discrepancy
constants `C, κ`, the scale `q` and the saving `δ` as parameters, stopped before the small-`m`
term is absorbed; `pcA, pcB` are the explicit constants of `pair_classify_expl`. -/
theorem secondMoment_profile_core (μ₀ : ℚ) (hμ : 2 < μ₀) {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b)
    (hP : ProfileOK μ₀ b) (h : ℤ) (hh : h ≠ 0) (C κ : ℝ)
    (hC : ∀ N : ℕ, 1 ≤ N → ∀ β u v : ℝ, 0 ≤ u → u ≤ v → v ≤ 1 →
      |(visitCount (fun m => Int.fract (m * Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ) + β)) u v N
        : ℝ) - N * (v - u)| ≤ C * (N : ℝ) ^ (1 - κ))
    (q : ℕ) (hq7 : 7 ≤ q) (δ : ℝ) (hδ1 : δ ≤ 1 / q) (hδ2 : δ ≤ κ - 6 / q)
    (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, ‖∑ k ∈ Finset.range N, DecayAeNormal.ee (h * (b : ℝ) ^ k * pt (expFree μ₀) ω)‖ ^ 2
        ∂ExplicitSquare.coinMeasure ≤
      N + 2 * N * ((9 * (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb (b / 3 ^ padicValNat 3 b) + 42 +
          162 * |C|) * (N : ℝ) ^ (1 - δ) +
        ((pcA μ₀ (padicValNat 3 b) (Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ)) *
            (3 * (Nat.log 3 N / q) + 1) +
          pcB μ₀ (padicValNat 3 b) (Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ))
            (Real.logb 3 |(h : ℝ)|) : ℕ) : ℝ)) := by
  have hμ1 : (1 : ℚ) < μ₀ := by linarith
  obtain ⟨hs1, hbt, ht3, ht2, -, -⟩ := profile_data hμ1 hb h3 hP
  set s := padicValNat 3 b
  set t := b / 3 ^ s
  have hAB := pair_bound_expl hμ hb h3 hP h hh
  set A := pcA μ₀ s (Real.logb 3 (t : ℕ))
  set B := pcB μ₀ s (Real.logb 3 (t : ℕ)) (Real.logb 3 |(h : ℝ)|)
  have hqR : (7 : ℝ) ≤ q := by exact_mod_cast hq7
  have hq0 : (0 : ℝ) < q := by linarith
  have h1q : 1 / (q : ℝ) ≤ 1 / 7 := by gcongr
  set Tt : ℝ := (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t
  set K : ℝ := 9 * Tt + 42 + 162 * |C|
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set r := Nat.log 3 N / q
  set W := 3 * r + 1
  set x : ℝ := (N : ℝ) ^ (1 / q : ℝ)
  set y : ℝ := (3 : ℝ) ^ r
  obtain ⟨hyx, hxy⟩ := three_pow_div_log_bounds q N (by omega) hN
  have hy1 : 1 ≤ y := one_le_pow₀ (by norm_num)
  have hx0 : 0 < x := by positivity
  have hxpow : ∀ k : ℕ, x ^ k = (N : ℝ) ^ ((k : ℝ) / q) := by
    intro k
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; ring
  set Z : ℝ := (N : ℝ) ^ (1 - δ)
  have hle : ∀ a : ℝ, a ≤ 1 - δ → (N : ℝ) ^ a ≤ Z := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hN1 ha
  have hNx : (N : ℝ) / x ≤ Z := by
    have : (N : ℝ) / x = (N : ℝ) ^ (1 - 1 / q : ℝ) := by
      rw [Real.rpow_sub hN0, Real.rpow_one]
    rw [this]; exact hle _ (by linarith)
  have hx6κ : x ^ 6 * (N : ℝ) ^ (1 - κ) ≤ Z := by
    rw [hxpow, ← Real.rpow_add hN0]; apply hle; push_cast; linarith
  have hx3 : x ^ 3 ≤ N := by
    rw [hxpow]
    calc (N : ℝ) ^ ((3 : ℕ) / (q : ℝ)) ≤ (N : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hN1
          have : (3 : ℝ) / q = 3 * (1 / q) := by ring
          push_cast; linarith
      _ = N := Real.rpow_one _
  have hP3 : (2 / 3 : ℝ) ^ (3 * r) ≤ 3 / x := by
    have h1 : (2 / 3 : ℝ) ^ (3 * r) ≤ 1 / y := by
      rw [pow_mul, one_div, ← inv_pow]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) r
    calc _ ≤ 1 / y := h1
      _ ≤ 3 / x := by rw [div_le_div_iff₀ (by linarith) hx0]; linarith
  have hPW : (2 / 3 : ℝ) ^ W ≤ 3 / x :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : 3 * r ≤ W)).trans hP3
  have hQW : (1 / 3 : ℝ) ^ W ≤ 3 / x :=
    (pow_le_pow_left₀ (by norm_num) (by norm_num) W).trans hPW
  have h9W : (9 : ℝ) ^ W ≤ 9 * x ^ 6 := by
    have : (9 : ℝ) ^ W = 9 * y ^ 6 := by
      simp only [W, y]; rw [pow_succ, ← pow_mul, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul]; ring
    rw [this]; gcongr
  set M := 2 * b * N + ⌈Real.logb 3 |(h : ℝ)|⌉₊ + W + 1
  set G : ℕ → ℕ → ℝ := fun d m => Bf (expFree μ₀) M (h * ((b : ℝ) ^ d - 1) * (b : ℝ) ^ m)
  have hTN : ∀ β : ℝ, ∑ m ∈ Finset.range N, topProd W (Int.fract (m * Real.logb 3 t + β)) ≤
      (21 + 81 * |C|) * Z := by
    intro β
    refine (sum_topProd_le_of C κ hC N hN W β).trans ?_
    have hN3 : 3 * (N : ℝ) * (2 / 3) ^ W ≤ 9 * Z := by
      calc 3 * (N : ℝ) * (2 / 3) ^ W ≤ 3 * N * (3 / x) := by gcongr
        _ = 9 * (N / x) := by ring
        _ ≤ 9 * Z := by gcongr
    have hN4 : 4 * (N : ℝ) * (1 / 3) ^ W ≤ 12 * Z := by
      calc 4 * (N : ℝ) * (1 / 3) ^ W ≤ 4 * N * (3 / x) := by gcongr
        _ = 12 * (N / x) := by ring
        _ ≤ 12 * Z := by gcongr
    have hCC : 9 * |C| * 9 ^ W * (N : ℝ) ^ (1 - κ) ≤ 81 * |C| * Z := by
      have hNk : (0 : ℝ) ≤ (N : ℝ) ^ (1 - κ) := by positivity
      calc 9 * |C| * 9 ^ W * (N : ℝ) ^ (1 - κ) ≤ 9 * |C| * (9 * x ^ 6) * (N : ℝ) ^ (1 - κ) := by
            gcongr
        _ = 81 * |C| * (x ^ 6 * (N : ℝ) ^ (1 - κ)) := by ring
        _ ≤ 81 * |C| * Z := by gcongr
    linarith
  have hd : ∀ d ∈ Finset.Ico 1 N, ∑ m ∈ Finset.range N, G d m ≤
      K * Z + ((A * W + B : ℕ) : ℝ) := by
    intro d hd
    simp only [Finset.mem_Ico] at hd
    set e := padicValNat 3 h.natAbs
    set h' := h.natAbs / 3 ^ e
    have hc : ¬ 3 ∣ h' * (b ^ d - 1) := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hna : h.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hh
      have hh' : ¬ 3 ∣ h' := by
        intro hd3
        have hhe : h.natAbs = 3 ^ e * h' := (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
        have : 3 ^ (e + 1) ∣ h.natAbs := by
          rw [hhe, pow_succ]; exact Nat.mul_dvd_mul_left _ hd3
        exact pow_succ_padicValNat_not_dvd hna this
      have hbd : ¬ 3 ∣ b ^ d - 1 := by
        have h1 : 3 ∣ b ^ d := dvd_pow h3 (by omega)
        have h2 : 1 ≤ b ^ d := Nat.one_le_pow _ _ (by omega)
        omega
      exact fun h3' => (Nat.Prime.dvd_mul Nat.prime_three).1 h3' |>.elim hh' hbd
    have hS1 := sum_hf_true_le ht2 ht3 (3 * r) (h' * (b ^ d - 1)) hc N
    have hS3 : ∑ m ∈ Finset.range N, (if m < A * W + B then (1 : ℝ) else 0) ≤
        ((A * W + B : ℕ) : ℝ) := by
      rw [Finset.sum_boole]
      have : (Finset.range N).filter (· < A * W + B) ⊆ Finset.range (A * W + B) := by
        intro m; simp
      have := Finset.card_le_card this
      simp only [Finset.card_range] at this
      exact_mod_cast this
    refine (Finset.sum_le_sum fun m hm =>
      hAB W N d m hd.1 hd.2 (Finset.mem_range.1 hm)).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have e1 := hTN (Real.logb 3 (|(h : ℝ)| * ((b : ℝ) ^ d - 1)))
    have e2 := hTN (Real.logb 3 |(h : ℝ)|)
    have hS1' : ∑ m ∈ Finset.range N, Hf (fun _ => true) 0 W
        (((h' * (b ^ d - 1) * t ^ m : ℕ)) : ℝ) ≤ 9 * Tt * Z := by
      refine hS1.trans ?_
      have hTt : 0 ≤ Tt := by positivity
      calc ((N : ℝ) + 2 * 3 ^ (3 * r)) * Tt * (2 / 3) ^ (3 * r) ≤ (3 * N) * Tt * (3 / x) := by
            gcongr
            have hy3 : (3 : ℝ) ^ (3 * r) ≤ x ^ 3 := by
              rw [show (3 : ℝ) ^ (3 * r) = y ^ 3 by simp only [y]; rw [← pow_mul, mul_comm]]
              exact pow_le_pow_left₀ (by positivity) hyx 3
            linarith
        _ = 9 * Tt * (N / x) := by ring
        _ ≤ 9 * Tt * Z := by gcongr
    simp only [K]; nlinarith [abs_nonneg C, hS3]
  have hpair := pair_sum_le (fun n m => Bf (expFree μ₀) M (h * ((b : ℝ) ^ n - (b : ℝ) ^ m))) G
    (fun d m => Bf_nonneg _ _ _) (fun n => Bf_le_one _ _ _)
    (fun n m hmn => le_of_eq (by
      simp only [G]; congr 1
      rw [show (b : ℝ) ^ n = (b : ℝ) ^ (n - m) * (b : ℝ) ^ m by rw [← pow_add]; congr 1; omega]; ring))
    (fun n m hmn => le_of_eq (by
      simp only [G]; rw [← Bf_neg]; congr 1
      rw [show (b : ℝ) ^ m = (b : ℝ) ^ (m - n) * (b : ℝ) ^ n by rw [← pow_add]; congr 1; omega]; ring)) N
  have hI := (CantorLiouvilleAll.secondMoment_expand_b (expFree μ₀) b h M N).trans hpair
  have hX : 0 ≤ K * Z + ((A * W + B : ℕ) : ℝ) := by
    have : 0 ≤ K := by simp only [K]; positivity
    positivity
  have hsum : ∑ d ∈ Finset.Ico 1 N, ∑ m ∈ Finset.range N, G d m ≤
      N * (K * Z + ((A * W + B : ℕ) : ℝ)) := by
    refine (Finset.sum_le_sum hd).trans ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    nlinarith
  calc _ ≤ (N : ℝ) + 2 * ∑ d ∈ Finset.Ico 1 N, ∑ m ∈ Finset.range N, G d m := hI
    _ ≤ (N : ℝ) + 2 * (N * (K * Z + ((A * W + B : ℕ) : ℝ))) := by gcongr
    _ = _ := by simp only [K, Z, Tt, W, r]; ring

set_option maxHeartbeats 4000000 in
/-- **Power-saving second moment for `3 ∣ b` below the threshold**, given the Baker input.
Proved: `pair_bound` per pair with window `W = 3⌊log₃ N / q⌋ + 1`, `q = ⌈6/κ⌉ + 7`; the low window
by `sum_hf_true_le`, both top windows by `sum_topProd_le`, giving `N^{2−δ}` with
`δ = min(1/q, κ − 6/q)`.  This is the analytic core of `ae_isNormal_of_profileOK_of_baker`; the English
proof is in that docstring (non-shadow `m` by the orbit of `t`, shadow `m` by top digits). -/
theorem secondMoment_le_profile (hB : Literature.BakerLogDiscrepancy) (μ₀ : ℚ) (hμ : 2 < μ₀)
    {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b) (hP : ProfileOK μ₀ b) (h : ℤ) (hh : h ≠ 0) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ ω, ‖∑ k ∈ Finset.range N, DecayAeNormal.ee (h * (b : ℝ) ^ k * pt (expFree μ₀) ω)‖ ^ 2
        ∂ExplicitSquare.coinMeasure ≤ C * (N : ℝ) ^ (2 - δ) := by
  have hμ1 : (1 : ℚ) < μ₀ := by linarith
  obtain ⟨hs1, hbt, ht3, ht2, -, -⟩ := profile_data hμ1 hb h3 hP
  set s := padicValNat 3 b
  set t := b / 3 ^ s
  obtain ⟨A, B, hAB⟩ := pair_bound hμ hb h3 hP h hh
  obtain ⟨C, κ, hκ, hC⟩ := sum_topProd_le (hB t ht2 ht3)
  set q : ℕ := ⌈6 / κ⌉₊ + 7
  have hq7 : 7 ≤ q := by omega
  have hqR : (7 : ℝ) ≤ q := by exact_mod_cast hq7
  have hq0 : (0 : ℝ) < q := by linarith
  have hqκ : 6 / (q : ℝ) < κ := by
    have h1 : 6 / κ < (q : ℝ) := by
      have := Nat.le_ceil (6 / κ)
      have : ((⌈6 / κ⌉₊ + 7 : ℕ) : ℝ) = ⌈6 / κ⌉₊ + 7 := by push_cast; ring
      simp only [q]; linarith
    rw [div_lt_iff₀ hκ] at h1
    rw [div_lt_iff₀ hq0]; linarith
  set δ : ℝ := min (1 / q) (κ - 6 / q)
  have hδ1 : δ ≤ 1 / q := min_le_left _ _
  have hδ2 : δ ≤ κ - 6 / q := min_le_right _ _
  have hδ : 0 < δ := lt_min (by positivity) (by linarith)
  have h1q : 1 / (q : ℝ) ≤ 1 / 7 := by gcongr
  set Tt : ℝ := (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t
  set K : ℝ := 9 * Tt + 42 + 18 * |C| + 9 * (A + B)
  refine ⟨1 + 2 * K, δ, hδ, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set r := Nat.log 3 N / q
  set W := 3 * r + 1
  set x : ℝ := (N : ℝ) ^ (1 / q : ℝ)
  set y : ℝ := (3 : ℝ) ^ r
  obtain ⟨hyx, hxy⟩ := three_pow_div_log_bounds q N (by omega) hN
  have hy1 : 1 ≤ y := one_le_pow₀ (by norm_num)
  have hx0 : 0 < x := by positivity
  have hxpow : ∀ k : ℕ, x ^ k = (N : ℝ) ^ ((k : ℝ) / q) := by
    intro k
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; ring
  set Z : ℝ := (N : ℝ) ^ (1 - δ)
  have hle : ∀ a : ℝ, a ≤ 1 - δ → (N : ℝ) ^ a ≤ Z := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hN1 ha
  have hNx : (N : ℝ) / x ≤ Z := by
    have : (N : ℝ) / x = (N : ℝ) ^ (1 - 1 / q : ℝ) := by
      rw [Real.rpow_sub hN0, Real.rpow_one]
    rw [this]; exact hle _ (by linarith)
  have hx6 : x ^ 6 ≤ Z := by
    rw [hxpow]; apply hle
    have : (6 : ℝ) / q = 6 * (1 / q) := by ring
    push_cast; linarith
  have hx6κ : x ^ 6 * (N : ℝ) ^ (1 - κ) ≤ Z := by
    rw [hxpow, ← Real.rpow_add hN0]; apply hle; push_cast; linarith
  have hx3 : x ^ 3 ≤ N := by
    rw [hxpow]
    calc (N : ℝ) ^ ((3 : ℕ) / (q : ℝ)) ≤ (N : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hN1
          have : (3 : ℝ) / q = 3 * (1 / q) := by ring
          push_cast; linarith
      _ = N := Real.rpow_one _
  -- the small powers
  have hP3 : (2 / 3 : ℝ) ^ (3 * r) ≤ 3 / x := by
    have h1 : (2 / 3 : ℝ) ^ (3 * r) ≤ 1 / y := by
      rw [pow_mul, one_div, ← inv_pow]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) r
    calc _ ≤ 1 / y := h1
      _ ≤ 3 / x := by rw [div_le_div_iff₀ (by linarith) hx0]; linarith
  have hPW : (2 / 3 : ℝ) ^ W ≤ 3 / x :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : 3 * r ≤ W)).trans hP3
  have hQW : (1 / 3 : ℝ) ^ W ≤ 3 / x :=
    (pow_le_pow_left₀ (by norm_num) (by norm_num) W).trans hPW
  have hy3 : (3 : ℝ) ^ (3 * r) ≤ x ^ 3 := by
    rw [show (3 : ℝ) ^ (3 * r) = y ^ 3 by simp only [y]; rw [← pow_mul, mul_comm]]
    exact pow_le_pow_left₀ (by positivity) hyx 3
  have h9W : (9 : ℝ) ^ W ≤ 9 * x ^ 6 := by
    have : (9 : ℝ) ^ W = 9 * y ^ 6 := by
      simp only [W, y]; rw [pow_succ, ← pow_mul, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul]; ring
    rw [this]; gcongr
  have hWR : (W : ℝ) ≤ 9 * x ^ 6 := by
    have hr0 : r < 3 ^ r := Nat.lt_pow_self (by norm_num)
    have hr : (r : ℝ) < y := by simp only [y]; exact_mod_cast hr0
    have : y ≤ y ^ 6 := le_self_pow₀ hy1 (by norm_num)
    have : y ^ 6 ≤ x ^ 6 := pow_le_pow_left₀ (by positivity) hyx 6
    simp only [W]; push_cast; nlinarith
  -- per-difference bound
  set M := 2 * b * N + ⌈Real.logb 3 |(h : ℝ)|⌉₊ + W + 1
  set G : ℕ → ℕ → ℝ := fun d m => Bf (expFree μ₀) M (h * ((b : ℝ) ^ d - 1) * (b : ℝ) ^ m)
  have hTN : ∀ β : ℝ, ∑ m ∈ Finset.range N, topProd W (Int.fract (m * Real.logb 3 t + β)) ≤
      (21 + 9 * |C|) * Z := by
    intro β
    refine (hC N hN W β).trans ?_
    have hN3 : 3 * (N : ℝ) * (2 / 3) ^ W ≤ 9 * Z := by
      calc 3 * (N : ℝ) * (2 / 3) ^ W ≤ 3 * N * (3 / x) := by gcongr
        _ = 9 * (N / x) := by ring
        _ ≤ 9 * Z := by gcongr
    have hN4 : 4 * (N : ℝ) * (1 / 3) ^ W ≤ 12 * Z := by
      calc 4 * (N : ℝ) * (1 / 3) ^ W ≤ 4 * N * (3 / x) := by gcongr
        _ = 12 * (N / x) := by ring
        _ ≤ 12 * Z := by gcongr
    have hCC : C * 9 ^ W * (N : ℝ) ^ (1 - κ) ≤ 9 * |C| * Z := by
      have hNk : (0 : ℝ) ≤ (N : ℝ) ^ (1 - κ) := by positivity
      calc C * 9 ^ W * (N : ℝ) ^ (1 - κ) ≤ |C| * (9 * x ^ 6) * (N : ℝ) ^ (1 - κ) := by
            gcongr; exact le_abs_self C
        _ = 9 * |C| * (x ^ 6 * (N : ℝ) ^ (1 - κ)) := by ring
        _ ≤ 9 * |C| * Z := by gcongr
    linarith
  have hd : ∀ d ∈ Finset.Ico 1 N, ∑ m ∈ Finset.range N, G d m ≤ K * Z := by
    intro d hd
    simp only [Finset.mem_Ico] at hd
    set e := padicValNat 3 h.natAbs
    set h' := h.natAbs / 3 ^ e
    have hc : ¬ 3 ∣ h' * (b ^ d - 1) := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hna : h.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hh
      have hh' : ¬ 3 ∣ h' := by
        intro hd3
        have hhe : h.natAbs = 3 ^ e * h' := (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
        have : 3 ^ (e + 1) ∣ h.natAbs := by
          rw [hhe, pow_succ]; exact Nat.mul_dvd_mul_left _ hd3
        exact pow_succ_padicValNat_not_dvd hna this
      have hbd : ¬ 3 ∣ b ^ d - 1 := by
        have h1 : 3 ∣ b ^ d := dvd_pow h3 (by omega)
        have h2 : 1 ≤ b ^ d := Nat.one_le_pow _ _ (by omega)
        omega
      exact fun h3' => (Nat.Prime.dvd_mul Nat.prime_three).1 h3' |>.elim hh' hbd
    have hS1 := sum_hf_true_le ht2 ht3 (3 * r) (h' * (b ^ d - 1)) hc N
    have hS3 : ∑ m ∈ Finset.range N, (if m < A * W + B then (1 : ℝ) else 0) ≤ A * W + B := by
      rw [Finset.sum_boole]
      have : (Finset.range N).filter (· < A * W + B) ⊆ Finset.range (A * W + B) := by
        intro m; simp
      have := Finset.card_le_card this
      simp only [Finset.card_range] at this
      exact_mod_cast this
    refine (Finset.sum_le_sum fun m hm =>
      hAB W N d m hd.1 hd.2 (Finset.mem_range.1 hm)).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have e1 := hTN (Real.logb 3 (|(h : ℝ)| * ((b : ℝ) ^ d - 1)))
    have e2 := hTN (Real.logb 3 |(h : ℝ)|)
    have hS1' : ∑ m ∈ Finset.range N, Hf (fun _ => true) 0 W
        (((h' * (b ^ d - 1) * t ^ m : ℕ)) : ℝ) ≤ 9 * Tt * Z := by
      refine hS1.trans ?_
      have hTt : 0 ≤ Tt := by positivity
      calc ((N : ℝ) + 2 * 3 ^ (3 * r)) * Tt * (2 / 3) ^ (3 * r) ≤ (3 * N) * Tt * (3 / x) := by
            gcongr; linarith
        _ = 9 * Tt * (N / x) := by ring
        _ ≤ 9 * Tt * Z := by gcongr
    have hS3' : (A * W + B : ℕ) ≤ 9 * (A + B) * Z := by
      have hW1 : (1 : ℝ) ≤ W := by simp only [W]; push_cast; linarith [(r.cast_nonneg : (0:ℝ) ≤ r)]
      push_cast
      have hAB0 : (0 : ℝ) ≤ A + B := by positivity
      calc (A : ℝ) * W + B ≤ (A + B) * W := by nlinarith [(B.cast_nonneg : (0:ℝ) ≤ B)]
        _ ≤ (A + B) * (9 * x ^ 6) := by gcongr
        _ ≤ (A + B) * (9 * Z) := by gcongr
        _ = _ := by ring
    have : ((A * W + B : ℕ) : ℝ) = (A : ℝ) * W + B := by push_cast; ring
    simp only [K]; nlinarith [abs_nonneg C, hS3, this]
  -- assemble
  have hpair := pair_sum_le (fun n m => Bf (expFree μ₀) M (h * ((b : ℝ) ^ n - (b : ℝ) ^ m))) G
    (fun d m => Bf_nonneg _ _ _) (fun n => Bf_le_one _ _ _)
    (fun n m hmn => le_of_eq (by
      simp only [G]; congr 1
      rw [show (b : ℝ) ^ n = (b : ℝ) ^ (n - m) * (b : ℝ) ^ m by rw [← pow_add]; congr 1; omega]; ring))
    (fun n m hmn => le_of_eq (by
      simp only [G]; rw [← Bf_neg]; congr 1
      rw [show (b : ℝ) ^ m = (b : ℝ) ^ (m - n) * (b : ℝ) ^ n by rw [← pow_add]; congr 1; omega]; ring)) N
  have hI := (CantorLiouvilleAll.secondMoment_expand_b (expFree μ₀) b h M N).trans hpair
  have hsum : ∑ d ∈ Finset.Ico 1 N, ∑ m ∈ Finset.range N, G d m ≤ N * (K * Z) := by
    refine (Finset.sum_le_sum hd).trans ?_
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hK : 0 ≤ K * Z := by
      have : 0 ≤ K := by simp only [K]; positivity
      positivity
    have : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    nlinarith
  have hNZ : (N : ℝ) * Z = (N : ℝ) ^ (2 - δ) := by
    rw [show (2 - δ) = 1 + (1 - δ) by ring, Real.rpow_add hN0, Real.rpow_one]
  have hNle : (N : ℝ) ≤ (N : ℝ) ^ (2 - δ) := by
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  calc _ ≤ (N : ℝ) + 2 * ∑ d ∈ Finset.Ico 1 N, ∑ m ∈ Finset.range N, G d m := hI
    _ ≤ (N : ℝ) + 2 * (N * (K * Z)) := by gcongr
    _ = (N : ℝ) + 2 * K * (N * Z) := by ring
    _ ≤ _ := by rw [hNZ]; nlinarith

/-- **The crux, conditional on the top-digit input.**  Confidence 60%.  English proof: split the
pair sum by `m`.  Outside every shadow, the window `[sm, sm + log₃N/2)` is free and the orbit
count of `sum_Hf_le_b` (with `t`) applies.  In the shadow, use the top `ε log N` digits of
`h(bᵈ−1)tᵐ`, which sit at free places because `(s+L)m > μ₀a` (`window_covered_imp`) and are
fixed by `{(m+d) log₃ t + β_{h,d}}`; `LogDiscrepancy` bounds the number of `m` whose top digits
are degenerate by `N(2/3)^{εlog N} + C N^{1−κ} 3^{ε log N}`, a power saving for small `ε`.
Then `ae_isNormal_of_secondMoment` along `CantorLiouville.sched`. -/
theorem ae_isNormal_of_profileOK_of_baker (hB : Literature.BakerLogDiscrepancy) (μ₀ : ℚ)
    (hμ : 2 < μ₀) :
    ∀ᵐ ω ∂coins, ∀ b : ℕ, 2 ≤ b → ProfileOK μ₀ b → IsNormal b (cantorExpReal μ₀ ω) := by
  have h1 : (1 : ℚ) < μ₀ := by linarith
  have hthree : ∀ᵐ ω ∂coins, ∀ b : ℕ, 2 ≤ b → 3 ∣ b →
      ProfileOK μ₀ b → IsNormal b (cantorExpReal μ₀ ω) := by
    rw [ae_all_iff]
    intro b
    by_cases hb : 2 ≤ b
    swap; · exact Eventually.of_forall fun _ h => absurd h hb
    by_cases h3 : 3 ∣ b
    swap; · exact Eventually.of_forall fun _ _ h => absurd h h3
    by_cases hPb : ProfileOK μ₀ b
    swap; · exact Eventually.of_forall fun _ _ _ h => absurd h hPb
    have : ∀ᵐ ω ∂coins, IsNormal b (cantorExpReal μ₀ ω) := by
      rw [coins_eq_coinMeasure]
      refine CantorLiouvilleAll.ae_isNormal_of_secondMoment ExplicitSquare.coinMeasure hb _
        (measurable_pt (expFree μ₀)) sched sched_strictMono sched_ratio ?_
      intro h hh
      obtain ⟨C, δ, hδ, hC⟩ := secondMoment_le_profile hB μ₀ hμ hb h3 hPb h hh
      refine ((summable_sched_rpow hδ).mul_left (max C 0)).of_nonneg_of_le
        (fun j => div_nonneg (integral_nonneg fun ω => by positivity) (by positivity)) (fun j => ?_)
      have hN : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
      rw [div_le_iff₀ (by positivity)]
      calc _ ≤ C * (sched j : ℝ) ^ (2 - δ) := hC _ (one_le_sched j)
        _ ≤ max C 0 * (sched j : ℝ) ^ (2 - δ) := by gcongr; exact le_max_left _ _
        _ = _ := by
          rw [mul_assoc, ← Real.rpow_natCast _ 2, ← Real.rpow_add hN]; congr 2; push_cast; ring
    exact this.mono fun _ h _ _ _ => h
  filter_upwards [ae_isNormal_of_coprime_three μ₀ h1, hthree] with ω hω1 hω2 b hb hPb
  by_cases h3 : 3 ∣ b
  · exact hω2 b hb h3 hPb
  · exact hω1 b hb h3

/-- **Normal below the threshold, a.e.**  Open node; confidence 70% true, but the elementary route
below is BLOCKED in the shadow (see `shadow_card_ge`, Maze row "elementary orbit port to 3 ∣ b");
the live route is `ae_isNormal_of_profileOK_of_baker` plus a proof of `LogDiscrepancy`.

English proof (sketch).  For `3 ∤ b` this is `ae_isNormal_of_coprime_three`.  Let `b = 3ˢt` with
`s ≥ 1`, `t > 3^{s(μ₀−1)}`, `L = log₃ t`.
1. *Window.*  In the coin law, the Fourier coefficient at `ξ = h·bᵐ·(bᵈ − 1)` (the pair terms
   of the second moment; `bᵈ − 1` is prime to 3) is a product of `|cos(2πξ/3^{p+1})|` over
   the free places `p`.  Factors with `p + 1 ≤ sm` are 1, and so are factors with `p` beyond the
   top digit of `ξ`.  The window is `[sm, (s+L)m + d log₃ b + O(log |h|)]`.
2. *Free count.*  A run `[a, μ₀a)` covers `[sm, (s+L)m]` only if `μ₀ > 1 + L/s`.  Below the
   threshold, the free places in the window number at least `a(1 − μ₀ s/(s+L)) − O(1)` for the
   worst run, which is linear in `m`.  Earlier runs are negligible because `a_{k+1}/a_k → ∞`.
3. *Digit changes.*  The ternary digits of `ξ` on the window are those of `h(bᵈ−1)tᵐ` shifted
   by `sm`.  As `m` varies, `tᵐ mod 3ᵏ` runs through a subgroup of index `≤ 3^{v₃(t²−1)}`
   (`padicValNat_pow_sub_one_le` for `t`), so the counting of
   `CantorLiouvilleAll.sum_Hf_le_b` applies with `t` in place of `b`.  This gives a summable
   second moment along `CantorLiouville.sched`, and `ae_isNormal_of_secondMoment` concludes.

Sibling check: for `t = 1` step 3 has a trivial orbit, and the frequencies' digits are one word
shifted.  The argument stops there, as it must, since `x` is never normal to a power of 3. -/
theorem ae_isNormal_of_profileOK (μ₀ : ℚ) (hμ : 2 < μ₀) :
    ∀ᵐ ω ∂coins, ∀ b : ℕ, 2 ≤ b → ProfileOK μ₀ b → IsNormal b (cantorExpReal μ₀ ω) := by
  sorry

/-! ### Wiring the headline through the family derandomizer

The family derandomizer `CantorLiouvilleAll.exists_computable_normal_sched_family` needs, for each
admitted base, a second moment `κ b · |h| · N² · W N` with ONE `W` and a PRIMITIVE RECURSIVE `κ`.
`secondMoment_le_profile` gives `C_{b,h} N^{2−δ_b}` with `C, δ` inside an `∃`, which cannot be
made computable.  Two changes fix this:
* the Baker input is taken in effective form (`Literature.BakerLogDiscrepancyEff`, one `K` for
  all `t`), so every constant is an explicit function of `b` and `K`;
* `W` decays only polylogarithmically (`profW`).  The small-`m` constant of `pair_classify`
  grows like `a_{k}` with `k ≍ log |h|`, faster than any power of `|h|`; it is absorbed because
  `N² profW N ≥ N²·|h|^{−o(1)}` once `N ≤ B_h²`, and by the `N^{−δ}` saving beyond. -/

/-- **Literature, effective form (Baker 1966 / Baker–Wüstholz 1993 with Erdős–Turán).**  For
`t ≥ 2` prime to 3, `|q log t − p log 3| ≥ q^{−C log t}` with an absolute effective `C`, so the
discrepancy of `{m log₃ t + β}` is `≪ t^{O(1)} N^{1 − c/log t}` uniformly in `β`.  Transcribed
weaker: one `K` with constant `t^K` and saving `1/(K t)` (`1/(K t) ≤ c/log t`). -/
def Literature.BakerLogDiscrepancyEff : Prop :=
  ∃ K : ℕ, 1 ≤ K ∧ ∀ t : ℕ, 2 ≤ t → ¬ 3 ∣ t → ∀ N : ℕ, 1 ≤ N → ∀ β u v : ℝ, 0 ≤ u → u ≤ v →
    v ≤ 1 → |(visitCount (fun m => Int.fract (m * Real.logb 3 t + β)) u v N : ℝ) - N * (v - u)| ≤
      (t : ℝ) ^ K * (N : ℝ) ^ (1 - 1 / ((K : ℝ) * t))

theorem bakerLogDiscrepancy_of_eff (hB : Literature.BakerLogDiscrepancyEff) :
    Literature.BakerLogDiscrepancy := by
  obtain ⟨K, hK, hD⟩ := hB
  intro t ht h3
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  exact ⟨(t : ℝ) ^ K, 1 / ((K : ℝ) * t), by positivity, hD t ht h3⟩

/-- The uniform weight: polylogarithmic decay. -/
noncomputable def profW (N : ℕ) : ℝ := 1 / ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 16

theorem profW_nonneg (N : ℕ) : 0 ≤ profW N := by unfold profW; positivity

theorem profW_antitone : Antitone profW := by
  intro a b hab
  unfold profW
  have h1 : Nat.log 2 a + 1 ≤ Nat.log 2 b + 1 := by
    have := Nat.log_mono_right (b := 2) hab; omega
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast h1) 16


/-- One division step of the 3-adic valuation, carrying a counter. -/
def stepV (x : ℕ × ℕ) : ℕ × ℕ := if x.1 % 3 = 0 ∧ 0 < x.1 then (x.1 / 3, x.2 + 1) else x

theorem primrec_stepV : Primrec stepV := by
  have hc : PrimrecPred fun x : ℕ × ℕ => x.1 % 3 = 0 ∧ 0 < x.1 :=
    PrimrecPred.and (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.fst (Primrec.const 3))
      (Primrec.const 0)) (Primrec.nat_lt.comp (Primrec.const 0) Primrec.fst)
  exact Primrec.ite hc (Primrec.pair (Primrec.nat_div.comp Primrec.fst (Primrec.const 3))
    (Primrec.succ.comp Primrec.snd)) Primrec.id

theorem stepV_iter (b n : ℕ) :
    stepV^[n] (b, 0) = (b / 3 ^ min n (padicValNat 3 b), min n (padicValNat 3 b)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set v := padicValNat 3 b
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hn : n < v
    · have hb : b ≠ 0 := by rintro rfl; simp [v] at hn
      have hd : 3 ^ (n + 1) ∣ b := (pow_dvd_pow 3 hn).trans pow_padicValNat_dvd
      have hmin : min n v = n := min_eq_left hn.le
      have hmin' : min (n + 1) v = n + 1 := min_eq_left hn
      rw [hmin, hmin']
      have h3 : 3 ∣ b / 3 ^ n := by
        rw [Nat.dvd_div_iff_mul_dvd ((pow_dvd_pow 3 (Nat.le_succ n)).trans hd), ← pow_succ]
        exact hd
      have hpos : 0 < b / 3 ^ n := by
        apply Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hb) ((pow_dvd_pow 3 (by omega)).trans hd))
        positivity
      unfold stepV
      rw [if_pos ⟨Nat.mod_eq_zero_of_dvd h3, hpos⟩, Nat.div_div_eq_div_mul, ← pow_succ]
    · push Not at hn
      have hmin : min n v = v := min_eq_right hn
      have hmin' : min (n + 1) v = v := min_eq_right (by omega)
      rw [hmin, hmin']
      unfold stepV
      rw [if_neg]
      rintro ⟨h0, hpos⟩
      have hb : b ≠ 0 := by rintro rfl; simp at hpos
      have hd3 : 3 ∣ b / 3 ^ v := Nat.dvd_of_mod_eq_zero h0
      have : 3 ^ (v + 1) ∣ b := by
        have hv : 3 ^ v ∣ b := pow_padicValNat_dvd
        rw [pow_succ]
        have := Nat.mul_dvd_mul_left (3 ^ v) hd3
        rwa [Nat.mul_div_cancel' hv] at this
      exact pow_succ_padicValNat_not_dvd hb this

/-- `ProfileOK` as an integer comparison. -/
theorem profileOK_iff (μ₀ : ℚ) (hμ : 1 < μ₀) (b : ℕ) :
    ProfileOK μ₀ b ↔ 3 ^ (padicValNat 3 b * (μ₀.num.toNat - μ₀.den)) <
      (b / 3 ^ padicValNat 3 b) ^ μ₀.den := by
  set v := padicValNat 3 b
  set t := b / 3 ^ v
  set p := μ₀.num.toNat
  set q := μ₀.den
  have hnum : 0 < μ₀.num := Rat.num_pos.2 (by linarith)
  have hpz : ((p : ℤ)) = μ₀.num := Int.toNat_of_nonneg hnum.le
  have hpQ : (p : ℚ) = μ₀ * q := by
    have h1 : ((p : ℤ) : ℚ) = (μ₀.num : ℚ) := by rw [hpz]
    rw [show ((q : ℕ) : ℚ) = (μ₀.den : ℚ) from rfl, Rat.mul_den_eq_num]
    exact_mod_cast h1
  have hq0 : (0 : ℚ) < q := by exact_mod_cast μ₀.den_pos
  have hqp : q ≤ p := by
    have : (q : ℚ) ≤ p := by rw [hpQ]; nlinarith
    exact_mod_cast this
  have hpR : (p : ℝ) = (μ₀ : ℝ) * q := by exact_mod_cast hpQ
  unfold ProfileOK
  rw [← pow_lt_pow_iff_left₀ (n := q) (by positivity) (by positivity) μ₀.den_nz,
    ← Real.rpow_natCast ((3 : ℝ) ^ _), ← Real.rpow_mul (by norm_num),
    show (v : ℝ) * ((μ₀ : ℝ) - 1) * (q : ℝ) = ((v * (p - q) : ℕ) : ℝ) by
      push_cast [Nat.cast_sub hqp]; rw [hpR]; ring, Real.rpow_natCast]
  exact_mod_cast Iff.rfl

theorem padicValNat_three_le (b : ℕ) : padicValNat 3 b ≤ b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · have : 3 ^ padicValNat 3 b ≤ b := Nat.le_of_dvd hb pow_padicValNat_dvd
    exact (Nat.lt_pow_self (by norm_num)).le.trans this

/-- `ProfileOK` is primitive recursive (`3^{s(p−q)} < t^q` for `μ₀ = p/q`). -/
theorem primrecPred_profileOK (μ₀ : ℚ) (hμ : 1 < μ₀) : PrimrecPred (ProfileOK μ₀) := by
  have hit : Primrec fun b : ℕ => stepV^[b] (b, 0) :=
    Primrec.nat_iterate Primrec.id (Primrec.pair Primrec.id (Primrec.const 0))
      (primrec_stepV.comp Primrec.snd).to₂
  have hP : PrimrecPred fun b : ℕ => 3 ^ ((stepV^[b] (b, 0)).2 * (μ₀.num.toNat - μ₀.den)) <
      ((stepV^[b] (b, 0)).1) ^ μ₀.den :=
    Primrec.nat_lt.comp
      (ComputableNormal.primrec_pow.comp (Primrec.const 3)
        (Primrec.nat_mul.comp (Primrec.snd.comp hit) (Primrec.const _)))
      (ComputableNormal.primrec_pow.comp (Primrec.fst.comp hit) (Primrec.const _))
  refine hP.of_eq fun b => ?_
  rw [stepV_iter, min_eq_right (padicValNat_three_le b)]
  exact (profileOK_iff μ₀ hμ b).symm

theorem pow_le_fact_two_rpow (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    y ^ n ≤ n.factorial * 2 ^ n * (2 : ℝ) ^ y := by
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hl0 : 0 < Real.log 2 := by linarith
  have h1 := Real.pow_div_factorial_le_exp (y * Real.log 2) (mul_nonneg hy hl0.le) n
  rw [div_le_iff₀ (by positivity), mul_pow] at h1
  have h2 : Real.exp (y * Real.log 2) = (2 : ℝ) ^ y := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  rw [h2] at h1
  have h3 : y ^ n ≤ y ^ n * (Real.log 2) ^ n * 2 ^ n := by
    have : (1 / 2 : ℝ) ^ n ≤ (Real.log 2) ^ n := pow_le_pow_left₀ (by norm_num) hl n
    have h4 : (1 : ℝ) ≤ (Real.log 2) ^ n * 2 ^ n := by
      calc (1 : ℝ) = (1 / 2) ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
        _ ≤ _ := by gcongr
    have : 0 ≤ y ^ n := by positivity
    nlinarith
  calc y ^ n ≤ y ^ n * (Real.log 2) ^ n * 2 ^ n := h3
    _ ≤ (2 : ℝ) ^ y * n.factorial * 2 ^ n := by gcongr
    _ = _ := by ring

/-- Polylog against a power: `(log₂ N + 1)^n ≤ 2·n!·2ⁿ·mⁿ·N^{1/m}`. -/
theorem log_pow_le_rpow (n m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ n ≤
      2 * n.factorial * 2 ^ n * (m : ℝ) ^ n * (N : ℝ) ^ (1 / m : ℝ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set ℓ := Nat.log 2 N
  set y : ℝ := (ℓ : ℝ) / m
  have hy : 0 ≤ y := by positivity
  have hℓ : ((ℓ + 1 : ℕ) : ℝ) ≤ m * (y + 1) := by
    simp only [y]; push_cast; field_simp; nlinarith
  have h1 := pow_le_fact_two_rpow n (by linarith : 0 ≤ y + 1)
  have h2 : (2 : ℝ) ^ y ≤ (N : ℝ) ^ (1 / m : ℝ) := by
    have h3 : (2 : ℝ) ^ y = ((2 : ℝ) ^ ℓ) ^ (1 / m : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; simp only [y]; ring_nf
    rw [h3]
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have h4 : (2 : ℝ) ^ (y + 1) = 2 * 2 ^ y := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
  calc ((ℓ + 1 : ℕ) : ℝ) ^ n ≤ (m * (y + 1)) ^ n := pow_le_pow_left₀ (by positivity) hℓ n
    _ = (m : ℝ) ^ n * (y + 1) ^ n := by rw [mul_pow]
    _ ≤ (m : ℝ) ^ n * (n.factorial * 2 ^ n * (2 * 2 ^ y)) := by rw [← h4]; gcongr
    _ ≤ (m : ℝ) ^ n * (n.factorial * 2 ^ n * (2 * (N : ℝ) ^ (1 / m : ℝ))) := by gcongr
    _ = _ := by ring

/-- The trivial second moment. -/
theorem secondMoment_le_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ℕ → Ω → ℝ) (N : ℕ) :
    ∫ ω, ‖∑ k ∈ Finset.range N, DecayAeNormal.ee (f k ω)‖ ^ 2 ∂μ ≤ (N : ℝ) ^ 2 := by
  have hb : ∀ ω, ‖∑ k ∈ Finset.range N, DecayAeNormal.ee (f k ω)‖ ≤ N := by
    intro ω
    refine (norm_sum_le _ _).trans ?_
    simp [DecayAeNormal.norm_ee]
  have := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun ω => ‖∑ k ∈ Finset.range N, DecayAeNormal.ee (f k ω)‖ ^ 2) (C := (N : ℝ) ^ 2)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb ω) 2)
  rw [probReal_univ, mul_one] at this
  exact (le_abs_self _).trans this

theorem expRunEnd_le (μ₀ : ℚ) (hμ : 0 ≤ μ₀) (a : ℕ) :
    expRunEnd μ₀ a ≤ (⌈μ₀⌉₊ + 1) * a := by
  unfold expRunEnd
  apply Nat.ceil_le.2
  push_cast
  have := Nat.le_ceil μ₀
  have ha : (0 : ℚ) ≤ a := by positivity
  nlinarith

theorem expRunStart_le (μ₀ : ℚ) (hμ : 0 ≤ μ₀) (k : ℕ) :
    expRunStart μ₀ k ≤ 4 * ((⌈μ₀⌉₊ + 1) * (k + 1)) ^ k := by
  set M := ⌈μ₀⌉₊ + 1
  induction k with
  | zero => simp [expRunStart]
  | succ k ih =>
    simp only [expRunStart]
    have h1 := expRunEnd_le μ₀ hμ (expRunStart μ₀ k)
    have h2 : (M * (k + 1)) ^ k ≤ (M * (k + 1 + 1)) ^ k := Nat.pow_le_pow_left (by nlinarith) k
    calc (k + 2) * expRunEnd μ₀ (expRunStart μ₀ k) ≤ (k + 2) * (M * (4 * (M * (k + 1)) ^ k)) := by
          gcongr; exact h1.trans (Nat.mul_le_mul_left _ ih)
      _ ≤ (k + 2) * (M * (4 * (M * (k + 1 + 1)) ^ k)) := by gcongr
      _ = 4 * (M * (k + 1 + 1)) ^ (k + 1) := by ring

/-- **Margin below the threshold**, explicitly: `g = s + L − μ₀ s ≥ 1/(4 q 3^{s(p−q)})`. -/
theorem margin_ge (μ₀ : ℚ) (hμ : 1 < μ₀) {b : ℕ} (hP : ProfileOK μ₀ b) :
    1 / (4 * (μ₀.den : ℝ) * 3 ^ (padicValNat 3 b * (μ₀.num.toNat - μ₀.den))) ≤
      padicValNat 3 b + Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ) - μ₀ * padicValNat 3 b := by
  have hlt := (profileOK_iff μ₀ hμ b).1 hP
  set s := padicValNat 3 b
  set t := b / 3 ^ s
  set p := μ₀.num.toNat
  set q := μ₀.den
  set e := s * (p - q)
  have hnum : 0 < μ₀.num := Rat.num_pos.2 (by linarith)
  have hpz : ((p : ℤ)) = μ₀.num := Int.toNat_of_nonneg hnum.le
  have hpQ : (p : ℚ) = μ₀ * q := by
    have h1 : ((p : ℤ) : ℚ) = (μ₀.num : ℚ) := by rw [hpz]
    rw [show ((q : ℕ) : ℚ) = (μ₀.den : ℚ) from rfl, Rat.mul_den_eq_num]
    exact_mod_cast h1
  have hq0 : (0 : ℚ) < q := by exact_mod_cast μ₀.den_pos
  have hqp : q ≤ p := by
    have : (q : ℚ) ≤ p := by rw [hpQ]; nlinarith
    exact_mod_cast this
  have hpR : (p : ℝ) = (μ₀ : ℝ) * q := by exact_mod_cast hpQ
  have hqR : (0 : ℝ) < q := by exact_mod_cast μ₀.den_pos
  have he : (e : ℝ) = s * ((μ₀ : ℝ) - 1) * q := by
    simp only [e]; push_cast [Nat.cast_sub hqp]; rw [hpR]; ring
  have htq : (3 : ℝ) ^ e + 1 ≤ (t : ℝ) ^ q := by exact_mod_cast hlt
  have h3e : (0 : ℝ) < 3 ^ e := by positivity
  have htq0 : (0 : ℝ) < (t : ℝ) ^ q := by linarith
  have ht0 : (0 : ℝ) < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · have h0 : (t : ℝ) = 0 := by exact_mod_cast h
      rw [h0, zero_pow μ₀.den_nz] at htq0; exact absurd htq0 (lt_irrefl 0)
    · exact_mod_cast h
  set u : ℝ := 1 / 3 ^ e
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by
    simp only [u]; rw [div_le_one h3e]; exact one_le_pow₀ (by norm_num)
  have hratio : 1 + u ≤ (t : ℝ) ^ q / 3 ^ e := by
    rw [le_div_iff₀ h3e]; simp only [u]; field_simp; linarith
  have hlog1 : u / 4 ≤ Real.logb 3 (1 + u) := by
    have h1 := Real.one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 + u)
    have h2 : u / 2 ≤ 1 - (1 + u)⁻¹ := by
      rw [show 1 - (1 + u)⁻¹ = u / (1 + u) by field_simp; ring]
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
    have hl3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
    have hl30 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    rw [Real.logb, le_div_iff₀ hl30]
    nlinarith
  have hlog2 : Real.logb 3 (1 + u) ≤ Real.logb 3 ((t : ℝ) ^ q) - e := by
    have := Real.logb_le_logb_of_le (b := 3) (by norm_num) (by linarith) hratio
    have h3 : Real.logb 3 ((3 : ℝ) ^ e) = e := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
    rw [Real.logb_div htq0.ne' h3e.ne', h3] at this
    exact this
  rw [Real.logb_pow] at hlog2
  set L := Real.logb 3 (t : ℝ)
  have key : u / 4 ≤ q * (s + L - μ₀ * s) := by
    have : (q : ℝ) * (s + L - μ₀ * s) = q * L - e := by rw [he]; ring
    rw [this]; linarith
  rw [div_le_iff₀ (by positivity)]
  have : u * 3 ^ e = 1 := by simp only [u]; field_simp
  nlinarith

/-- Explicit constants for the uniform bound. -/
def profM (μ₀ : ℚ) : ℕ := ⌈μ₀⌉₊ + 1

def profF (μ₀ : ℚ) (b : ℕ) : ℕ := 4 * μ₀.den * 3 ^ (b * μ₀.num.toNat)

def profP (μ₀ : ℚ) (b : ℕ) : ℕ :=
  profM μ₀ + 5 + 4 * profM μ₀ * (b + 1) ^ 4 + (profM μ₀ + 4) * profF μ₀ b

/-- The profile facts used by the explicit bounds. -/
theorem profile_facts {μ₀ : ℚ} (hμ : 2 < μ₀) {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b)
    (hP : ProfileOK μ₀ b) :
    1 ≤ padicValNat 3 b ∧ 0 ≤ Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ) ∧
      (padicValNat 3 b : ℝ) + Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ) ≤ b ∧
      1 / (profF μ₀ b : ℝ) ≤ padicValNat 3 b + Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ) -
        μ₀ * padicValNat 3 b := by
  have hμ1 : (1 : ℚ) < μ₀ := by linarith
  obtain ⟨hs1, -, -, ht2, -, hlogb⟩ := profile_data hμ1 hb h3 hP
  have hm := margin_ge μ₀ hμ1 hP
  set s := padicValNat 3 b
  set t := b / 3 ^ s
  refine ⟨hs1, Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ t)), ?_, ?_⟩
  · rw [← hlogb]
    have h1 : (b : ℝ) ≤ 3 ^ b := by exact_mod_cast (Nat.lt_pow_self (by norm_num)).le
    have := Real.logb_le_logb_of_le (b := 3) (by norm_num) (by exact_mod_cast (by omega : 0 < b)) h1
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this
  · refine le_trans ?_ hm
    have hsb : s ≤ b := padicValNat_three_le b
    have he : s * (μ₀.num.toNat - μ₀.den) ≤ b * μ₀.num.toNat :=
      Nat.mul_le_mul hsb (Nat.sub_le _ _)
    have h1 : (4 * (μ₀.den : ℝ) * 3 ^ (s * (μ₀.num.toNat - μ₀.den))) ≤ (profF μ₀ b : ℝ) := by
      unfold profF; push_cast
      gcongr; norm_num
    have hq : (0 : ℝ) < μ₀.den := by exact_mod_cast μ₀.den_pos
    exact one_div_le_one_div_of_le (by positivity) h1

theorem nat_add_two_le_two_pow (c : ℕ) : c + 2 ≤ 2 ^ (c + 1) := by
  have := Nat.lt_two_pow_self (n := c + 1); omega

set_option maxHeartbeats 2000000 in
/-- **The small-`m` constant is at most exponential in `(log |h|)²`.** -/
theorem pcB_le {μ₀ : ℚ} (hμ : 2 < μ₀) {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b) (hP : ProfileOK μ₀ b)
    (H : ℝ) (hH : 0 ≤ H) :
    pcB μ₀ (padicValNat 3 b) (Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ)) H + 1 ≤
      2 ^ (profP μ₀ b * (⌈H⌉₊ + 1) ^ 2) := by
  obtain ⟨hs1, hL0, hsL, hg⟩ := profile_facts hμ hb h3 hP
  set s := padicValNat 3 b
  set L := Real.logb 3 (b / 3 ^ s : ℕ)
  set M := profM μ₀
  set F := profF μ₀ b
  set H' := ⌈H⌉₊
  have hHH : H ≤ H' := Nat.le_ceil H
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hμ0 : (0 : ℚ) ≤ μ₀ := by linarith
  have hMR : (μ₀ : ℝ) ≤ M := by
    simp only [M, profM]; push_cast
    have : (μ₀ : ℝ) ≤ ((⌈μ₀⌉₊ : ℕ) : ℝ) := by exact_mod_cast Nat.le_ceil μ₀
    linarith
  have hF0 : (0 : ℝ) < F := by
    simp only [F, profF]; have := μ₀.den_pos; positivity
  have hg0 : 0 < (s : ℝ) + L - μ₀ * s := lt_of_lt_of_le (by positivity) hg
  -- the run index
  set k := (b + 1) ^ 2 * (H' + 1)
  set k1 := ⌈((s + L) ^ 2 / s + ((s + L) * H / s + H)) / s⌉₊
  have hk1 : k1 ≤ k := by
    apply Nat.ceil_le.2
    set lam := (s : ℝ) + L
    have hl0 : 0 ≤ lam := by positivity
    have hlb : lam ≤ b := hsL
    have e1 : lam ^ 2 / s ≤ lam ^ 2 := div_le_self (by positivity) hsR
    have e2 : lam * H / s ≤ lam * H := div_le_self (by positivity) hsR
    have hX : 0 ≤ lam ^ 2 / s + (lam * H / s + H) := by positivity
    have e3 := div_le_self hX hsR
    simp only [k]; push_cast
    have hb0 : (0 : ℝ) ≤ b := by positivity
    have : lam * H ≤ b * H' := by nlinarith
    have : lam ^ 2 ≤ (b : ℝ) ^ 2 := by nlinarith
    have hH'0 : (0 : ℝ) ≤ H' := by positivity
    nlinarith
  -- the run end
  have hE : expRunEnd μ₀ (expRunStart μ₀ k1) ≤ 2 ^ (M + 2 + M * (k + 1) ^ 2) := by
    have h1 := expRunEnd_le μ₀ hμ0 (expRunStart μ₀ k1)
    have h2 := expRunStart_le μ₀ hμ0 k1
    have hM1 : 1 ≤ M := by simp [M, profM]
    have h4 : (M * (k1 + 1)) ^ k1 ≤ (M * (k + 1)) ^ k :=
      (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (by omega)) _).trans
        (Nat.pow_le_pow_right (by positivity) hk1)
    have h5 : (M * (k + 1)) ^ k ≤ 2 ^ (M * (k + 1) ^ 2) := by
      calc (M * (k + 1)) ^ k ≤ (2 ^ (M * (k + 1))) ^ k :=
            Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
        _ = 2 ^ (M * (k + 1) * k) := by rw [← pow_mul]
        _ ≤ 2 ^ (M * (k + 1) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have h6 : M * 4 ≤ 2 ^ (M + 2) := by
      rw [pow_add]; exact Nat.mul_le_mul_right _ (Nat.lt_two_pow_self).le
    calc expRunEnd μ₀ (expRunStart μ₀ k1) ≤ M * (4 * (M * (k1 + 1)) ^ k1) :=
          h1.trans (Nat.mul_le_mul_left _ h2)
      _ ≤ M * (4 * 2 ^ (M * (k + 1) ^ 2)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (h4.trans h5))
      _ = (M * 4) * 2 ^ (M * (k + 1) ^ 2) := by ring
      _ ≤ 2 ^ (M + 2) * 2 ^ (M * (k + 1) ^ 2) := Nat.mul_le_mul_right _ h6
      _ = _ := by rw [← pow_add]
  -- the margin term
  have hc2 : ⌈((μ₀ : ℝ) * H + 4) / (s + L - μ₀ * s)⌉₊ ≤ (M * H' + 4) * F := by
    apply Nat.ceil_le.2
    have hx : 0 ≤ (μ₀ : ℝ) * H + 4 := by
      have : (0 : ℝ) ≤ μ₀ := by exact_mod_cast hμ0
      positivity
    have hinv : 1 / ((s : ℝ) + L - μ₀ * s) ≤ F := by
      rw [div_le_iff₀ hg0]; rw [div_le_iff₀ hF0] at hg; linarith
    have hMH : (μ₀ : ℝ) * H ≤ M * H' := by
      have : (0 : ℝ) ≤ μ₀ := by exact_mod_cast hμ0
      have : (0 : ℝ) ≤ M := by positivity
      nlinarith
    push_cast
    calc ((μ₀ : ℝ) * H + 4) / (s + L - μ₀ * s) = ((μ₀ : ℝ) * H + 4) * (1 / (s + L - μ₀ * s)) := by
          ring
      _ ≤ ((μ₀ : ℝ) * H + 4) * F := by gcongr
      _ ≤ (M * H' + 4) * F := by gcongr
  -- assemble
  unfold pcB
  set a := M + 2 + M * (k + 1) ^ 2
  set c := (M * H' + 4) * F
  have hsum : a + c + 2 ≤ profP μ₀ b * (H' + 1) ^ 2 := by
    have hk : k + 1 ≤ 2 * (b + 1) ^ 2 * (H' + 1) := by
      simp only [k]; nlinarith [Nat.one_le_pow 2 (b + 1) (by omega)]
    have hk2 : M * (k + 1) ^ 2 ≤ 4 * M * (b + 1) ^ 4 * (H' + 1) ^ 2 := by
      calc M * (k + 1) ^ 2 ≤ M * (2 * (b + 1) ^ 2 * (H' + 1)) ^ 2 := by gcongr
        _ = _ := by ring
    have hc : c ≤ (M + 4) * F * (H' + 1) ^ 2 := by
      simp only [c]
      have : (M * H' + 4) ≤ (M + 4) * (H' + 1) := by nlinarith
      calc (M * H' + 4) * F ≤ (M + 4) * (H' + 1) * F := Nat.mul_le_mul_right _ this
        _ ≤ (M + 4) * (H' + 1) * F * (H' + 1) := Nat.le_mul_of_pos_right _ (by omega)
        _ = _ := by ring
    have hone : 1 ≤ (H' + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hM4 : M + 4 ≤ (M + 5) * (H' + 1) ^ 2 := by nlinarith
    simp only [a, profP]
    rw [show profM μ₀ = M from rfl, show profF μ₀ b = F from rfl]
    nlinarith
  calc expRunEnd μ₀ (expRunStart μ₀ k1) + ⌈((μ₀ : ℝ) * H + 4) / (s + L - μ₀ * s)⌉₊ + 1 + 1
      ≤ 2 ^ a + c + 2 := by omega
    _ ≤ 2 ^ a + 2 ^ (c + 1) := by have := nat_add_two_le_two_pow c; omega
    _ ≤ 2 ^ (a + c + 2) := by
        have h1 : 2 ^ a ≤ 2 ^ (a + c + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : 2 ^ (c + 1) ≤ 2 ^ (a + c + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [show a + c + 2 = (a + c + 1) + 1 by omega, pow_succ]; omega
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hsum

theorem pcA_le {μ₀ : ℚ} (hμ : 2 < μ₀) {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b) (hP : ProfileOK μ₀ b) :
    pcA μ₀ (padicValNat 3 b) (Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ)) ≤
      profM μ₀ * profF μ₀ b := by
  obtain ⟨hs1, hL0, -, hg⟩ := profile_facts hμ hb h3 hP
  set s := padicValNat 3 b
  set L := Real.logb 3 (b / 3 ^ s : ℕ)
  have hF0 : (0 : ℝ) < profF μ₀ b := by unfold profF; have := μ₀.den_pos; positivity
  have hg0 : 0 < (s : ℝ) + L - μ₀ * s := lt_of_lt_of_le (by positivity) hg
  have hinv : 1 / ((s : ℝ) + L - μ₀ * s) ≤ profF μ₀ b := by
    rw [div_le_iff₀ hg0]; rw [div_le_iff₀ hF0] at hg; linarith
  have hM : (μ₀ : ℝ) + 1 ≤ profM μ₀ := by
    unfold profM; push_cast
    have : (μ₀ : ℝ) ≤ ((⌈μ₀⌉₊ : ℕ) : ℝ) := by exact_mod_cast Nat.le_ceil μ₀
    linarith
  unfold pcA
  apply Nat.ceil_le.2
  have hμ0 : (0 : ℝ) ≤ (μ₀ : ℝ) + 1 := by
    have : (2 : ℝ) < μ₀ := by exact_mod_cast hμ
    linarith
  push_cast
  calc ((μ₀ : ℝ) + 1) / (s + L - μ₀ * s) = ((μ₀ : ℝ) + 1) * (1 / (s + L - μ₀ * s)) := by ring
    _ ≤ ((μ₀ : ℝ) + 1) * profF μ₀ b := by gcongr
    _ ≤ _ := by gcongr

def profG (n m : ℕ) : ℕ := 2 * n.factorial * 2 ^ n * m ^ n

/-- The uniform constant. -/
def profKappa (μ₀ : ℚ) (K b : ℕ) : ℕ :=
  profG 16 1 + 2 * (9 * b ^ 2 + 42 + 162 * b ^ K) * profG 16 (K * b * (6 * K * b + 7)) +
    8 * (profM μ₀ * profF μ₀ b) * profG 17 1 + 2 * profG 16 2 +
      (2 * profP μ₀ b) ^ 16 * Nat.factorial 32 * 2 ^ 34

theorem profG_cast (n m : ℕ) : (profG n m : ℝ) = 2 * n.factorial * 2 ^ n * (m : ℝ) ^ n := by
  unfold profG; push_cast; ring

theorem profG_mono (n : ℕ) {m m' : ℕ} (h : m ≤ m') : profG n m ≤ profG n m' := by
  unfold profG; gcongr

/-- **Small `N`** (below the square of the small-`m` constant): the polylog weight costs at most
a constant times `|h|`. -/
theorem small_case {μ₀ : ℚ} (hμ : 2 < μ₀) {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b) (hP : ProfileOK μ₀ b)
    (h : ℤ) (hh : h ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (hsmall : N < (pcB μ₀ (padicValNat 3 b) (Real.logb 3 (b / 3 ^ padicValNat 3 b : ℕ))
      (Real.logb 3 |(h : ℝ)|) + 1) ^ 2) :
    ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 16 ≤
      (((2 * profP μ₀ b) ^ 16 * Nat.factorial 32 * 2 ^ 34 : ℕ) : ℝ) * |(h : ℝ)| := by
  set H := Real.logb 3 |(h : ℝ)|
  have hhR : (1 : ℝ) ≤ |(h : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hh
  have hH : 0 ≤ H := Real.logb_nonneg (by norm_num) hhR
  have hB := pcB_le hμ hb h3 hP H hH
  set P := profP μ₀ b
  set H' := ⌈H⌉₊
  set Y := P * (H' + 1) ^ 2
  have hNY : N < 2 ^ (2 * Y) := by
    calc N < _ := hsmall
      _ ≤ (2 ^ Y) ^ 2 := Nat.pow_le_pow_left hB 2
      _ = 2 ^ (2 * Y) := by rw [← pow_mul, mul_comm]
  have hl : Nat.log 2 N + 1 ≤ 2 * Y := Nat.log_lt_of_lt_pow (by omega) hNY
  have hnat : (Nat.log 2 N + 1) ^ 16 ≤ (2 * P) ^ 16 * (H' + 1) ^ 32 := by
    calc (Nat.log 2 N + 1) ^ 16 ≤ (2 * Y) ^ 16 := Nat.pow_le_pow_left hl 16
      _ = _ := by
        rw [show 2 * Y = 2 * P * (H' + 1) ^ 2 by simp only [Y]; rw [mul_assoc], mul_pow,
          ← pow_mul]
  have hreal : ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 16 ≤ ((2 * P : ℕ) : ℝ) ^ 16 * ((H' + 1 : ℕ) : ℝ) ^ 32 := by
    exact_mod_cast hnat
  have hy := pow_le_fact_two_rpow 32 (Nat.cast_nonneg (α := ℝ) (H' + 1))
  have hH'H : (H' : ℝ) < H + 1 := Nat.ceil_lt_add_one hH
  have h2 : (2 : ℝ) ^ (((H' + 1 : ℕ) : ℝ)) ≤ 4 * |(h : ℝ)| := by
    calc (2 : ℝ) ^ (((H' + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (H + 2) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num); push_cast; linarith
      _ = 4 * (2 : ℝ) ^ H := by rw [Real.rpow_add (by norm_num), Real.rpow_two]; ring
      _ ≤ 4 * (3 : ℝ) ^ H := by
          have := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 3) hH
          linarith
      _ = 4 * |(h : ℝ)| := by rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
  have hP0 : (0 : ℝ) ≤ ((2 * P : ℕ) : ℝ) ^ 16 := pow_nonneg (Nat.cast_nonneg _) _
  clear_value Y H' P
  rw [Nat.cast_mul, Nat.cast_mul]
  generalize Nat.factorial 32 = f at hy ⊢
  calc _ ≤ ((2 * P : ℕ) : ℝ) ^ 16 * ((H' + 1 : ℕ) : ℝ) ^ 32 := hreal
    _ ≤ ((2 * P : ℕ) : ℝ) ^ 16 * ((f : ℝ) * 2 ^ 32 * (4 * |(h : ℝ)|)) := by
        have hf : (0 : ℝ) ≤ (f : ℝ) * 2 ^ 32 :=
          mul_nonneg (Nat.cast_nonneg f) (pow_nonneg (by norm_num) 32)
        exact mul_le_mul_of_nonneg_left (hy.trans (mul_le_mul_of_nonneg_left h2 hf)) hP0
    _ = _ := by
        rw [Nat.cast_pow (2 * P), Nat.cast_pow 2 34, Nat.cast_ofNat]; ring

theorem primrec_profG (n : ℕ) : Primrec (profG n) := by
  have hp := ComputableNormal.primrec_pow
  exact (Primrec.nat_mul.comp (Primrec.const (2 * n.factorial * 2 ^ n))
    (hp.comp Primrec.id (Primrec.const n))).of_eq fun m => by simp [profG]

theorem primrec_profF (μ₀ : ℚ) : Primrec (profF μ₀) := by
  have hp := ComputableNormal.primrec_pow
  exact (Primrec.nat_mul.comp (Primrec.const (4 * μ₀.den))
    (hp.comp (Primrec.const 3) (Primrec.nat_mul.comp Primrec.id (Primrec.const μ₀.num.toNat)))).of_eq
      fun b => by simp only [profF, id]

theorem primrec_profP (μ₀ : ℚ) : Primrec (profP μ₀) := by
  have hp := ComputableNormal.primrec_pow
  unfold profP
  exact Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const _)
    (Primrec.nat_mul.comp (Primrec.const _)
      (hp.comp (Primrec.succ.comp Primrec.id) (Primrec.const 4))))
    (Primrec.nat_mul.comp (Primrec.const _) (primrec_profF μ₀))

theorem primrec_profKappa (μ₀ : ℚ) (K : ℕ) : Primrec (profKappa μ₀ K) := by
  have hp := ComputableNormal.primrec_pow
  unfold profKappa
  refine Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.const _) ?_) ?_) (Primrec.const _)) ?_
  · refine Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 2) ?_) ?_
    · exact Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 9)
        (hp.comp Primrec.id (Primrec.const 2))) (Primrec.const 42))
        (Primrec.nat_mul.comp (Primrec.const 162) (hp.comp Primrec.id (Primrec.const K)))
    · exact (primrec_profG 16).comp (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const K)
        Primrec.id) (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const (6 * K)) Primrec.id)
          (Primrec.const 7)))
  · exact Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 8)
      (Primrec.nat_mul.comp (Primrec.const _) (primrec_profF μ₀))) (Primrec.const _)
  · exact Primrec.nat_mul.comp (Primrec.nat_mul.comp
      (hp.comp (Primrec.nat_mul.comp (Primrec.const 2) (primrec_profP μ₀)) (Primrec.const 16))
      (Primrec.const _)) (Primrec.const _)

set_option maxHeartbeats 4000000 in
/-- **Uniform second moment for the profile bases.**  Proved.  Proof: the
proof of `secondMoment_le_profile` with every constant explicit (`K` from the effective
hypothesis, `g_b = log₃ t − s(μ₀−1) ≥ 3^{−s(p−q)}/(3q)` for `μ₀ = p/q`, `A, B` of
`pair_classify` bounded through `expRunStart k ≤ 4 (k+1)! ⌈μ₀+1⌉^k`), the trivial bound `N²`
for `N ≤ B_h²`, and `(log N)^{16} ≤ c(δ) N^δ`. -/
theorem secondMoment_profile_uniform (hB : Literature.BakerLogDiscrepancyEff) (μ₀ : ℚ)
    (hμ : 2 < μ₀) :
    ∃ κ : ℕ → ℕ, Primrec κ ∧ ∀ b : ℕ, 2 ≤ b → 3 ∣ b → ProfileOK μ₀ b → ∀ h : ℤ, h ≠ 0 →
      ∀ N : ℕ, 1 ≤ N →
        ∫ ω, ‖∑ k ∈ Finset.range N, DecayAeNormal.ee (h * (b : ℝ) ^ k * cantorExpReal μ₀ ω)‖ ^ 2
          ∂coins ≤ κ b * |(h : ℝ)| * N ^ 2 * profW N := by
  obtain ⟨K, hK, hD⟩ := hB
  refine ⟨profKappa μ₀ K, primrec_profKappa μ₀ K, ?_⟩
  intro b hb h3 hP h hh N hN
  have hμ1 : (1 : ℚ) < μ₀ := by linarith
  obtain ⟨hs1, hbt, ht3, ht2, -, -⟩ := profile_data hμ1 hb h3 hP
  have hcoreRaw := secondMoment_profile_core μ₀ hμ hb h3 hP h hh
  have hsmallRaw := small_case hμ hb h3 hP h hh N hN
  have hAle := pcA_le hμ hb h3 hP
  set s := padicValNat 3 b
  set t := b / 3 ^ s
  have htb : t ≤ b := Nat.div_le_self _ _
  set q := 6 * K * t + 7
  set Dt := K * t * q
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht2
  have hqR : (q : ℝ) = 6 * K * t + 7 := by simp only [q]; push_cast; ring
  have hDtR : (Dt : ℝ) = K * t * q := by simp only [Dt]; push_cast; ring
  have hq0 : (0 : ℝ) < q := by rw [hqR]; positivity
  have hKt : (1 : ℝ) ≤ K * t := by nlinarith
  set δ : ℝ := 1 / (Dt : ℝ)
  have hδ1 : δ ≤ 1 / q := by
    simp only [δ]; rw [hDtR]
    apply one_div_le_one_div_of_le hq0; nlinarith
  have hδ2 : δ ≤ 1 / ((K : ℝ) * t) - 6 / q := by
    have : 1 / ((K : ℝ) * t) - 6 / q = 7 / ((K : ℝ) * t * q) := by
      rw [hqR]; field_simp; ring
    rw [this]; simp only [δ]; rw [hDtR]
    apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hcore := hcoreRaw ((t : ℝ) ^ K) (1 / ((K : ℝ) * t)) (hD t ht2 ht3) q (by omega) δ hδ1 hδ2
    N hN
  set I := ∫ ω, ‖∑ k ∈ Finset.range N, DecayAeNormal.ee (h * (b : ℝ) ^ k * cantorExpReal μ₀ ω)‖ ^ 2
    ∂coins
  have hcI : I ≤ _ := hcore
  have hsq : I ≤ (N : ℝ) ^ 2 :=
    secondMoment_le_sq ExplicitSquare.coinMeasure (fun k ω => h * (b : ℝ) ^ k * cantorExpReal μ₀ ω) N
  set ℓ := Nat.log 2 N + 1
  have hℓ1 : (1 : ℝ) ≤ ℓ := by simp only [ℓ]; push_cast; linarith [(Nat.log 2 N).cast_nonneg (α := ℝ)]
  have hP0 : (0 : ℝ) < (ℓ : ℝ) ^ 16 := by positivity
  have hW : profW N = 1 / (ℓ : ℝ) ^ 16 := rfl
  have hhR : (1 : ℝ) ≤ |(h : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hh
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  rw [hW, show (profKappa μ₀ K b : ℝ) * |(h : ℝ)| * N ^ 2 * (1 / (ℓ : ℝ) ^ 16) =
    (profKappa μ₀ K b : ℝ) * |(h : ℝ)| * N ^ 2 / (ℓ : ℝ) ^ 16 by ring, le_div_iff₀ hP0]
  set A := pcA μ₀ s (Real.logb 3 (t : ℕ))
  set B := pcB μ₀ s (Real.logb 3 (t : ℕ)) (Real.logb 3 |(h : ℝ)|)
  set E1 : ℕ := profG 16 1 + 2 * (9 * b ^ 2 + 42 + 162 * b ^ K) * profG 16 (K * b * (6 * K * b + 7)) +
    8 * (profM μ₀ * profF μ₀ b) * profG 17 1 + 2 * profG 16 2
  set E2 : ℕ := (2 * profP μ₀ b) ^ 16 * Nat.factorial 32 * 2 ^ 34
  have hκ : profKappa μ₀ K b = E1 + E2 := rfl
  have hE1 : (0 : ℝ) ≤ E1 := Nat.cast_nonneg _
  have hE2 : (0 : ℝ) ≤ E2 := Nat.cast_nonneg _
  have hκR : (profKappa μ₀ K b : ℝ) = E1 + E2 := by rw [hκ]; push_cast; ring
  rw [hκR]
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  by_cases hsmall : N < (B + 1) ^ 2
  · have h1 := hsmallRaw hsmall
    have h2 : I * (ℓ : ℝ) ^ 16 ≤ (N : ℝ) ^ 2 * (ℓ : ℝ) ^ 16 :=
      mul_le_mul_of_nonneg_right hsq hP0.le
    have h3 : (N : ℝ) ^ 2 * (ℓ : ℝ) ^ 16 ≤ (N : ℝ) ^ 2 * (E2 * |(h : ℝ)|) :=
      mul_le_mul_of_nonneg_left h1 hN2
    have h4 : 0 ≤ (E1 : ℝ) * |(h : ℝ)| * N ^ 2 := mul_nonneg (mul_nonneg hE1 (abs_nonneg _)) hN2
    nlinarith
  · push Not at hsmall
    have hBs : (B : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      apply Real.le_sqrt_of_sq_le
      have : (B + 1) ^ 2 ≤ N := hsmall
      have : B ^ 2 ≤ N := le_trans (Nat.pow_le_pow_left (by omega) 2) this
      exact_mod_cast this
    have hW' : ((3 * (Nat.log 3 N / q) + 1 : ℕ) : ℝ) ≤ 4 * ℓ := by
      have h1 : Nat.log 3 N ≤ Nat.log 2 N := Nat.log_anti_left (by norm_num) (by norm_num)
      have h2 : Nat.log 3 N / q ≤ Nat.log 3 N := Nat.div_le_self _ _
      have : 3 * (Nat.log 3 N / q) + 1 ≤ 4 * ℓ := by simp only [ℓ]; omega
      exact_mod_cast this
    have hAR : (A : ℝ) ≤ profM μ₀ * profF μ₀ b := by exact_mod_cast hAle
    have hc : 9 * (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t + 42 + 162 * |(t : ℝ) ^ K| ≤
        9 * b ^ 2 + 42 + 162 * b ^ K := by
      have e1 : (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t ≤ (b : ℝ) ^ 2 := by
        have h1 : (3 : ℝ) ^ CantorLiouvilleAll.tb t ≤ (t : ℝ) ^ 2 := by
          exact_mod_cast (CantorLiouvilleAll.three_pow_tb_lt ht2).le
        have h2 : (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t ≤ 3 ^ CantorLiouvilleAll.tb t :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) _
        have h3 : (t : ℝ) ^ 2 ≤ (b : ℝ) ^ 2 := by gcongr
        linarith
      have e2 : |(t : ℝ) ^ K| ≤ (b : ℝ) ^ K := by
        rw [abs_of_nonneg (by positivity)]; gcongr
      linarith
    set c : ℝ := 9 * (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t + 42 + 162 * |(t : ℝ) ^ K|
    have hc0 : 0 ≤ c := by positivity
    set Z : ℝ := (N : ℝ) ^ (1 - δ)
    have hZ0 : 0 ≤ Z := by positivity
    set W' : ℕ := 3 * (Nat.log 3 N / q) + 1
    have hcI' : I ≤ N + 2 * N * (c * Z + ((A * W' + B : ℕ) : ℝ)) := hcI
    -- the four polylog estimates
    have f1 := log_pow_le_rpow 16 1 N le_rfl hN
    have hDt1 : 1 ≤ Dt := by
      simp only [Dt]
      have := Nat.mul_le_mul (Nat.mul_le_mul hK (by omega : 1 ≤ t)) (by omega : 1 ≤ q)
      simpa using this
    have f2 := log_pow_le_rpow 16 Dt N hDt1 hN
    have f3 := log_pow_le_rpow 17 1 N le_rfl hN
    have f4 := log_pow_le_rpow 16 2 N (by norm_num) hN
    simp only [Nat.cast_one, div_one, Real.rpow_one, one_pow, mul_one] at f1 f3
    rw [← profG_cast] at f2 f4
    have hG1 : (profG 16 1 : ℝ) = 2 * (Nat.factorial 16 : ℝ) * 2 ^ 16 := by
      rw [profG_cast]; norm_num
    have hG17 : (profG 17 1 : ℝ) = 2 * (Nat.factorial 17 : ℝ) * 2 ^ 17 := by
      rw [profG_cast]; norm_num
    rw [← hG1] at f1; rw [← hG17] at f3
    have hZN : Z * (N : ℝ) ^ (1 / (Dt : ℝ)) = N := by
      simp only [Z, δ]; rw [← Real.rpow_add hN0]; simp
    have hHalf : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
      rw [← Real.rpow_add hN0]; norm_num
    have hf4 : ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 16 ≤ profG 16 2 * (N : ℝ) ^ (1 / 2 : ℝ) := by
      have := f4; push_cast at this ⊢; exact this
    set P0 : ℝ := (ℓ : ℝ) ^ 16
    have T1 : (N : ℝ) * P0 ≤ profG 16 1 * N ^ 2 := by
      have := mul_le_mul_of_nonneg_left f1 hN0.le; nlinarith
    have T2 : 2 * N * (c * Z) * P0 ≤ 2 * c * profG 16 Dt * N ^ 2 := by
      have h1 : Z * P0 ≤ Z * (profG 16 Dt * (N : ℝ) ^ (1 / (Dt : ℝ))) :=
        mul_le_mul_of_nonneg_left f2 hZ0
      have h2 : Z * (profG 16 Dt * (N : ℝ) ^ (1 / (Dt : ℝ))) = profG 16 Dt * N := by
        calc Z * (profG 16 Dt * (N : ℝ) ^ (1 / (Dt : ℝ))) =
            profG 16 Dt * (Z * (N : ℝ) ^ (1 / (Dt : ℝ))) := by ring
          _ = _ := by rw [hZN]
      have h3 : 0 ≤ 2 * (N : ℝ) * c := by positivity
      have := mul_le_mul_of_nonneg_left (h1.trans h2.le) h3
      nlinarith
    have T3 : 2 * N * ((A : ℝ) * W') * P0 ≤ 8 * A * profG 17 1 * N ^ 2 := by
      have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
      have h1 : (W' : ℝ) * P0 ≤ 4 * ((ℓ : ℝ) ^ 17) := by
        have := mul_le_mul_of_nonneg_right hW' hP0.le
        simp only [P0] at this ⊢; rw [pow_succ]; nlinarith
      have h2 : (ℓ : ℝ) ^ 17 ≤ profG 17 1 * N := f3
      have h3 : 0 ≤ 2 * (N : ℝ) * A := by positivity
      have := mul_le_mul_of_nonneg_left (h1.trans (by linarith : 4 * (ℓ : ℝ) ^ 17 ≤ 4 * (profG 17 1 * N))) h3
      nlinarith
    have T4 : 2 * N * (B : ℝ) * P0 ≤ 2 * profG 16 2 * N ^ 2 := by
      have h1 : (B : ℝ) * P0 ≤ (N : ℝ) ^ (1 / 2 : ℝ) * (profG 16 2 * (N : ℝ) ^ (1 / 2 : ℝ)) :=
        mul_le_mul hBs hf4 hP0.le (by positivity)
      have h2 : (N : ℝ) ^ (1 / 2 : ℝ) * (profG 16 2 * (N : ℝ) ^ (1 / 2 : ℝ)) = profG 16 2 * N := by
        calc (N : ℝ) ^ (1 / 2 : ℝ) * (profG 16 2 * (N : ℝ) ^ (1 / 2 : ℝ)) =
            profG 16 2 * ((N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ)) := by ring
          _ = _ := by rw [hHalf]
      have := mul_le_mul_of_nonneg_left (h1.trans h2.le) (by positivity : (0 : ℝ) ≤ 2 * N)
      nlinarith
    have hsum : I * P0 ≤ (profG 16 1 + 2 * c * profG 16 Dt + 8 * A * profG 17 1 +
        2 * profG 16 2) * N ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_right hcI' hP0.le
      have e : ((N : ℝ) + 2 * N * (c * Z + ((A * W' + B : ℕ) : ℝ))) * P0 =
          N * P0 + 2 * N * (c * Z) * P0 + 2 * N * ((A : ℝ) * W') * P0 + 2 * N * (B : ℝ) * P0 := by
        push_cast; ring
      rw [e] at h1
      nlinarith
    have hDle : Dt ≤ K * b * (6 * K * b + 7) := by
      simp only [Dt, q]; gcongr
    have hG2 : (profG 16 Dt : ℝ) ≤ profG 16 (K * b * (6 * K * b + 7)) := by
      exact_mod_cast profG_mono 16 hDle
    have hE1' : (profG 16 1 + 2 * c * profG 16 Dt + 8 * A * profG 17 1 + 2 * profG 16 2 : ℝ) ≤ E1 := by
      simp only [E1]; push_cast
      have hG20 : (0 : ℝ) ≤ profG 16 Dt := Nat.cast_nonneg _
      have hG170 : (0 : ℝ) ≤ profG 17 1 := Nat.cast_nonneg _
      have : c * profG 16 Dt ≤ (9 * b ^ 2 + 42 + 162 * b ^ K) * profG 16 (K * b * (6 * K * b + 7)) :=
        mul_le_mul hc hG2 hG20 (by positivity)
      have : (A : ℝ) * profG 17 1 ≤ (profM μ₀ * profF μ₀ b) * profG 17 1 :=
        mul_le_mul_of_nonneg_right hAR hG170
      nlinarith
    have h5 := mul_le_mul_of_nonneg_right hE1' hN2
    have h6 : (E1 : ℝ) * N ^ 2 ≤ (E1 + E2) * |(h : ℝ)| * N ^ 2 := by
      have : (E1 : ℝ) ≤ (E1 + E2) * |(h : ℝ)| := by nlinarith
      exact mul_le_mul_of_nonneg_right this hN2
    linarith

/-- The schedule condition for the combined weight.  Proved (`clNs j ≥ 4^{√j}`, `profW` at
`4^{√j}` is `≤ (2√j+1)^{−16}`). -/
theorem profile_ev (μ₀ : ℚ) (hμ : 1 < μ₀) : ∀ᶠ j in atTop, 8 ≤ clNr j ∧ clNr j ≤ clNs j ∧
    (clNr j : ℝ) ^ 6 * ((eW μ₀ (clNs j) + profW (clNs j)) / 2) ≤ 1 / ((j : ℝ) + 1) ^ 4 := by
  have hpw : ∀ᶠ j in atTop, (clNr j : ℝ) ^ 6 * profW (clNs j) ≤ 1 / ((j : ℝ) + 1) ^ 4 := by
    filter_upwards [eventually_ge_atTop 64] with j hj
    set s := Nat.sqrt j
    have hs8 : 8 ≤ s := by
      have : Nat.sqrt 64 ≤ Nat.sqrt j := Nat.sqrt_le_sqrt hj
      have h64 : Nat.sqrt 64 = 8 := by
        rw [show 64 = 8 * 8 by rfl, Nat.sqrt_eq]
      omega
    have hlog : 2 * s ≤ Nat.log 2 (clNs j) := by
      apply Nat.le_log_of_pow_le (by norm_num)
      unfold clNs
      rw [pow_mul]; norm_num
      exact Nat.le_mul_of_pos_right _ (by omega)
    have hj1 : j + 1 ≤ (s + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt j; nlinarith
    have hnat : (clNr j) ^ 6 * (j + 1) ^ 4 ≤ (Nat.log 2 (clNs j) + 1) ^ 16 := by
      unfold clNr
      have h1 : (Nat.sqrt j + 8) ^ 6 ≤ (2 * s + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
      have h2 : (j + 1) ^ 4 ≤ (2 * s + 1) ^ 8 := by
        calc (j + 1) ^ 4 ≤ ((s + 1) ^ 2) ^ 4 := Nat.pow_le_pow_left hj1 4
          _ = (s + 1) ^ 8 := by ring
          _ ≤ (2 * s + 1) ^ 8 := Nat.pow_le_pow_left (by omega) 8
      have h3 : (2 * s + 1) ^ 16 ≤ (Nat.log 2 (clNs j) + 1) ^ 16 := Nat.pow_le_pow_left (by omega) 16
      have h4 : (2 * s + 1) ^ 6 * (2 * s + 1) ^ 8 ≤ (2 * s + 1) ^ 16 := by
        rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by norm_num)
      calc _ ≤ (2 * s + 1) ^ 6 * (2 * s + 1) ^ 8 := Nat.mul_le_mul h1 h2
        _ ≤ _ := h4.trans h3
    have hR : ((clNr j : ℝ)) ^ 6 * ((j : ℝ) + 1) ^ 4 ≤ ((Nat.log 2 (clNs j) + 1 : ℕ) : ℝ) ^ 16 := by
      exact_mod_cast hnat
    unfold profW
    have hp : (0 : ℝ) < ((Nat.log 2 (clNs j) + 1 : ℕ) : ℝ) ^ 16 := by positivity
    have hj0 : (0 : ℝ) < ((j : ℝ) + 1) ^ 4 := by positivity
    rw [mul_one_div, div_le_div_iff₀ hp hj0]; linarith
  filter_upwards [e_ev μ₀ hμ, hpw] with j ⟨h1, h2, h3⟩ h4
  exact ⟨h1, h2, by linarith⟩

/-- **Family derandomization with the profile bases.**  Wiring (proved from the three leaves). -/
theorem exists_computable_normal_avoid_profile (hB : Literature.BakerLogDiscrepancyEff) (μ₀ : ℚ)
    (hμ : 2 < μ₀)
    (bad' : ℕ → List Bool → Bool) (hbad' : Primrec₂ bad') (d' : ℕ → ℕ) (hd' : Primrec d')
    (hmass : ∀ j, coins.real {ω | bad' j (pre ω (d' j)) = true} ≤ 1 / ((j : ℝ) + 1) ^ 2) :
    ∃ e : ℕ → Bool, Computable e ∧
      (∀ b : ℕ, 2 ≤ b → ProfileOK μ₀ b → IsNormal b (cantorExpReal μ₀ e)) ∧
      ∃ j₁, ∀ j, j₁ ≤ j → bad' j (pre e (d' j)) = false := by
  have h1 : (1 : ℚ) < μ₀ := by linarith
  obtain ⟨κP, hκP, hP⟩ := secondMoment_profile_uniform hB μ₀ hμ
  classical
  have hS := primrecPred_profileOK μ₀ h1
  have hκ : Primrec fun b : ℕ => 2 * (16 * b ^ 6 + κP b) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_add.comp CantorLiouvilleAll.primrec_kappa hκP)
  set W : ℕ → ℝ := fun N => (eW μ₀ N + profW N) / 2
  have hW0 : ∀ N, 0 ≤ W N := fun N => by
    have := eW_nonneg μ₀ N; have := profW_nonneg N; simp only [W]; positivity
  have hWa : Antitone W := fun m n hmn => by
    have := eW_antitone μ₀ hmn; have := profW_antitone hmn; simp only [W]; linarith
  have hsm : ∀ b, 2 ≤ b → ProfileOK μ₀ b → ∀ h : ℤ, h ≠ 0 → ∀ N : ℕ, 1 ≤ N →
      ∫ ω, ‖∑ k ∈ Finset.range N, DecayAeNormal.ee (h * (b : ℝ) ^ k * cantorExpReal μ₀ ω)‖ ^ 2
        ∂coins ≤ ((2 * (16 * b ^ 6 + κP b) : ℕ) : ℝ) * |(h : ℝ)| * N ^ 2 * W N := by
    intro b hb hPb h hh N hN
    have hh0 : (0 : ℝ) ≤ |(h : ℝ)| * N ^ 2 := by positivity
    have he := eW_nonneg μ₀ N
    have hp := profW_nonneg N
    have hcast : ((2 * (16 * b ^ 6 + κP b) : ℕ) : ℝ) * |(h : ℝ)| * N ^ 2 * W N =
        ((16 * b ^ 6 : ℕ) + (κP b : ℝ)) * (|(h : ℝ)| * N ^ 2) * (eW μ₀ N + profW N) := by
      simp only [W]; push_cast; ring
    rw [hcast]
    have hk0 : (0 : ℝ) ≤ (κP b : ℝ) := by positivity
    have hb0 : (0 : ℝ) ≤ ((16 * b ^ 6 : ℕ) : ℝ) := by positivity
    by_cases h3 : 3 ∣ b
    · refine (hP b hb h3 hPb h hh N hN).trans ?_
      have : (κP b : ℝ) * |(h : ℝ)| * N ^ 2 * profW N = (κP b : ℝ) * (|(h : ℝ)| * N ^ 2) * profW N := by
        ring
      rw [this]
      have := mul_nonneg (mul_nonneg hb0 hh0) (add_nonneg he hp)
      have := mul_nonneg (mul_nonneg hk0 hh0) he
      nlinarith
    · refine (e_secondMoment_b μ₀ hb h3 h hh N hN).trans ?_
      have : ((16 * b ^ 6 : ℕ) : ℝ) * |(h : ℝ)| * N ^ 2 * eW μ₀ N =
          ((16 * b ^ 6 : ℕ) : ℝ) * (|(h : ℝ)| * N ^ 2) * eW μ₀ N := by ring
      rw [this]
      have := mul_nonneg (mul_nonneg hb0 hh0) hp
      have := mul_nonneg (mul_nonneg hk0 hh0) (add_nonneg he hp)
      nlinarith
  obtain ⟨e, hce, hn, j₁, hj⟩ := CantorLiouvilleAll.exists_computable_normal_sched_family
    (eΨ μ₀) (primrec_eΨ μ₀) (eA μ₀) (eΨ_eq μ₀) (eA_nonneg μ₀) (cantorExpReal μ₀)
    (measurable_pt (expFree μ₀)) (eA_bounds μ₀) (ProfileOK μ₀) hS
    (fun b => 2 * (16 * b ^ 6 + κP b)) hκ W hW0 hWa hsm
    clNs clNr primrec_clNs primrec_clNr tendsto_clNs clNs_ratio tendsto_clNr (profile_ev μ₀ h1) bad'
    hbad' d' hd' hmass
  exact ⟨e, hce, hn, j₁, hj⟩

/-- **The headline, given the effective Baker input.**  Wiring (proved from the leaves above,
`not_isNormal_of_not_profileOK`, and the stretch exponent tests). -/
theorem exists_computable_normalProfile_of_baker (hB : Literature.BakerLogDiscrepancyEff)
    (μ₀ : ℚ) (hμ : 2 < μ₀) :
    ∃ e : ℕ → Bool, Computable e ∧ cantorExpReal μ₀ e ∈ cantorSet ∧
      HasIrrExponent (cantorExpReal μ₀ e) μ₀ ∧
      ∀ b : ℕ, 2 ≤ b → (IsNormal b (cantorExpReal μ₀ e) ↔ ProfileOK μ₀ b) := by
  have h1 : (1 : ℚ) < μ₀ := by linarith
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1 (ev_expTest_mass_all μ₀ hμ)
  have hmass : ∀ j, coins.real {ω | (fun j p => decide (J₀ ≤ j) && expTest μ₀ j p) j
      (pre ω ((fun j => expL μ₀ j + 1) j)) = true} ≤ 1 / ((j : ℝ) + 1) ^ 2 := by
    intro j
    by_cases hj : J₀ ≤ j
    · simpa [hj] using hJ₀ j hj
    · simp only [hj, decide_false, Bool.false_and, Bool.false_eq_true, Set.ofPred_false,
        measureReal_empty]
      positivity
  have hbad : Primrec₂ fun j p => decide (J₀ ≤ j) && expTest μ₀ j p :=
    Primrec.and.comp (Primrec.nat_le.comp (Primrec.const J₀) Primrec.fst).decide
      (primrec_expTest μ₀)
  obtain ⟨e, hce, hn, j₁, hj⟩ := exists_computable_normal_avoid_profile hB μ₀ hμ _ hbad
    (fun j => expL μ₀ j + 1) (Primrec.succ.comp (primrec_expL μ₀)) hmass
  refine ⟨e, hce, mem_cantorSet μ₀ e,
    hasIrrExponent_of_avoid_two μ₀ hμ e ⟨max j₁ J₀, fun m hm => ?_⟩, fun b hb => ⟨fun hN => ?_, hn b hb⟩⟩
  · have := hj m (le_of_max_le_left hm)
    simpa [le_of_max_le_right hm] using this
  · by_contra hP
    exact not_isNormal_of_not_profileOK μ₀ h1 e hb hP hN

/-- **Sub-exponential two-logarithm bound (Gelfond-type).**  For `t ≥ 2` prime to 3, eventually
`|k log t − j log 3| ≥ exp(−k^{2/5})` for all `j`.  Much weaker than Baker–Wüstholz; Gelfond
(1935) proved bounds of this strength for two logarithms. -/
def GelfondTwoLog : Prop :=
  ∀ t : ℕ, 2 ≤ t → ¬ 3 ∣ t → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ j : ℕ,
    Real.exp (-((k : ℝ) ^ (2 / 5 : ℝ))) ≤ |(k : ℝ) * Real.log t - j * Real.log 3|

/-- **A Gelfond-strength input suffices** (lap 2's analysis, 2026-10-06).  Confidence 55%.

English proof (sketch).  The power saving of `Literature.BakerLogDiscrepancyEff` is used only
on the top window of each run shadow.  A Davenport–Erdős–LeVeque sum over the shadows
(`log a_k ≍ k log k`) converges as soon as the top-window saving is
`exp(−o(log a_k))`-uniform, which a sub-exponential two-log bound gives through Erdős–Turán with
`H = exp((log N)^{1/2})`.  The purely elementary rate (from `tᵏ ≠ 3ʲ` alone) gives only
`(log N)^{−log₃(3/2)}`, and that diverges on the shadows.  Not checked in Lean. -/
theorem ae_isNormal_of_profileOK_of_gelfond (hG : GelfondTwoLog) (μ₀ : ℚ) (hμ : 2 < μ₀) :
    ∀ᵐ ω ∂coins, ∀ b : ℕ, 2 ≤ b → ProfileOK μ₀ b → IsNormal b (cantorExpReal μ₀ ω) := by
  sorry

/-- **Headline: the exponent sets the normal profile.**  For every rational `μ₀ > 2` there is a
computable `x ∈ K` with irrationality exponent exactly `μ₀` such that, for every base `b ≥ 2`,
`x` is normal to `b` iff `b = 3ˢt` with `t > 3^{s(μ₀−1)}`.  Confidence 65% (the node above, plus
the derandomizer taking the extra bases: `exists_computable_normal_avoid`'s test family must
include the `3 ∣ b` second moments). -/
theorem exists_computable_mem_cantorSet_irrExponent_normalProfile (μ₀ : ℚ) (hμ : 2 < μ₀) :
    ∃ e : ℕ → Bool, Computable e ∧ cantorExpReal μ₀ e ∈ cantorSet ∧
      HasIrrExponent (cantorExpReal μ₀ e) μ₀ ∧
      ∀ b : ℕ, 2 ≤ b → (IsNormal b (cantorExpReal μ₀ e) ↔ ProfileOK μ₀ b) := by
  sorry

end NormalNumbers.CantorExactExponentProfile
